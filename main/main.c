#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

/* --- Local implementations for symbols not exported by VMUPro OS --- */
uint64_t __udivdi3(uint64_t n, uint64_t d) {
    if (d == 0) return 0;
    uint64_t q = 0, r = 0;
    for (int i = 63; i >= 0; i--) {
        r = (r << 1) | ((n >> i) & 1ULL);
        if (r >= d) { r -= d; q |= (1ULL << i); }
    }
    return q;
}
float __divsf3(float a, float b) {
    union { float f; uint32_t u; } ua = { .f = a }, ub = { .f = b };
    uint32_t sign = (ua.u ^ ub.u) & 0x80000000U;
    int32_t ea = (int32_t)((ua.u >> 23) & 0xFF), eb = (int32_t)((ub.u >> 23) & 0xFF);
    if (ea == 0) return 0.0f;
    if (eb == 0) return (sign ? -1.0e30f : 1.0e30f);
    uint64_t ma = ((uint64_t)(ua.u & 0x7FFFFF) | 0x800000ULL) << 24;
    uint64_t mb = ((uint64_t)(ub.u & 0x7FFFFF) | 0x800000ULL);
    uint32_t q = (uint32_t)__udivdi3(ma, mb);
    int32_t er = ea - eb + 127;
    while (q >= 0x01000000U) { q >>= 1; er++; }
    while (q < 0x00800000U && er > 0) { q <<= 1; er--; }
    if (er <= 0) return 0.0f;
    if (er >= 255) er = 254;
    union { uint32_t u; float f; } r; r.u = sign | ((uint32_t)er << 23) | (q & 0x7FFFFFU);
    return r.f;
}
void *memmove(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst; const uint8_t *s = (const uint8_t *)src;
    if (d < s) { for (size_t i = 0; i < n; i++) d[i] = s[i]; }
    else if (d > s) { for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1]; }
    return dst;
}

#define MINIMP3_ONLY_MP3
#define MINIMP3_NO_SIMD
#define MINIMP3_IMPLEMENTATION
#include "minimp3.h"
#include "vmupro_sdk.h"

#define MP3_ROOT "/sdcard/mp3"
#define INDEX_DIR "/sdcard/apps/WiFi Transfer"
#define MAX_TRACKS 200
#define PATH_MAX_LEN 160
#define IN_BUF_SIZE 16384
#define OUT_HZ 44100

/* 2 pages x 8 grid slots */
enum {
    P0_REW = 0, P0_PLAY, P0_FWD, P0_SUB,
    P0_PREV,    P0_NONE, P0_NEXT, P0_EXIT,
    P1_VOLDN = 0, P1_VOLUP, P1_LOOP, P1_MAIN,
    P1_SLEEP,     P1_NONE,  P1_FILES, P1_EXIT
};

static mp3dec_t *g_dec = NULL;
static uint8_t *g_in_buf = NULL;
static int16_t *g_pcm_frame = NULL;
static int16_t *g_mono_buf = NULL;
static int16_t *g_resamp_buf = NULL;
static char (*g_tracks)[PATH_MAX_LEN] = NULL;
static int g_track_cnt = 0, g_track_idx = -1;

static FILE *g_fp = NULL;
static char g_cur_path[PATH_MAX_LEN] = "";
static char g_cur_name[128] = "No track loaded";
static size_t g_file_size = 0;
static long g_audio_start = 0, g_file_pos = 0;
static int g_in_len = 0, g_in_pos = 0;

static bool g_playing = false, g_paused = false, g_loop = false, g_running = true;
static bool g_sleeping = false, g_ui_dirty = true;
static int g_page = 0, g_sel = P0_PLAY, g_vol_pct = 100;
static uint8_t g_saved_bright = 80;
static int g_sample_hz = 44100, g_bitrate = 128;
static uint32_t g_samples_played = 0, g_phase = 0;
static int16_t g_prev_sample = 0;
static uint64_t g_last_ui_us = 0, g_last_mode_us = 0;

static bool ends_with_mp3(const char *s, size_t len) {
    if (len < 4) return false;
    const char *e = s + len - 4;
    return e[0] == '.' && (e[1] == 'm' || e[1] == 'M') && (e[2] == 'p' || e[2] == 'P') && e[3] == '3';
}
static int my_strncmp(const char *a, const char *b, size_t n) {
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return (unsigned char)a[i] - (unsigned char)b[i];
        if (!a[i]) return 0;
    }
    return 0;
}
static const char *base_filename(const char *path) {
    const char *slash = strrchr(path, '/');
    return slash ? slash + 1 : path;
}
static void draw_box_outline(int x1, int y1, int x2, int y2, vmupro_color_t col) {
    vmupro_draw_fill_rect(x1, y1, x2, y1 + 1, col);
    vmupro_draw_fill_rect(x1, y2 - 1, x2, y2, col);
    vmupro_draw_fill_rect(x1, y1, x1 + 1, y2, col);
    vmupro_draw_fill_rect(x2 - 1, y1, x2, y2, col);
}

static void load_playlist_from_index(void) {
    if (!g_tracks) return;
    g_track_cnt = 0;
    char ppath[128];
    for (int pg = 1; pg <= 32 && g_track_cnt < MAX_TRACKS; pg++) {
        if (pg == 1) vmupro_snprintf(ppath, sizeof(ppath), "%s/wifi_files.txt", INDEX_DIR);
        else vmupro_snprintf(ppath, sizeof(ppath), "%s/wifi_files_%d.txt", INDEX_DIR, pg);
        size_t sz = vmupro_get_file_size(ppath);
        if (sz == (size_t)-1 || sz == 0) { if (pg == 1) continue; else break; }
        if (sz > 32768) sz = 32768;
        FILE *f = fopen(ppath, "rb");
        if (!f) continue;
        char *buf = (char *)malloc(sz + 1);
        if (buf) {
            size_t n = fread(buf, 1, sz, f);
            buf[n] = '\0';
            const char *p = buf;
            while (*p && g_track_cnt < MAX_TRACKS) {
                const char *nl = p;
                while (*nl && *nl != '\n' && *nl != '\r') nl++;
                size_t ll = (size_t)(nl - p);
                if (ll > 0 && ll < PATH_MAX_LEN && my_strncmp(p, MP3_ROOT, strlen(MP3_ROOT)) == 0 && ends_with_mp3(p, ll)) {
                    memcpy(g_tracks[g_track_cnt], p, ll);
                    g_tracks[g_track_cnt][ll] = '\0';
                    g_track_cnt++;
                }
                p = *nl ? nl + 1 : nl;
                while (*p == '\n' || *p == '\r') p++;
            }
            free(buf);
        }
        fclose(f);
    }
}

static void sync_track_idx(const char *path) {
    g_track_idx = -1;
    for (int i = 0; i < g_track_cnt; i++) {
        if (strcmp(g_tracks[i], path) == 0) { g_track_idx = i; return; }
    }
}

static void close_track(void) {
    if (g_fp) { fclose(g_fp); g_fp = NULL; }
    vmupro_audio_clear_ring_buffer();
    g_playing = false; g_paused = false;
    g_in_len = 0; g_in_pos = 0;
    g_samples_played = 0; g_phase = 0; g_prev_sample = 0;
}

static long skip_id3v2(FILE *fp) {
    uint8_t h[10];
    fseek(fp, 0, SEEK_SET);
    if (fread(h, 1, 10, fp) != 10) { fseek(fp, 0, SEEK_SET); return 0; }
    if (h[0] == 'I' && h[1] == 'D' && h[2] == '3') {
        long sz = ((long)(h[6] & 0x7F) << 21) | ((long)(h[7] & 0x7F) << 14) |
                  ((long)(h[8] & 0x7F) << 7)  |  (long)(h[9] & 0x7F);
        fseek(fp, 10 + sz, SEEK_SET);
        return 10 + sz;
    }
    fseek(fp, 0, SEEK_SET);
    return 0;
}

static bool open_track(const char *path) {
    close_track();
    if (!path || !path[0]) return false;
    size_t fsz = vmupro_get_file_size(path);
    FILE *fp = fopen(path, "rb");
    if (!fp || fsz == (size_t)-1) { if (fp) fclose(fp); return false; }

    g_fp = fp; g_file_size = fsz;
    strncpy(g_cur_path, path, sizeof(g_cur_path) - 1); g_cur_path[sizeof(g_cur_path) - 1] = '\0';
    strncpy(g_cur_name, base_filename(path), sizeof(g_cur_name) - 1); g_cur_name[sizeof(g_cur_name) - 1] = '\0';
    sync_track_idx(g_cur_path);

    g_audio_start = skip_id3v2(g_fp);
    g_file_pos = g_audio_start;
    mp3dec_init(g_dec);
    g_playing = true; g_paused = false; g_ui_dirty = true;
    return true;
}

static void step_track(int dir) {
    if (g_track_cnt <= 0) load_playlist_from_index();
    if (g_track_cnt <= 0) {
        if (g_cur_path[0]) open_track(g_cur_path);
        return;
    }
    int start = (g_track_idx >= 0) ? g_track_idx : 0;
    for (int tries = 0; tries < g_track_cnt; tries++) {
        int next = (start + dir * (tries + 1)) % g_track_cnt;
        if (next < 0) next += g_track_cnt;
        if (open_track(g_tracks[next])) return;
    }
}

static void seek_seconds(int delta_sec) {
    if (!g_fp || g_file_size <= (size_t)g_audio_start) return;
    vmupro_audio_clear_ring_buffer();
    int kbps = (g_bitrate > 0) ? g_bitrate : 128;
    long target = (g_file_pos - (g_in_len - g_in_pos)) + (long)delta_sec * (long)(kbps * 125);
    if (target < g_audio_start) target = g_audio_start;
    long max_off = (long)g_file_size - 2048L;
    if (max_off < g_audio_start) max_off = g_audio_start;
    if (target > max_off) target = max_off;

    fseek(g_fp, target, SEEK_SET);
    g_file_pos = target; g_in_len = 0; g_in_pos = 0; g_phase = 0; g_prev_sample = 0;
    mp3dec_init(g_dec);
    int32_t new_sec = (int32_t)((target - g_audio_start) / (long)(kbps * 125));
    g_samples_played = (new_sec > 0) ? (uint32_t)new_sec * OUT_HZ : 0;
    g_ui_dirty = true;
}

static bool browse_for_mp3(char *out_path) {
    if (!vmupro_folder_exists(MP3_ROOT)) vmupro_create_folder(MP3_ROOT);
    vmupro_stop_double_buffer_renderer();

    vmupro_emubrowser_settings_t st = vmupro_emubrowser_defaults();
    st.title = "Select MP3";
    st.rootPath = MP3_ROOT;
    st.filterExtension = ".mp3,.MP3";
    st.showFiles = true; st.showFolders = true; st.showIcons = true;

    out_path[0] = '\0';
    if (vmupro_emubrowser_init(st) == VMUPRO_EMUBROWSER_OK) {
        vmupro_emubrowser_render_contents(out_path);
    }
    vmupro_start_double_buffer_renderer();
    g_ui_dirty = true;
    return (out_path[0] != '\0');
}

static void toggle_sleep(void) {
    if (!g_sleeping) {
        uint8_t cur_b = vmupro_get_global_brightness();
        g_saved_bright = (cur_b > 0) ? cur_b : 80;
        vmupro_display_clear(VMUPRO_COLOR_BLACK);
        vmupro_push_double_buffer_frame();
        vmupro_set_global_brightness(0);
        g_sleeping = true;
    } else {
        vmupro_set_global_brightness(g_saved_bright);
        g_sleeping = false;
        g_ui_dirty = true;
    }
}

static void apply_vol_and_send(int16_t *samples, int count) {
    if (g_vol_pct < 100) {
        for (int i = 0; i < count; i++) {
            samples[i] = (int16_t)(((int32_t)samples[i] * g_vol_pct) / 100);
        }
    }
    vmupro_audio_add_stream_samples(samples, count, VMUPRO_AUDIO_MONO, true);
}

static void pump_audio(void) {
    if (!g_playing || g_paused || !g_fp) return;

    uint32_t filled = 0, total = 0;
    int pct = vmupro_get_ringbuffer_fill_state(&filled, &total);
    uint32_t free_samp = (total > filled) ? (total - filled) : 0;

    /* Prevent USB-C ringbuffer overflow: only decode when enough free space exists */
    if ((total > 0 && free_samp < 1600) || (total == 0 && pct >= 60)) return;

    int frames_sent = 0;
    while (frames_sent < 2) {
        if (g_in_len - g_in_pos < 2048) {
            int rem = g_in_len - g_in_pos;
            if (rem > 0 && g_in_pos > 0) memmove(g_in_buf, g_in_buf + g_in_pos, (size_t)rem);
            g_in_len = rem; g_in_pos = 0;
            size_t rd = fread(g_in_buf + g_in_len, 1, (size_t)(IN_BUF_SIZE - g_in_len), g_fp);
            g_in_len += (int)rd;
            g_file_pos += (long)rd;
        }
        if (g_in_len - g_in_pos <= 0) {
            if (g_loop) {
                fseek(g_fp, g_audio_start, SEEK_SET);
                g_file_pos = g_audio_start; g_in_len = 0; g_in_pos = 0; g_samples_played = 0;
                mp3dec_init(g_dec);
                continue;
            } else if (g_track_cnt > 1) {
                step_track(1);
                return;
            } else {
                g_playing = false; g_paused = false; g_ui_dirty = true;
                return;
            }
        }

        mp3dec_frame_info_t info;
        memset(&info, 0, sizeof(info));
        int samples = mp3dec_decode_frame(g_dec, g_in_buf + g_in_pos, g_in_len - g_in_pos, g_pcm_frame, &info);
        if (info.frame_bytes <= 0) { g_in_pos++; continue; }
        g_in_pos += info.frame_bytes;
        if (samples <= 0) continue;

        if (info.hz > 0) g_sample_hz = info.hz;
        if (info.bitrate_kbps > 0) g_bitrate = info.bitrate_kbps;

        if (info.channels == 2) {
            for (int i = 0; i < samples; i++)
                g_mono_buf[i] = (int16_t)(((int32_t)g_pcm_frame[2 * i] + (int32_t)g_pcm_frame[2 * i + 1]) >> 1);
        } else {
            memcpy(g_mono_buf, g_pcm_frame, (size_t)samples * sizeof(int16_t));
        }

        if (g_sample_hz == OUT_HZ) {
            apply_vol_and_send(g_mono_buf, samples);
            g_samples_played += (uint32_t)samples;
        } else {
            uint32_t step = (((uint32_t)g_sample_hz << 12) / (OUT_HZ >> 4));
            int out_cnt = 0;
            uint32_t limit = (uint32_t)samples << 16;
            while (g_phase < limit && out_cnt < 4096) {
                int idx = (int)(g_phase >> 16);
                int16_t s0 = (idx == 0) ? g_prev_sample : g_mono_buf[idx - 1];
                int16_t s1 = g_mono_buf[idx];
                g_resamp_buf[out_cnt++] = (int16_t)(s0 + (((int32_t)(s1 - s0) * (int32_t)(g_phase & 0xFFFF)) >> 16));
                g_phase += step;
            }
            g_phase -= limit;
            g_prev_sample = g_mono_buf[samples - 1];
            if (out_cnt > 0) {
                apply_vol_and_send(g_resamp_buf, out_cnt);
                g_samples_played += (uint32_t)out_cnt;
            }
        }
        frames_sent++;
        pct = vmupro_get_ringbuffer_fill_state(&filled, &total);
        free_samp = (total > filled) ? (total - filled) : 0;
        if ((total > 0 && free_samp < 1600) || (total == 0 && pct >= 60)) break;
    }
}

static void render_player(void) {
    vmupro_display_clear(VMUPRO_COLOR_BLACK);
    vmupro_set_font(VMUPRO_FONT_SMALL);

    char hdr[32];
    if (g_track_cnt > 0 && g_track_idx >= 0) {
        vmupro_snprintf(hdr, sizeof(hdr), "Track %d/%d", g_track_idx + 1, g_track_cnt);
    } else {
        vmupro_snprintf(hdr, sizeof(hdr), "Batt: N/A");
    }
    vmupro_draw_text(hdr, 8, 6, VMUPRO_COLOR_VMUGREEN, VMUPRO_COLOR_BLACK);
    vmupro_snprintf(hdr, sizeof(hdr), "Vol:%d%%", g_vol_pct);
    vmupro_draw_text(hdr, 170, 6, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_BLACK);

    /* Track filename box */
    vmupro_draw_fill_rect(6, 26, 234, 72, VMUPRO_COLOR_NAVY);
    draw_box_outline(6, 26, 234, 72, VMUPRO_COLOR_BLUE);
    char line1[30], line2[30];
    size_t nlen = strlen(g_cur_name), c1 = nlen > 28 ? 28 : nlen;
    memcpy(line1, g_cur_name, c1); line1[c1] = '\0';
    vmupro_draw_text(line1, 12, 34, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_NAVY);
    if (nlen > 28) {
        size_t rem = nlen - 28, c2 = rem > 28 ? 28 : rem;
        memcpy(line2, g_cur_name + 28, c2); line2[c2] = '\0';
        vmupro_draw_text(line2, 12, 52, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_NAVY);
    }

    const char *st_str = !g_fp ? "NO TRACK" : (g_paused ? "PAUSED" : (g_playing ? "PLAYING" : "STOPPED"));
    vmupro_color_t st_col = g_playing && !g_paused ? VMUPRO_COLOR_VMUGREEN : (g_paused ? VMUPRO_COLOR_YELLOW : VMUPRO_COLOR_GREY);
    uint32_t sec = g_samples_played / OUT_HZ;
    char info_str[40];
    vmupro_snprintf(info_str, sizeof(info_str), "%s  %02u:%02u", st_str, (unsigned)(sec / 60), (unsigned)(sec % 60));
    vmupro_draw_text(info_str, 10, 84, st_col, VMUPRO_COLOR_BLACK);
    if (g_fp) {
        vmupro_snprintf(info_str, sizeof(info_str), "%dHz %dkbps", g_sample_hz, g_bitrate);
        vmupro_draw_text(info_str, 126, 84, VMUPRO_COLOR_GREY, VMUPRO_COLOR_BLACK);
    }

    /* Progress bar */
    draw_box_outline(10, 104, 230, 114, VMUPRO_COLOR_GREY);
    if (g_fp && g_file_size > (size_t)g_audio_start) {
        long cur = g_file_pos - (g_in_len - g_in_pos);
        if (cur < g_audio_start) cur = g_audio_start;
        uint32_t span = (uint32_t)(g_file_size - (size_t)g_audio_start);
        uint32_t pos = (uint32_t)(cur - g_audio_start);
        int fill_w = (span > 0) ? (int)(pos / (span / 218U + 1U)) : 0;
        if (fill_w > 218) fill_w = 218;
        if (fill_w > 0) vmupro_draw_fill_rect(11, 105, 11 + fill_w, 113, VMUPRO_COLOR_VMUGREEN);
    }

    /* 2x4 Selectable Controls (Page 0 or Page 1) */
    const char *p0[8] = { "<<10s", (g_playing && !g_paused) ? "Pause" : "Play", "10s>>", "Sub >", "|<Prv", "", "Nxt>|", "Exit" };
    const char *p1[8] = { "Vol-", "Vol+", "Loop", "<Main", "Sleep", "", "Files", "Exit" };
    for (int i = 0; i < 8; i++) {
        int col = i % 4, row = i / 4;
        int x1 = 6 + col * 58, y1 = 128 + row * 40, x2 = x1 + 54, y2 = y1 + 34;
        const char *lbl = (g_page == 0) ? p0[i] : p1[i];
        if (!lbl[0]) continue; /* leave slot under Play / Vol+ empty */

        bool sel = (i == g_sel);
        vmupro_color_t bg = VMUPRO_COLOR_NAVY;
        vmupro_color_t fg = VMUPRO_COLOR_WHITE;
        if (g_page == 1 && i == P1_LOOP) {
            bg = g_loop ? VMUPRO_COLOR_ORANGE : VMUPRO_COLOR_BLUE;
            if (g_loop) fg = VMUPRO_COLOR_BLACK;
        } else if (sel) {
            bg = VMUPRO_COLOR_BLUE;
        }
        vmupro_color_t br = sel ? VMUPRO_COLOR_YELLOW : VMUPRO_COLOR_GREY;
        vmupro_draw_fill_rect(x1, y1, x2, y2, bg);
        draw_box_outline(x1, y1, x2, y2, br);
        int lx = x1 + (54 - (int)strlen(lbl) * 7) / 2;
        if (lx < x1 + 2) lx = x1 + 2;
        vmupro_draw_text(lbl, lx, y1 + 11, fg, bg);
    }

    vmupro_draw_text("A:OK  B:Files  Pwr:Sleep", 12, 220, VMUPRO_COLOR_GREY, VMUPRO_COLOR_BLACK);
    vmupro_push_double_buffer_frame();
    g_ui_dirty = false;
    g_last_ui_us = vmupro_get_time_us();
}

static void move_sel(int dcol, int drow) {
    int col = g_sel % 4, row = g_sel / 4;
    if (dcol != 0) {
        col = (col + dcol + 4) % 4;
        if (row == 1 && col == 1) col = (col + dcol + 4) % 4; /* skip empty slot 5 */
    }
    if (drow != 0) {
        row = (row + 1) % 2;
        if (row == 1 && col == 1) col = 0; /* skip empty slot 5 */
    }
    g_sel = row * 4 + col;
    g_ui_dirty = true;
}

static void activate_selection(void) {
    if (g_page == 0) {
        if (g_sel == P0_PLAY) {
            if (!g_fp && g_cur_path[0]) open_track(g_cur_path);
            else if (g_playing) { g_paused = !g_paused; if (g_paused) vmupro_audio_clear_ring_buffer(); }
            else if (g_cur_path[0]) open_track(g_cur_path);
        } else if (g_sel == P0_REW) seek_seconds(-10);
        else if (g_sel == P0_FWD) seek_seconds(10);
        else if (g_sel == P0_SUB) { g_page = 1; g_sel = P1_MAIN; }
        else if (g_sel == P0_PREV) step_track(-1);
        else if (g_sel == P0_NEXT) step_track(1);
        else if (g_sel == P0_EXIT) g_running = false;
    } else {
        if (g_sel == P1_VOLDN) { g_vol_pct = (g_vol_pct >= 10) ? g_vol_pct - 10 : 0; }
        else if (g_sel == P1_VOLUP) { g_vol_pct = (g_vol_pct <= 90) ? g_vol_pct + 10 : 100; }
        else if (g_sel == P1_LOOP) { g_loop = !g_loop; }
        else if (g_sel == P1_MAIN) { g_page = 0; g_sel = P0_SUB; }
        else if (g_sel == P1_SLEEP) { toggle_sleep(); return; }
        else if (g_sel == P1_FILES) { char pk[PATH_MAX_LEN]; if (browse_for_mp3(pk)) open_track(pk); }
        else if (g_sel == P1_EXIT) { g_running = false; }
    }
    g_ui_dirty = true;
}

void app_main(void) {
    g_dec = (mp3dec_t *)malloc(sizeof(mp3dec_t));
    g_in_buf = (uint8_t *)malloc(IN_BUF_SIZE);
    g_pcm_frame = (int16_t *)malloc(MINIMP3_MAX_SAMPLES_PER_FRAME * sizeof(int16_t));
    g_mono_buf = (int16_t *)malloc(1152 * sizeof(int16_t));
    g_resamp_buf = (int16_t *)malloc(4096 * sizeof(int16_t));
    g_tracks = (char (*)[PATH_MAX_LEN])malloc((size_t)MAX_TRACKS * PATH_MAX_LEN);
    if (!g_dec || !g_in_buf || !g_pcm_frame || !g_mono_buf || !g_resamp_buf || !g_tracks) return;

    load_playlist_from_index();
    vmupro_audio_start_listen_mode();
    vmupro_start_double_buffer_renderer();

    char initial_pick[PATH_MAX_LEN];
    if (browse_for_mp3(initial_pick)) open_track(initial_pick);

    while (g_running) {
        vmupro_btn_read();

        if (vmupro_btn_pressed(Btn_Power)) {
            toggle_sleep();
        } else if (g_sleeping) {
            if (vmupro_btn_pressed(Btn_Mode)) {
                uint64_t now = vmupro_get_time_us();
                if (g_last_mode_us != 0 && ((now - g_last_mode_us) >> 10) <= 500) {
                    g_last_mode_us = 0;
                    step_track(1);
                } else {
                    g_last_mode_us = now;
                }
            }
        } else {
            if (vmupro_btn_pressed(DPad_Left))  move_sel(-1, 0);
            if (vmupro_btn_pressed(DPad_Right)) move_sel(1, 0);
            if (vmupro_btn_pressed(DPad_Up))    move_sel(0, -1);
            if (vmupro_btn_pressed(DPad_Down))  move_sel(0, 1);
            if (vmupro_btn_pressed(Btn_A))      activate_selection();
            if (vmupro_btn_pressed(Btn_B)) {
                char pk[PATH_MAX_LEN];
                if (browse_for_mp3(pk)) open_track(pk);
            }
        }

        pump_audio();

        if (!g_sleeping) {
            uint64_t now = vmupro_get_time_us();
            if (g_ui_dirty || ((now - g_last_ui_us) >> 10) >= 250) {
                render_player();
            }
        }

        vmupro_sleep_ms(8);
    }

    close_track();
    if (g_sleeping) vmupro_set_global_brightness(g_saved_bright);
    vmupro_stop_double_buffer_renderer();
    vmupro_audio_exit_listen_mode();

    free(g_dec); free(g_in_buf); free(g_pcm_frame);
    free(g_mono_buf); free(g_resamp_buf); free(g_tracks);
}
/* END OF MAIN.C */
