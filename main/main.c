#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>

/* --- Local implementations of symbols not exported by VMUPro OS --- */

/* 1. 64-bit unsigned division helper (__udivdi3) */
uint64_t __udivdi3(uint64_t n, uint64_t d) {
    if (d == 0) return 0;
    uint64_t q = 0, r = 0;
    for (int i = 63; i >= 0; i--) {
        r = (r << 1) | ((n >> i) & 1ULL);
        if (r >= d) {
            r -= d;
            q |= (1ULL << i);
        }
    }
    return q;
}

/* 2. Soft-float division helper (__divsf3) */
float __divsf3(float a, float b) {
    union { float f; uint32_t u; } ua = { .f = a }, ub = { .f = b };
    uint32_t sign = (ua.u ^ ub.u) & 0x80000000U;
    int32_t exp_a = (int32_t)((ua.u >> 23) & 0xFF);
    int32_t exp_b = (int32_t)((ub.u >> 23) & 0xFF);
    if (exp_a == 0) return 0.0f;
    if (exp_b == 0) return (sign ? -1.0e30f : 1.0e30f);

    uint64_t man_a = ((uint64_t)(ua.u & 0x7FFFFF) | 0x800000ULL) << 24;
    uint64_t man_b = ((uint64_t)(ub.u & 0x7FFFFF) | 0x800000ULL);
    uint32_t quot = (uint32_t)__udivdi3(man_a, man_b);
    int32_t exp_r = exp_a - exp_b + 127;

    while (quot >= 0x01000000U) { quot >>= 1; exp_r++; }
    while (quot < 0x00800000U && exp_r > 0) { quot <<= 1; exp_r--; }

    if (exp_r <= 0) return 0.0f;
    if (exp_r >= 255) exp_r = 254;

    union { uint32_t u; float f; } res;
    res.u = sign | ((uint32_t)exp_r << 23) | (quot & 0x7FFFFFU);
    return res.f;
}

/* 3. memmove replacement for minimp3 and libc */
void *memmove(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    if (d < s) {
        for (size_t i = 0; i < n; i++) d[i] = s[i];
    } else if (d > s) {
        for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1];
    }
    return dst;
}

#define MINIMP3_ONLY_MP3
#define MINIMP3_NO_SIMD
#define MINIMP3_IMPLEMENTATION
#include "minimp3.h"
#include "vmupro_sdk.h"

#define MP3_ROOT "/sdcard/mp3/"
#define IN_BUF_SIZE 16384
#define OUT_HZ 44100

enum {
    ACT_REW = 0, ACT_PLAY, ACT_FWD, ACT_BROWSE,
    ACT_VOLDN, ACT_VOLUP, ACT_LOOP, ACT_EXIT,
    ACT_COUNT
};

static const char *g_btn_labels[ACT_COUNT] = {
    "<<10s", "Play", "10s>>", "Files",
    "Vol-",  "Vol+", "Loop",  "Exit"
};

static mp3dec_t *g_dec = NULL;
static uint8_t *g_in_buf = NULL;
static int16_t *g_pcm_frame = NULL;
static int16_t *g_mono_buf = NULL;
static int16_t *g_resamp_buf = NULL;

static FILE *g_fp = NULL;
static char g_cur_path[256] = "";
static char g_cur_name[128] = "No track loaded";
static size_t g_file_size = 0;
static long g_audio_start = 0;
static long g_file_pos = 0;
static int g_in_len = 0, g_in_pos = 0;

static bool g_playing = false, g_paused = false, g_loop = false, g_running = true;
static int g_sel = ACT_PLAY;
static int g_sample_hz = 44100, g_bitrate = 128;
static uint32_t g_samples_played = 0;
static uint32_t g_phase = 0;
static int16_t g_prev_sample = 0;

static const char *base_filename(const char *path) {
    const char *slash = strrchr(path, '/');
    return slash ? slash + 1 : path;
}

static void close_track(void) {
    if (g_fp) { fclose(g_fp); g_fp = NULL; }
    vmupro_audio_clear_ring_buffer();
    g_playing = false;
    g_paused = false;
    g_in_len = 0;
    g_in_pos = 0;
    g_samples_played = 0;
    g_phase = 0;
    g_prev_sample = 0;
}

static long skip_id3v2(FILE *fp) {
    uint8_t h[10];
    fseek(fp, 0, SEEK_SET);
    if (fread(h, 1, 10, fp) != 10) { fseek(fp, 0, SEEK_SET); return 0; }
    if (h[0] == 'I' && h[1] == 'D' && h[2] == '3') {
        long sz = ((long)(h[6] & 0x7F) << 21) | ((long)(h[7] & 0x7F) << 14) |
                  ((long)(h[8] & 0x7F) << 7)  |  (long)(h[9] & 0x7F);
        long off = 10 + sz;
        fseek(fp, off, SEEK_SET);
        return off;
    }
    fseek(fp, 0, SEEK_SET);
    return 0;
}

static bool open_track(const char *path) {
    close_track();
    if (!path || !path[0]) return false;

    size_t fsz = vmupro_get_file_size(path);
    FILE *fp = fopen(path, "rb");
    if (!fp || fsz == (size_t)-1) {
        if (fp) fclose(fp);
        return false;
    }

    g_fp = fp;
    g_file_size = fsz;
    strncpy(g_cur_path, path, sizeof(g_cur_path) - 1);
    g_cur_path[sizeof(g_cur_path) - 1] = '\0';
    strncpy(g_cur_name, base_filename(path), sizeof(g_cur_name) - 1);
    g_cur_name[sizeof(g_cur_name) - 1] = '\0';

    g_audio_start = skip_id3v2(g_fp);
    g_file_pos = g_audio_start;
    mp3dec_init(g_dec);

    g_playing = true;
    g_paused = false;
    g_sel = ACT_PLAY;
    return true;
}

static void seek_seconds(int delta_sec) {
    if (!g_fp || g_file_size <= (size_t)g_audio_start) return;
    vmupro_audio_clear_ring_buffer();

    int kbps = (g_bitrate > 0) ? g_bitrate : 128;
    long delta_bytes = (long)delta_sec * (long)(kbps * 125);
    long cur_approx = g_file_pos - (g_in_len - g_in_pos);
    long target = cur_approx + delta_bytes;
    if (target < g_audio_start) target = g_audio_start;
    long max_off = (long)g_file_size - 2048L;
    if (max_off < g_audio_start) max_off = g_audio_start;
    if (target > max_off) target = max_off;

    fseek(g_fp, target, SEEK_SET);
    g_file_pos = target;
    g_in_len = 0;
    g_in_pos = 0;
    g_phase = 0;
    g_prev_sample = 0;
    mp3dec_init(g_dec);

    long byte_rate = (long)(kbps * 125);
    int32_t new_sec = (byte_rate > 0) ? (int32_t)((target - g_audio_start) / byte_rate) : 0;
    if (new_sec < 0) new_sec = 0;
    g_samples_played = (uint32_t)new_sec * OUT_HZ;
}

static bool browse_for_mp3(char *out_path, size_t max_len) {
    (void)max_len;
    if (!vmupro_folder_exists(MP3_ROOT)) vmupro_create_folder(MP3_ROOT);

    vmupro_stop_double_buffer_renderer();

    vmupro_emubrowser_settings_t st = vmupro_emubrowser_defaults();
    st.title = "Select MP3";
    st.rootPath = MP3_ROOT;
    st.filterExtension = ".mp3,.MP3";
    st.showFiles = true;
    st.showFolders = true;
    st.showIcons = true;

    out_path[0] = '\0';
    vmupro_emubrowser_error_t err = vmupro_emubrowser_init(st);
    if (err == VMUPRO_EMUBROWSER_OK) {
        vmupro_emubrowser_render_contents(out_path);
    }

    vmupro_start_double_buffer_renderer();
    return (out_path[0] != '\0');
}

static void pump_audio(void) {
    if (!g_playing || g_paused || !g_fp) return;

    uint32_t filled = 0, total = 0;
    int pct = vmupro_get_ringbuffer_fill_state(&filled, &total);
    if (pct >= 75) return;

    int loops = 0;
    while (loops < 3) {
        loops++;
        if (g_in_len - g_in_pos < 2048 && g_fp) {
            int rem = g_in_len - g_in_pos;
            if (rem > 0 && g_in_pos > 0) {
                for (int i = 0; i < rem; i++) g_in_buf[i] = g_in_buf[g_in_pos + i];
            }
            g_in_len = rem;
            g_in_pos = 0;
            size_t rd = fread(g_in_buf + g_in_len, 1, (size_t)(IN_BUF_SIZE - g_in_len), g_fp);
            g_in_len += (int)rd;
            g_file_pos += (long)rd;
        }

        if (g_in_len - g_in_pos <= 0) {
            if (g_loop) {
                fseek(g_fp, g_audio_start, SEEK_SET);
                g_file_pos = g_audio_start;
                g_in_len = 0;
                g_in_pos = 0;
                g_samples_played = 0;
                mp3dec_init(g_dec);
                continue;
            } else {
                g_playing = false;
                g_paused = false;
                return;
            }
        }

        mp3dec_frame_info_t info;
        memset(&info, 0, sizeof(info));
        int samples = mp3dec_decode_frame(g_dec, g_in_buf + g_in_pos, g_in_len - g_in_pos, g_pcm_frame, &info);
        if (info.frame_bytes <= 0) {
            g_in_pos++;
            continue;
        }
        g_in_pos += info.frame_bytes;
        if (samples <= 0) continue;

        if (info.hz > 0) g_sample_hz = info.hz;
        if (info.bitrate_kbps > 0) g_bitrate = info.bitrate_kbps;

        if (info.channels == 2) {
            for (int i = 0; i < samples; i++) {
                g_mono_buf[i] = (int16_t)(((int32_t)g_pcm_frame[2 * i] + (int32_t)g_pcm_frame[2 * i + 1]) >> 1);
            }
        } else {
            for (int i = 0; i < samples; i++) g_mono_buf[i] = g_pcm_frame[i];
        }

        if (g_sample_hz == OUT_HZ) {
            vmupro_audio_add_stream_samples(g_mono_buf, samples, VMUPRO_AUDIO_MONO, true);
            g_samples_played += (uint32_t)samples;
        } else {
            uint32_t step = (((uint32_t)g_sample_hz << 12) / (OUT_HZ >> 4));
            int out_cnt = 0;
            uint32_t limit = (uint32_t)samples << 16;
            while (g_phase < limit && out_cnt < 4096) {
                int idx = (int)(g_phase >> 16);
                int16_t s0 = (idx == 0) ? g_prev_sample : g_mono_buf[idx - 1];
                int16_t s1 = g_mono_buf[idx];
                uint32_t frac = g_phase & 0xFFFF;
                g_resamp_buf[out_cnt++] = (int16_t)(s0 + (((int32_t)(s1 - s0) * (int32_t)frac) >> 16));
                g_phase += step;
            }
            g_phase -= limit;
            g_prev_sample = g_mono_buf[samples - 1];
            if (out_cnt > 0) {
                vmupro_audio_add_stream_samples(g_resamp_buf, out_cnt, VMUPRO_AUDIO_MONO, true);
                g_samples_played += (uint32_t)out_cnt;
            }
        }

        pct = vmupro_get_ringbuffer_fill_state(&filled, &total);
        if (pct >= 75) break;
    }
}

static void render_player(void) {
    vmupro_display_clear(VMUPRO_COLOR_BLACK);
    vmupro_set_font(VMUPRO_FONT_SMALL);

    uint8_t vol = vmupro_get_global_volume();
    char hdr[32];
    vmupro_snprintf(hdr, sizeof(hdr), "MP3 Player");
    vmupro_draw_text(hdr, 8, 6, VMUPRO_COLOR_VMUGREEN, VMUPRO_COLOR_BLACK);
    vmupro_snprintf(hdr, sizeof(hdr), "Vol:%u%%", (unsigned)vol);
    vmupro_draw_text(hdr, 172, 6, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_BLACK);

    /* Track name box */
    vmupro_draw_fill_rect(6, 26, 234, 72, VMUPRO_COLOR_NAVY);
    vmupro_draw_rect(6, 26, 234, 72, VMUPRO_COLOR_BLUE);
    char line1[30], line2[30];
    size_t nlen = strlen(g_cur_name);
    size_t c1 = nlen > 28 ? 28 : nlen;
    memcpy(line1, g_cur_name, c1); line1[c1] = '\0';
    vmupro_draw_text(line1, 12, 34, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_NAVY);
    if (nlen > 28) {
        size_t rem = nlen - 28;
        size_t c2 = rem > 28 ? 28 : rem;
        memcpy(line2, g_cur_name + 28, c2); line2[c2] = '\0';
        vmupro_draw_text(line2, 12, 52, VMUPRO_COLOR_WHITE, VMUPRO_COLOR_NAVY);
    }

    /* Playback status + elapsed time */
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
    vmupro_draw_rect(10, 104, 230, 114, VMUPRO_COLOR_GREY);
    if (g_fp && g_file_size > (size_t)g_audio_start) {
        long cur = g_file_pos - (g_in_len - g_in_pos);
        if (cur < g_audio_start) cur = g_audio_start;
        uint32_t span = (uint32_t)(g_file_size - (size_t)g_audio_start);
        uint32_t pos = (uint32_t)(cur - g_audio_start);
        int fill_w = (span > 0) ? (int)(pos / (span / 218U + 1U)) : 0;
        if (fill_w > 218) fill_w = 218;
        if (fill_w > 0) vmupro_draw_fill_rect(11, 105, 11 + fill_w, 113, VMUPRO_COLOR_VMUGREEN);
    }

    /* 2x4 Selectable On-Screen Controls */
    for (int i = 0; i < ACT_COUNT; i++) {
        int col = i % 4, row = i / 4;
        int x1 = 6 + col * 58, y1 = 128 + row * 40;
        int x2 = x1 + 54, y2 = y1 + 34;
        bool sel = (i == g_sel);
        vmupro_color_t bg = sel ? VMUPRO_COLOR_BLUE : VMUPRO_COLOR_NAVY;
        vmupro_color_t br = sel ? VMUPRO_COLOR_YELLOW : VMUPRO_COLOR_GREY;
        vmupro_draw_fill_rect(x1, y1, x2, y2, bg);
        vmupro_draw_rect(x1, y1, x2, y2, br);

        const char *lbl = g_btn_labels[i];
        if (i == ACT_PLAY) lbl = (g_playing && !g_paused) ? "Pause" : "Play";
        else if (i == ACT_LOOP) lbl = g_loop ? "Loop*" : "Loop";

        int lx = x1 + (54 - (int)strlen(lbl) * 7) / 2;
        if (lx < x1 + 2) lx = x1 + 2;
        vmupro_draw_text(lbl, lx, y1 + 11, VMUPRO_COLOR_WHITE, bg);
    }

    vmupro_draw_text("D-Pad: Move  A: OK  B: Browse", 10, 220, VMUPRO_COLOR_GREY, VMUPRO_COLOR_BLACK);
    vmupro_push_double_buffer_frame();
}

static void activate_selection(void) {
    if (g_sel == ACT_PLAY) {
        if (!g_fp && g_cur_path[0]) {
            open_track(g_cur_path);
        } else if (g_playing) {
            g_paused = !g_paused;
            if (g_paused) vmupro_audio_clear_ring_buffer();
        } else if (g_cur_path[0]) {
            open_track(g_cur_path);
        }
    } else if (g_sel == ACT_REW) {
        seek_seconds(-10);
    } else if (g_sel == ACT_FWD) {
        seek_seconds(10);
    } else if (g_sel == ACT_BROWSE) {
        char picked[256];
        if (browse_for_mp3(picked, sizeof(picked))) {
            open_track(picked);
        }
    } else if (g_sel == ACT_VOLDN) {
        uint8_t v = vmupro_get_global_volume();
        vmupro_set_global_volume(v >= 10 ? (uint8_t)(v - 10) : 0);
    } else if (g_sel == ACT_VOLUP) {
        uint8_t v = vmupro_get_global_volume();
        vmupro_set_global_volume(v <= 90 ? (uint8_t)(v + 10) : 100);
    } else if (g_sel == ACT_LOOP) {
        g_loop = !g_loop;
    } else if (g_sel == ACT_EXIT) {
        g_running = false;
    }
}

void app_main(void) {
    g_dec = (mp3dec_t *)malloc(sizeof(mp3dec_t));
    g_in_buf = (uint8_t *)malloc(IN_BUF_SIZE);
    g_pcm_frame = (int16_t *)malloc(MINIMP3_MAX_SAMPLES_PER_FRAME * sizeof(int16_t));
    g_mono_buf = (int16_t *)malloc(1152 * sizeof(int16_t));
    g_resamp_buf = (int16_t *)malloc(4096 * sizeof(int16_t));

    if (!g_dec || !g_in_buf || !g_pcm_frame || !g_mono_buf || !g_resamp_buf) {
        return;
    }

    vmupro_audio_start_listen_mode();
    vmupro_start_double_buffer_renderer();

    char initial_pick[256];
    if (browse_for_mp3(initial_pick, sizeof(initial_pick))) {
        open_track(initial_pick);
    }

    while (g_running) {
        vmupro_btn_read();
        if (vmupro_btn_pressed(DPad_Left))  g_sel = (g_sel % 4 == 0) ? (g_sel + 3) : (g_sel - 1);
        if (vmupro_btn_pressed(DPad_Right)) g_sel = (g_sel % 4 == 3) ? (g_sel - 3) : (g_sel + 1);
        if (vmupro_btn_pressed(DPad_Up) || vmupro_btn_pressed(DPad_Down)) g_sel = (g_sel + 4) % ACT_COUNT;

        if (vmupro_btn_pressed(Btn_A)) activate_selection();
        if (vmupro_btn_pressed(Btn_B)) {
            char picked[256];
            if (browse_for_mp3(picked, sizeof(picked))) {
                open_track(picked);
            }
        }

        pump_audio();
        render_player();
        vmupro_sleep_ms(16);
    }

    close_track();
    vmupro_stop_double_buffer_renderer();
    vmupro_audio_exit_listen_mode();

    free(g_dec); free(g_in_buf); free(g_pcm_frame); free(g_mono_buf); free(g_resamp_buf);
}
/* END OF MAIN.C */
