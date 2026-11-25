cmake_minimum_required(VERSION 3.16)

set(EXTRA_COMPONENT_DIRS ${CMAKE_CURRENT_LIST_DIR}/vmupro-sdk/sdk/c)

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(mp3_player)

include(elf_loader)
project_elf(mp3_player)

target_link_options(${CMAKE_PROJECT_NAME}.elf PRIVATE -Wl,--unresolved-symbols=ignore-all)