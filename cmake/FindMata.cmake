###############################################################################
# Top contributors (to current version):
#   Luís Felipe Ramos Ferreira
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Mata
# Mata_FOUND - found Mata lib
# Mata_INCLUDE_DIR - the Mata include directory
##

include(deps-helper)

find_path(Mata_INCLUDE_DIR NAMES mata/kissat.h)
find_library(Mata_LIBRARIES NAMES kissat)

set(Mata_FOUND_SYSTEM FALSE)
if(Mata_INCLUDE_DIR AND Mata_LIBRARIES)
  set(Mata_FOUND_SYSTEM TRUE)
  set(Mata_VERSION "")
  check_system_version("Mata")
endif()

if(NOT Mata_FOUND_SYSTEM)
  check_ep_downloaded("Mata-EP")
  if(NOT Mata-EP_DOWNLOADED)
    check_auto_download("Mata" "--no-kissat")
  endif()

  include(ExternalProject)

  fail_if_include_missing("sys/resource.h" "Mata")

  set(Mata_VERSION "sc2021")
  set(Mata_CHECKSUM "ad1945cc6980cc6d8b7049cf0a298f9f806ac3c9ca1ccb51f1bc533253d285cc")

  ExternalProject_Add(
    Mata-EP
    ${COMMON_EP_CONFIG}
    BUILD_IN_SOURCE ON
    URL https://github.com/arminbiere/kissat/archive/${Mata_VERSION}.tar.gz
    URL_HASH SHA256=${Mata_CHECKSUM}
    CONFIGURE_COMMAND <SOURCE_DIR>/configure -fPIC --quiet
                      CC=${CMAKE_C_COMPILER}
    INSTALL_COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/build/libkissat.a
                    <INSTALL_DIR>/lib/libkissat.a
    COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/src/kissat.h
            <INSTALL_DIR>/include/kissat/kissat.h
    BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libkissat.a
  )

  set(Mata_INCLUDE_DIR "${DEPS_BASE}/include/")
  set(Mata_LIBRARIES "${DEPS_BASE}/lib/libkissat.a")
endif()

set(Mata_FOUND TRUE)

add_library(Mata STATIC IMPORTED GLOBAL)
set_target_properties(Mata PROPERTIES IMPORTED_LOCATION "${Mata_LIBRARIES}")
set_target_properties(
  Mata PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${Mata_INCLUDE_DIR}"
)

mark_as_advanced(Mata_FOUND)
mark_as_advanced(Mata_FOUND_SYSTEM)
mark_as_advanced(Mata_INCLUDE_DIR)
mark_as_advanced(Mata_LIBRARIES)

if(Mata_FOUND_SYSTEM)
  message(STATUS "Found Mata ${Mata_VERSION}: ${Mata_LIBRARIES}")
else()
  message(STATUS "Building Mata ${Mata_VERSION}: ${Mata_LIBRARIES}")
  add_dependencies(Mata Mata-EP)
  # Install static library only if it is a static build.
  if(NOT BUILD_SHARED_LIBS)
    install(FILES ${Mata_LIBRARIES} TYPE ${LIB_BUILD_TYPE})
  endif()
endif()

