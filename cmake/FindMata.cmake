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

find_path(Mata_INCLUDE_DIR NAMES mata/nfa/nfa.hh)
find_library(Mata_LIBRARIES NAMES libmata.a)

set(Mata_FOUND_SYSTEM FALSE)

if(Mata_INCLUDE_DIR AND Mata_LIBRARIES)
 # set(Mata_FOUND_SYSTEM TRUE)
 set(Mata_VERSION "")
 # check_system_version("Mata")
endif()

if(NOT Mata_FOUND_SYSTEM)
 include(ExternalProject)

 message("mata not found (inside FindMata.cmake)")
  #  ExternalProject_Add(
  #   Mata
  #   ${COMMON_EP_CONFIG}
  #   BUILD_IN_SOURCE ON
  #   URL https://github.com/VeriFIT/mata/archive/refs/heads/devel.zip
  #   CONFIGURE_COMMAND make release 
  #   INSTALL_COMMAND make install
  #   COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/include/mata/
  #           <INSTALL_DIR>/include/mata/
  #   BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libmata.a
  # )

 ExternalProject_Add(
    GIT_REPOSITORY https://github.com/VeriFIT/mata.git
    GIT_TAG devel  # Specify a branch, tag, or commit hash
     CONFIGURE_COMMAND make release 
     INSTALL_COMMAND make install
     COMMAND ${CMAKE_COMMAND} -E copy <SOURCE_DIR>/include/mata/
             <INSTALL_DIR>/include/mata/
     BUILD_BYPRODUCTS <INSTALL_DIR>/lib/libmata.a
)

 set(Mata_INCLUDE_DIR "${DEPS_BASE}/include/")
 set(Mata_LIBRARIES "${DEPS_BASE}/lib/libmata.a")

endif()


