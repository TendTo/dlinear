#[=======================================================================[.rst:
FindQsoptex
-----------

Find the QSopt_ex exact linear programming solver library.

This module finds the QSopt_ex library installed via the autotools build
system of the qsopt-ex repository.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported targets, if found:

``Qsoptex::qsoptex``
  The QSopt_ex library.

Result Variables
^^^^^^^^^^^^^^^^

This will define the following variables:

``QSOPTEX_FOUND``
  True if the system has the QSopt_ex library.
``QSOPTEX_INCLUDE_DIRS``
  Include directories needed to use QSopt_ex.
``QSOPTEX_LIBRARIES``
  Libraries needed to link to QSopt_ex.
``QSOPTEX_VERSION``
  The version of QSopt_ex that was found (if determinable).

Cache Variables
^^^^^^^^^^^^^^^

The following cache variables may also be set:

``QSOPTEX_INCLUDE_DIR``
  The directory containing ``qsopt_ex/QSopt_ex.h``.
``QSOPTEX_LIBRARY``
  The path to the QSopt_ex library.

Hints
^^^^^

``QSOPTEX_ROOT``
  An environment variable or CMake variable pointing to the QSopt_ex
  installation prefix. If set, this path is searched first.

#]=======================================================================]

include(FindPackageHandleStandardArgs)

# Allow QSOPTEX_ROOT as a hint (both as CMake var and env var)
set(_qsoptex_search_paths "")
if(QSOPTEX_ROOT)
  list(APPEND _qsoptex_search_paths "${QSOPTEX_ROOT}")
endif()
if(DEFINED ENV{QSOPTEX_ROOT})
  list(APPEND _qsoptex_search_paths "$ENV{QSOPTEX_ROOT}")
endif()

# ---------------------------------------------------------------------------
# Find the header directory
# ---------------------------------------------------------------------------
# The library installs headers into <prefix>/include/qsopt_ex/.
# We look for the main umbrella header QSopt_ex.h inside that subdirectory.
find_path(QSOPTEX_INCLUDE_DIR
        NAMES qsopt_ex/QSopt_ex.h
        HINTS ${_qsoptex_search_paths}
        PATH_SUFFIXES include
)

# ---------------------------------------------------------------------------
# Find the library
# ---------------------------------------------------------------------------
find_library(QSOPTEX_LIBRARY
        NAMES qsopt_ex
        HINTS ${_qsoptex_search_paths}
        PATH_SUFFIXES lib lib64
)

# ---------------------------------------------------------------------------
# Try to determine the version from the installed header
# ---------------------------------------------------------------------------
# QSopt_ex does not embed a version macro in its public headers, but
# the libtool .la file or the configure.ac carries the version.  We try
# to read the version from the .la file that is typically installed next
# to the shared library, or from a pkg-config file if present.
set(QSOPTEX_VERSION "")

if(QSOPTEX_LIBRARY)
  # Attempt 1: check for a pkg-config file
  find_package(PkgConfig QUIET)
  if(PKG_CONFIG_FOUND)
    pkg_check_modules(_QSOPTEX_PC QUIET qsopt_ex)
    if(_QSOPTEX_PC_VERSION)
      set(QSOPTEX_VERSION "${_QSOPTEX_PC_VERSION}")
    endif()
  endif()
endif()

# ---------------------------------------------------------------------------
# Standard argument handling
# ---------------------------------------------------------------------------
find_package_handle_standard_args(Qsoptex
        REQUIRED_VARS
        QSOPTEX_LIBRARY
        QSOPTEX_INCLUDE_DIR
        VERSION_VAR
        QSOPTEX_VERSION
)

# ---------------------------------------------------------------------------
# Set output variables
# ---------------------------------------------------------------------------
if(QSOPTEX_FOUND)
  set(QSOPTEX_INCLUDE_DIRS "${QSOPTEX_INCLUDE_DIR}")
  set(QSOPTEX_LIBRARIES "${QSOPTEX_LIBRARY}")

  # -----------------------------------------------------------------
  # Create imported target Qsoptex::qsoptex
  # -----------------------------------------------------------------
  if(NOT TARGET Qsoptex::qsoptex)
    # Determine library type (shared or static)
    get_filename_component(_qsoptex_lib_ext "${QSOPTEX_LIBRARY}" EXT)
    if(_qsoptex_lib_ext STREQUAL ".a" OR _qsoptex_lib_ext STREQUAL ".lib")
      set(_qsoptex_lib_type STATIC)
    else()
      set(_qsoptex_lib_type SHARED)
    endif()

    add_library(Qsoptex::qsoptex ${_qsoptex_lib_type} IMPORTED)
    set_target_properties(Qsoptex::qsoptex PROPERTIES
            IMPORTED_LOCATION "${QSOPTEX_LIBRARY}"
            INTERFACE_INCLUDE_DIRECTORIES "${QSOPTEX_INCLUDE_DIR}"
    )

    # Link transitive dependencies via the target interface
    set(_qsoptex_interface_libs "")
    if(_qsoptex_interface_libs)
      set_target_properties(Qsoptex::qsoptex PROPERTIES
              INTERFACE_LINK_LIBRARIES "${_qsoptex_interface_libs}"
      )
    endif()

    # For shared libraries, set the SONAME property if possible
    if(_qsoptex_lib_type STREQUAL "SHARED")
      get_filename_component(_qsoptex_lib_realpath "${QSOPTEX_LIBRARY}" REALPATH)
      set_target_properties(Qsoptex::qsoptex PROPERTIES
              IMPORTED_LOCATION "${_qsoptex_lib_realpath}"
              IMPORTED_SONAME "libqsopt_ex.so.2"
      )
    endif()

    unset(_qsoptex_lib_type)
    unset(_qsoptex_lib_ext)
    unset(_qsoptex_interface_libs)
  endif()
endif()

mark_as_advanced(
        QSOPTEX_INCLUDE_DIR
        QSOPTEX_LIBRARY
)
