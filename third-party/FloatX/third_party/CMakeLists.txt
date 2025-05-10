include(package_loader.cmake)

if(BUILD_TESTS)
    add_subdirectory(gtest)
endif()
