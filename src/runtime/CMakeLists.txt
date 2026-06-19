#==============================================================================
# morok_runtime — shared IR emitters for platform primitives.
#==============================================================================

add_library(morok_runtime STATIC
  PlatformRuntime.cpp)
add_library(morok::runtime ALIAS morok_runtime)

target_compile_features(morok_runtime PUBLIC cxx_std_23)
target_include_directories(morok_runtime PUBLIC
  "${PROJECT_SOURCE_DIR}/include")
target_link_libraries(morok_runtime
  PUBLIC morok::llvm
  PRIVATE morok::warnings morok::no_eh_rtti)
