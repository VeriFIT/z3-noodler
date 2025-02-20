find_package(Catch2 3)
if (Catch2_FOUND)
    set(z3_test_deps smt api)
    z3_expand_dependencies(z3_test_expanded_deps ${z3_test_deps})
    set (z3_test_extra_object_files "")
    foreach (component ${z3_test_expanded_deps})
        list(APPEND z3_test_extra_object_files $<TARGET_OBJECTS:${component}>)
    endforeach()

    add_executable(test-noodler
            EXCLUDE_FROM_ALL
            "${CMAKE_CURRENT_BINARY_DIR}/gparams_register_modules.cpp"
            "${CMAKE_CURRENT_BINARY_DIR}/install_tactic.cpp"
            "${CMAKE_CURRENT_BINARY_DIR}/mem_initializer.cpp"
            ${z3_test_extra_object_files}
            main.cc
            inclusion-graph-node.cc
            theory_str_noodler.cc
            formula-preprocess.cpp
            decision-procedure.cpp
            parikh.cc
            util.cc
            formula.cpp
    )

    find_library(LIBMATA mata)
    target_link_libraries(test-noodler PRIVATE ${LIBMATA})

    z3_add_install_tactic_rule(${z3_test_deps})
    z3_add_memory_initializer_rule(${z3_test_deps})
    z3_add_gparams_register_modules_rule(${z3_test_deps})
    target_compile_definitions(test-noodler PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
    target_compile_options(test-noodler PRIVATE ${Z3_COMPONENT_CXX_FLAGS} -Wno-unused -Wno-unused-function)
    target_link_libraries(test-noodler PRIVATE ${Z3_DEPENDENT_LIBS})
    target_include_directories(test-noodler PRIVATE ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
    z3_append_linker_flag_list_to_target(test-noodler ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
    z3_add_component_dependencies_to_target(test-noodler ${z3_test_expanded_deps})
    target_link_libraries(test-noodler PRIVATE Catch2::Catch2WithMain)
endif()
