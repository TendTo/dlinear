def _remove_dynamic_libraries(ctx, library, libraries_to_remove = []):
    if library not in libraries_to_remove:
        return library
    if library.static_library == None:
        return None
    return cc_common.create_library_to_link(
        static_library = library.static_library,
        dynamic_library = None,
        # Copy the rest of the fields
        alwayslink = library.alwayslink,
        interface_library = library.interface_library,
        objects = library.objects,
        pic_objects = library.pic_objects,
        pic_static_library = library.pic_static_library,
        #
        actions = ctx.actions,
    )

def _cc_import_foreign(ctx):
    if len(ctx.attr.deps) != 1:
        fail("cc_extract_lib rule must have exactly one dependency.")
    if ctx.attr.mode not in ["auto", "static", "dynamic", "header"]:
        fail("cc_extract_lib rule must have a valid mode.")

    mode = ctx.attr.mode
    static_libs_to_remove = []
    dynamic_libs_to_remove = []
    dynamic_linkings_to_remove = []
    out_files = []

    for dep in ctx.attr.deps:
        dep_cc_info = dep[CcInfo]
        files = dep[DefaultInfo].files

        # Capture the static libraries
        if not (mode == "static" or mode == "auto"):
            static_libs_to_remove += [
                s
                for s in files.to_list()
                if s.extension in ["a", "lib"]
            ]

        # Capture the dynamic libraries
        if not (mode == "dynamic" or mode == "auto"):
            dynamic_libs_to_remove += [
                d
                for d in files.to_list()
                if d.extension in ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] and not d.is_source
            ]

            dynamic_linkings_to_remove += [
                d
                for input in dep_cc_info.linking_context.linker_inputs.to_list()
                for d in input.libraries
                if d.dynamic_library != None
            ]

        out_files += [
            f
            for f in files.to_list()
            if f not in static_libs_to_remove and f not in dynamic_libs_to_remove
        ]

    in_cc_info = ctx.attr.deps[0][CcInfo]

    linker_inputs = [
        cc_common.create_linker_input(
            owner = input.owner,
            libraries = depset([_remove_dynamic_libraries(ctx, library, dynamic_linkings_to_remove) for library in input.libraries if _remove_dynamic_libraries(ctx, library, dynamic_linkings_to_remove) != None]),
            user_link_flags = input.user_link_flags,
            additional_inputs = depset(input.additional_inputs),
        )
        for input in in_cc_info.linking_context.linker_inputs.to_list()
    ]

    out_cc_info = CcInfo(
        compilation_context = in_cc_info.compilation_context,
        linking_context = cc_common.create_linking_context(
            linker_inputs = depset(linker_inputs),
        ),
    )

    return [DefaultInfo(files = depset(out_files)), out_cc_info]

cc_import_foreign = rule(
    attrs = {
        "deps": attr.label_list(providers = [CcInfo], allow_empty = False, mandatory = True),
        "mode": attr.string(mandatory = False, default = "auto", values = ["auto", "static", "dynamic", "header"]),
    },
    implementation = _cc_import_foreign,
)
