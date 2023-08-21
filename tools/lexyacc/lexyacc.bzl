_toolchain_type = "lexyacc_toolchain_type"

LexYaccInfo = provider(
    doc = "Paths to lex and yacc binaries.",
    fields = ["lex"],  # TODO: add back yacc
)

def setup_lexyacc_toolchain(os):
    """
    Macro to set up the toolchains for the different platforms
    """
    native.toolchain_type(name = _toolchain_type)
    toolchain_name = "lexyacc_toolchain_%s" % os
    native_toolchain_name = "lexyacc_%s_toolchain" % os
    compatibility = ["@bazel_tools//platforms:%s" % os]

    lexyacc_toolchain(
        name = toolchain_name,
        visibility = ["//visibility:public"],
    )

    native.toolchain(
        name = native_toolchain_name,
        toolchain = ":%s" % toolchain_name,
        toolchain_type = ":%s" % _toolchain_type,
        target_compatible_with = compatibility,
    )

def register_toolchain():
    """
    Registers the Fn toolchains.
    """
    path = "//tools/bazel_rules/fn/internal/cli:fn_cli_%s_toolchain"

    for os in os_list:
        native.register_toolchains(path % os)

def _lexyacc_toolchain_impl(ctx):
    return [
        platform_common.ToolchainInfo(
            lex_yacc_info = LexYaccInfo(
                lex = ctx.attr._lex,
                #                yacc = ctx.attr._yacc,
            ),
        ),
    ]

lexyacc_toolchain = rule(
    implementation = _lexyacc_toolchain_impl,
    attrs = {
        "_lex": attr.label(default = Label("@flex")),
        #        "_yacc": attr.label(default = Label("@bison")),
    },
    provides = [platform_common.ToolchainInfo],
)

lexyacc_toolchain(
    name = "lexyacc_toolchain_linux",
    arch_flags = ["-arch", "linux"],
)

def lexyacc_toolchain(name, lex, yacc):
    print("lexyacc_toolchain: %s %s %s" % (name, lex, yacc))
    lexyacc_toolchain(name = name)
    native.toolchain(
        name = name + "_toolchain",
        toolchain = ":" + name,
        toolchain_type = "//tools:lexyacc_toolchain_type",
    )

#gen_lex = rule(
#    implementation = _lexyacc_toolchain_impl,
#    attrs = {
#        "srcs": attr.label_list(allow_files = True),
#    },
#    toolchains = ["//bar_tools:toolchain_type"],
#)
#
#gen_yacc = rule(
#    implementation = _lexyacc_toolchain_impl,
#    attrs = {
#        "srcs": attr.label_list(allow_files = True),
#    },
#    toolchains = ["//bar_tools:toolchain_type"],
#)
