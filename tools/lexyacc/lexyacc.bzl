_toolchain_type = "toolchain_type"
_toolchain_name = "lexyacc"

LexYaccInfo = provider(
    doc = "Paths to lex and yacc binaries.",
    fields = ["lex", "yacc"],
)

def _lexyacc_toolchain_impl(ctx):
    return [
        platform_common.ToolchainInfo(
            lex_yacc_info = LexYaccInfo(
                lex = ctx.attr._lex,
                yacc = ctx.attr._yacc,
            ),
        ),
    ]

lexyacc_toolchain = rule(
    implementation = _lexyacc_toolchain_impl,
    attrs = {
        "_lex": attr.string(default = "flex"),
        "_yacc": attr.string(default = "bison"),
    },
    provides = [platform_common.ToolchainInfo],
)

def setup_lexyacc_toolchain(os):
    """Macro to set up the toolchains for the different platforms

    Args:
        os: The OS to set up the toolchain for.
    """
    if os != "linux":
        fail("Unknown OS: %s. Only linux is supported" % os)

    native.toolchain_type(name = _toolchain_type)
    toolchain_name = "%s_toolchain_%s" % (_toolchain_name, os)
    native_toolchain_name = "%s_%s_toolchain" % (_toolchain_name, os)
    compatibility = [
        "@platforms//os:%s" % os,
        "@platforms//cpu:x86_64",
    ]

    lexyacc_toolchain(
        name = toolchain_name,
        visibility = ["//visibility:public"],
    )

    native.toolchain(
        name = native_toolchain_name,
        toolchain = ":%s" % toolchain_name,
        toolchain_type = ":%s" % _toolchain_type,
        exec_compatible_with = compatibility,
        target_compatible_with = compatibility,
    )

def register_toolchain(os):
    """Registers the toolchain.

    Args:
        os: The OS to register the toolchain for.
    """
    native.register_toolchains("//tools/%s:%s_%s_toolchain" % (_toolchain_name, _toolchain_name, os))

def _gen_lex_impl(ctx):
    if len(ctx.files.src) != 1:
        fail("Expected exactly one source file, got %s" % ctx.files.src)
    _lex_yacc_info = ctx.toolchains["//tools/%s:%s" % (_toolchain_name, _toolchain_type)].lex_yacc_info

    output = ctx.outputs.source_out
    ctx.actions.run(
        outputs = [output],
        inputs = [ctx.files.src[0]],
        arguments = ["-o", output.path, ctx.files.src[0].path],
        executable = _lex_yacc_info.lex,
    )
    return DefaultInfo(files = depset([output]))

def _gen_yacc_impl(ctx):
    if len(ctx.files.src) != 1:
        fail("Expected exactly one source file, got %s" % ctx.files.src)
    _lex_yacc_info = ctx.toolchains["//tools/%s:%s" % (_toolchain_name, _toolchain_type)].lex_yacc_info

    outputs = [out_file for out_file in ctx.outputs.extra_outs] + [ctx.outputs.header_out, ctx.outputs.source_out]
    print("outputs: %s" % outputs)
    ctx.actions.run(
        outputs = outputs,
        inputs = [ctx.files.src[0]],
        arguments = ["-o", ctx.outputs.source_out.path, ctx.files.src[0].path],
        executable = _lex_yacc_info.yacc,
    )
    return DefaultInfo(files = depset(outputs))

gen_lex = rule(
    implementation = _gen_lex_impl,
    attrs = {
        "src": attr.label(mandatory = True, allow_single_file = True),
        "source_out": attr.output(mandatory = True),
    },
    toolchains = ["//tools/%s:%s" % (_toolchain_name, _toolchain_type)],
)

gen_yacc = rule(
    implementation = _gen_yacc_impl,
    attrs = {
        "src": attr.label(mandatory = True, allow_single_file = True),
        "source_out": attr.output(mandatory = True),
        "header_out": attr.output(mandatory = True),
        "extra_outs": attr.output_list(mandatory = False, allow_empty = True),
    },
    toolchains = ["//tools/%s:%s" % (_toolchain_name, _toolchain_type)],
)
