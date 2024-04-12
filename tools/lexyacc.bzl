load("@rules_bison//bison:bison.bzl", "BISON_TOOLCHAIN_TYPE", "bison_toolchain")
load("@rules_flex//flex:flex.bzl", "FLEX_TOOLCHAIN_TYPE", "flex_toolchain")

def _gen_lex_impl(ctx):
    if len(ctx.files.src) != 1:
        fail("Expected exactly one source file, got %s" % ctx.files.src)
    flex = flex_toolchain(ctx)

    output = ctx.outputs.source_out
    ctx.actions.run(
        outputs = [output],
        inputs = [ctx.files.src[0]],
        arguments = ["-o", output.path, ctx.files.src[0].path],
        executable = flex.flex_tool,
        env = flex.flex_env,
    )
    return DefaultInfo(files = depset([output] + ctx.files.hdr))

def _gen_yacc_impl(ctx):
    if len(ctx.files.src) != 1:
        fail("Expected exactly one source file, got %s" % ctx.files.src)
    bison = bison_toolchain(ctx)

    outputs = [out_file for out_file in ctx.outputs.extra_outs] + [ctx.outputs.header_out, ctx.outputs.source_out]
    ctx.actions.run(
        outputs = outputs,
        inputs = [ctx.files.src[0]],
        arguments = ["-Wall", "-o", ctx.outputs.source_out.path, ctx.files.src[0].path],
        executable = bison.bison_tool,
        env = bison.bison_env,
    )
    return DefaultInfo(files = depset(outputs))

gen_lex = rule(
    implementation = _gen_lex_impl,
    attrs = {
        "src": attr.label(mandatory = True, allow_single_file = True),
        "hdr": attr.label(mandatory = False, allow_single_file = True),
        "source_out": attr.output(mandatory = True),
    },
    toolchains = [FLEX_TOOLCHAIN_TYPE],
)

gen_yacc = rule(
    implementation = _gen_yacc_impl,
    attrs = {
        "src": attr.label(mandatory = True, allow_single_file = True),
        "source_out": attr.output(mandatory = True),
        "header_out": attr.output(mandatory = True),
        "extra_outs": attr.output_list(mandatory = False, allow_empty = True),
    },
    toolchains = [BISON_TOOLCHAIN_TYPE],
)
