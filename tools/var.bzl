"""Provides a set of variables to the template engine."""

def _provide_var_impl(ctx):
    return [platform_common.TemplateVariableInfo(ctx.attr.variables)]

provide_var = rule(
    implementation = _provide_var_impl,
    attrs = {
        "variables": attr.string_dict(),
    },
    doc = "Provides a set of variables to the template engine. Variables are passed as a dictionary of strings. The keys are the variable names, and the values are the variable values.",
)
