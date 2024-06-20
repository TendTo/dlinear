load("@depend_on_what_you_use//:defs.bzl", "dwyu_aspect_factory")

# TODO: remove STD headers from `ignored_includes` once the dwyu is updated
dwyu = dwyu_aspect_factory(use_implementation_deps = True, recursive = True, skip_external_targets = True, ignored_includes = Label("//tools:ignore_includes.json"))
