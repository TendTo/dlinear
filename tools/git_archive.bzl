"""A macro to be called in the WORKSPACE that adds an external from github using a workspace rule.
Taken from https://github.com/RobotLocomotion/drake with BSD 3-Clause License.
"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def github_archive(
        name,
        repository = None,
        commit = None,
        sha256 = None,
        build_file = None,
        local_repository_override = None,
        **kwargs):
    """A macro to be called in the WORKSPACE that adds an external from github using a workspace rule.

    The required name= is the rule name and so is used for @name//... labels when referring to this archive from BUILD files.

    The required commit= is the git hash to download.
    When the git project is also a git submodule in CMake, this should be kept in sync with the git submodule commit used there.
    This can also be a tag.

    The required sha256= is the checksum of the downloaded archive.
    When unsure, you can omit this argument (or comment it out) and then the checksum-mismatch error message message will offer a suggestion.

    The optional build_file= is the BUILD file label to use for building this external.
    When omitted, the BUILD file(s) within the archive will be used.

    The optional local_repository_override= can be used for temporary local testing;
    instead of retrieving the code from github, the code is retrieved from the local filesystem path given in the argument.

    Args:
        name: The name of the external, used for @name//... labels.
        repository: The github repository to download from.
        commit: The git commit hash to download.
        sha256: The sha256 checksum of the downloaded archive.
        build_file: The BUILD file label to use for building this external.
        local_repository_override: The local filesystem path to use instead of
            downloading from github.
        **kwargs: Additional arguments to pass to http_archive.
    """
    if repository == None:
        fail("Missing repository=")
    if commit == None:
        fail("Missing commit=")
    if sha256 == None:
        # This is mostly-required, but we fallback to a wrong-default value to
        # allow the first attempt to fail and print the correct sha256.
        sha256 = "0" * 64

    urls = [
        "https://github.com/%s/archive/%s.tar.gz" % (repository, commit),
    ]

    repository_split = repository.split("/")
    if len(repository_split) != 2:
        fail("The repository= must be formatted as 'organization/project'")
    _, project = repository_split

    # Github archives omit the "v" in version tags, for some reason.
    strip_commit = commit.removeprefix("v")
    strip_prefix = project + "-" + strip_commit

    if local_repository_override != None:
        if build_file == None:
            native.local_repository(
                name = name,
                path = local_repository_override,
            )
        else:
            native.new_local_repository(
                name = name,
                build_file = build_file,
                path = local_repository_override,
            )
        return

    http_archive(
        name = name,
        urls = urls,
        sha256 = sha256,
        build_file = build_file,
        strip_prefix = strip_prefix,
        **kwargs
    )

def gitlab_archive(
        name,
        repository = None,
        commit = None,
        sha256 = None,
        build_file = None,
        local_repository_override = None,
        domain = "com",
        **kwargs):
    """A macro to be called in the WORKSPACE that adds an external from gitlab using a workspace rule.

    The required name= is the rule name and so is used for @name//... labels when referring to this archive from BUILD files.

    The required commit= is the git hash to download.
    When the git project is also a git submodule in CMake, this should be kept in sync with the git submodule commit used there.
    This can also be a tag.

    The required sha256= is the checksum of the downloaded archive.
    When unsure, you can omit this argument (or comment it out) and then the checksum-mismatch error message message will offer a suggestion.

    The optional build_file= is the BUILD file label to use for building this external.
    When omitted, the BUILD file(s) within the archive will be used.

    The optional local_repository_override= can be used for temporary local testing;
    instead of retrieving the code from github, the code is retrieved from the local filesystem path given in the argument.

    Args:
        name: The name of the external, used for @name//... labels.
        repository: The github repository to download from.
        commit: The git commit hash to download.
        sha256: The sha256 checksum of the downloaded archive.
        build_file: The BUILD file label to use for building this external.
        local_repository_override: The local filesystem path to use instead of
            downloading from github.
        domain: The gitlab domain to use. Defaults to "com"
        **kwargs: Additional arguments to pass to http_archive.
    """
    if repository == None:
        fail("Missing repository=")
    if commit == None:
        fail("Missing commit=")
    if sha256 == None:
        # This is mostly-required, but we fallback to a wrong-default value to
        # allow the first attempt to fail and print the correct sha256.
        sha256 = "0" * 64

    repository_split = repository.split("/")
    if len(repository_split) != 2:
        fail("The repository= must be formatted as 'organization/project'")
    _, project = repository_split
    folder_name = project + "-" + commit

    urls = [
        "https://gitlab.%s/%s/-/archive/%s/%s.tar.gz" % (domain, repository, commit, folder_name),
    ]

    # Github archives omit the "v" in version tags, for some reason.

    if local_repository_override != None:
        if build_file == None:
            native.local_repository(
                name = name,
                path = local_repository_override,
            )
        else:
            native.new_local_repository(
                name = name,
                build_file = build_file,
                path = local_repository_override,
            )
        return

    http_archive(
        name = name,
        urls = urls,
        sha256 = sha256,
        build_file = build_file,
        strip_prefix = folder_name,
        **kwargs
    )
