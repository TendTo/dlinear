# Notes

## Parts skipped (may need to check later)

- Transformation from CNF to 3-CNF
- Extensional constraints in CNF
- Intensional constraints in CNF
- Final part of section 2

## Things done

The first step required to refactor the project was understanding its structure and its dependencies.
Bazel provides a very useful tool to visualize the dependencies between the different targets of a project.
The result is definitely overwhelming, but it allowed me to understand the structure of the project and the dependencies between the different targets.
One of the reasons why such complexity has been introduced is the legacy of the project, with all the components carried over from dReal.
Most of them are not used anymore, but they are still present in the codebase.

## Building dependecies

Building and linking dependencies in a \texttt{c++} project can be a daunting task.
Although Bazel provides a very powerful tool to manage dependencies, it is not always easy to use, expecially when the dependencies are not managed by Bazel itself but by other tools.
This is a very common scenario.
For this reason, there exists a set of rules called \textit{ForeignCc} \footnote{\url{https://github.com/bazelbuild/rules_foreign_cc}} meant to easy the process and automate it as much as possible.
They support the most common tools, such as CMake, make and the autotools, such as autoconf and autoreconf.
Since each project is different, a long and tedious process of trial and error is required to make the rules work with all the configurations.
The results of this process are the \texttt{soplex.BUILD.bazel} and \texttt{qsoptex.BUILD.bazel} files in the \texttt{third\_party} directory.

### Soplex

Soplex is a \texttt{c++} library for solving linear programs.


### PIMPL idiom

Pointer to implementation" or "pImpl" is a C++ programming technique that removes implementation details of a class from its object representation by placing them in a separate class, accessed through an opaque pointer. This way the client code is unaware of the class's implementation details. Most importantly, it does not have to be recompiled when 