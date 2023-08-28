# Copyright (c) 2015 Microsoft Corporation

import os
import sys
import subprocess
import shutil
import config
import filecmp
import time
from multiprocessing import Pool


# Goodie for changing the directory
class cd:
    def __init__(self, newPath):
        self.newPath = newPath

    def __enter__(self):
        self.savedPath = os.getcwd()
        os.chdir(self.newPath)

    def __exit__(self, etype, value, traceback):
        os.chdir(self.savedPath)


class setenv:
    def __init__(self, var, val):
        self.var = var
        self.val = val
        self.old_val = None

    def __enter__(self):
        if self.var in os.environ:
            self.old_val = os.environ[self.var]
        os.environ[self.var] = self.val

    def __exit__(self, etype, value, traceback):
        if self.old_val == None:
            os.environ.pop(self.var)
        else:
            os.environ[self.var] = self.old_val


def rmf(path):
    if not os.path.exists(path):
        return  # nothing to be done
    if not os.path.isdir(path):
        os.remove(path)
    else:
        shutil.rmtree(path)


def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)


def print_dirlisting(bdir):
    print("Content of %s:" % bdir)
    for dirname, dirnames, filenames in os.walk(bdir):
        for subdirname in dirnames:
            print(os.path.join(dirname, subdirname))

        for filename in filenames:
            print(os.path.join(dirname, filename))


def testz3py(branch="master", debug=True, clang=False):
    z3dir = find_z3depot()
    bdir = get_builddir(branch, debug, clang)
    p = os.path.join(z3dir, bdir, "python")
    print("Testing docstrings in %s" % p)
    with cd(p):
        print("Testing z3test.py z3")
        if subprocess.call([config.PYTHON, "z3test.py", "z3"]) != 0:
            raise Exception("Failed to execute Z3 python regression tests 'z3test.py' at '%s'" % p)
        print("Testing z3test.py z3num")
        if subprocess.call([config.PYTHON, "z3test.py", "z3num"]) != 0:
            raise Exception("Failed to execute Z3 python regression tests 'z3num' at '%s'" % p)


def testz3ex(exe, branch="master", debug=True, clang=False):
    z3dir = find_z3depot()
    bdir = get_builddir(branch, debug, clang)
    p = os.path.join(z3dir, bdir)
    with cd(p):
        with setenv("PATH", "."):
            if is_windows() or is_osx():
                if subprocess.call([exe]) != 0:
                    raise Exception("Failed to execute '%s' at '%s'" % (exe, p))
            elif is_linux() or is_freebsd():
                with setenv("LD_LIBRARY_PATH", "."):
                    if subprocess.call([exe]) != 0:
                        raise Exception("Failed to execute '%s' at '%s'" % (exe, p))


# The duration is in seconds. It can be a float such as 0.001
def timeout(func, args=(), kwargs={}, timeout_duration=1.0, default=None):
    import threading

    class InterruptableThread(threading.Thread):
        def __init__(self):
            threading.Thread.__init__(self)
            self.result = None
            self.exception = None

        def run(self):
            try:
                self.result = func(*args, **kwargs)
            except Exception as ex:
                self.exception = ex

    it = InterruptableThread()
    it.start()
    it.join(timeout_duration)
    if it.exception is not None:
        raise it.exception
    if it.is_alive():
        return default
    return it.result


def subprocess_killer(args, stdin=None, stdout=None, stderr=None, shell=False, env=None, timeout=1.0):
    try:
        if shell:
            args = "".join(a + " " for a in args)
            if not is_windows():
                for k, v in env.items():
                    args = k + "=" + v + " " + args
        p = subprocess.Popen(args, stdin=stdin, stdout=stdout, stderr=stderr, shell=shell, env=env)
        start = time.time()
        time.sleep(0.02)
        while p.poll() == None:
            time.sleep(0.1)
            if (time.time() - start) > timeout:
                p.kill()
        return p.returncode
    except Exception as ex:
        print("Exception: %s" % ex)
        return 0


def test_benchmark(z3exe, benchmark, timeout, expected=None):
    if not os.path.exists(benchmark):
        raise Exception("Benchmark '%s' does not exist" % benchmark)
    base, ext = os.path.splitext(benchmark)
    if expected == None:
        expected = "%s.expected.out" % base
    if not os.path.exists(expected):
        raise Exception("Expected answer file '%s' does not exist" % benchmark)
    produced = "%s.produced.out" % base
    producedf = open(produced, "w")
    errcode = 0
    try:
        errcode = subprocess_killer(
            [z3exe, "model_validate=true", benchmark],
            stdout=producedf,
            stderr=producedf,
            timeout=timeout,
            env=os.environ,
        )
    except:
        raise Exception("Failed to start Z3: %s" % z3exe)
    producedf.close()
    if errcode != 0 and errcode != 1 and errcode != 105:
        raise Exception("Z3 (%s) returned unexpected error code %s for %s" % (z3exe, errcode, benchmark))
    if not filecmp.cmp(expected, produced):
        print("EXPECTED")
        print(open(expected, "r").read())
        print("======================")
        print("PRODUCED")
        print(open(produced, "r").read())
        print("======================")
        raise Exception("Z3 (%s) produced unexpected output for %s" % (z3exe, benchmark))
    return True


def run_one(z3exe, benchdir, benchmark, timeout_duration):
    try:
        bench = os.path.join(benchdir, benchmark)
        print("Testing %s" % bench)
        if (
            timeout(
                test_benchmark, args=(z3exe, bench, timeout_duration), timeout_duration=timeout_duration, default=False
            )
            == False
        ):
            raise Exception("Timeout executing benchmark %s using %s" % (bench, z3exe))
    except Exception as ex:
        print("Failed")
        print(ex)
        return True
    return False


def test_benchmarks(argv):
    z3exe = argv[1]
    benchdir = argv[2]
    ext = argv[3] if len(argv) > 3 else "smt2"
    num_threads = int(argv[4]) if len(argv) > 4 else 0
    timeout_duration = float(argv[5]) if len(argv) > 5 else 60.0

    print("Testing benchmarks at %s using %s" % (benchdir, z3exe))
    error = False
    benchmarks = filter(lambda f: f.endswith(ext), os.listdir(benchdir))

    if num_threads == 0:
        for benchmark in benchmarks:
            if run_one(z3exe, benchdir, benchmark, timeout_duration):
                error = True
    else:
        pool = Pool(num_threads)
        rs = pool.starmap(run_one, [(z3exe, benchdir, f, timeout_duration) for f in benchmarks])
        for r in rs:
            error |= r

    if error:
        raise Exception("Found errors testing benchmarks at %s using %s" % (benchdir, z3exe))


def test_benchmarks_using_latest(benchdir, branch="master", debug=True, clang=False, ext="smt2", timeout_duration=60.0):
    z3dir = find_z3depot()
    bdir = get_builddir(branch, debug, clang)
    z3exe = os.path.join(z3dir, bdir, "z3")
    test_benchmarks(z3exe, benchdir, ext, timeout_duration)


def exec_pyscript(script, timeout, env):
    shell = False if is_windows() else True
    if subprocess_killer([config.PYTHON, script], timeout=timeout, shell=shell, env=env) != 0:
        raise Exception("Script '%s' returned non-zero exit code" % script)
    return True
