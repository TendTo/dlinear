import subprocess
import time
import os
import filecmp


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


def subprocess_killer(
    args, stdin=None, stdout=None, stderr=None, shell=False, env: "os._Environ | None" = None, timeout=1.0
):
    try:
        if shell:
            args = "".join(a + " " for a in args)
            if env is not None:
                for k, v in env.items():
                    args = k + "=" + v + " " + args
        p = subprocess.Popen(args, stdin=stdin, stdout=stdout, stderr=stderr, shell=shell, env=env)
        start = time.time()
        time.sleep(0.02)
        while p.poll() is None:
            time.sleep(0.1)
            if (time.time() - start) > timeout:
                p.kill()
        return p.returncode
    except Exception as ex:
        print("Exception: {}".format(ex))
        return 0


def test_benchmarks(binary: "str", benchmarks: "list[str]", max_time: "float", expected=None):
    for benchmark in benchmarks:
        test_benchmark(binary, benchmark, max_time, expected)


def test_benchmark(binary: "str", benchmark: "str", max_time: "float", expected=None):
    if not os.path.exists(benchmark):
        raise FileNotFoundError("Benchmark '%s' does not exist" % benchmark)
    base, ext = os.path.splitext(benchmark)
    if expected is None:
        expected = "{}.expected.out".format(base)
    if not os.path.exists(expected):
        raise FileNotFoundError("Expected answer file '%s' does not exist" % benchmark)
    produced = "%s.produced.out" % base
    producedf = open(produced, "w")
    errcode = 0
    try:
        errcode = subprocess_killer(
            [binary, "model_validate=true", benchmark],
            stdout=producedf,
            stderr=producedf,
            timeout=max_time,
            env=os.environ,
        )
    except:
        raise RuntimeError("Failed to start Z3: %s" % binary)
    producedf.close()
    if errcode != 0 and errcode != 1 and errcode != 105:
        raise RuntimeError("Z3 (%s) returned unexpected error code %s for %s" % (binary, errcode, benchmark))
    if not filecmp.cmp(expected, produced):
        print("EXPECTED")
        print(open(expected, "r").read())
        print("======================")
        print("PRODUCED")
        print(open(produced, "r").read())
        print("======================")
        raise RuntimeError("Z3 (%s) produced unexpected output for %s" % (binary, benchmark))
    return True
