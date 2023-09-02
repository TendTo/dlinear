import os
import pydlinear as p
import pytest

SMT2_DIR = os.path.join(os.path.dirname(__file__), "smt2")


@pytest.fixture(scope="module", autouse=True)
def init() -> "p.Config":
    p.init_solver(p.QSOPTEX)
    yield
    p.de_init_solver(p.QSOPTEX)


@pytest.fixture(scope="function")
def config() -> "p.Config":
    return p.Config()


class TestSmt2Driver:
    def test_constructor(self, config: "p.Config"):
        d = p.Smt2Driver(config)

    def test_parse_file(self, config: "p.Config"):
        for file in os.listdir(SMT2_DIR):
            file_path = os.path.join(SMT2_DIR, file)
            d = p.Smt2Driver(config)
            assert d.parse_file(file_path)

    def test_parse_string(self, config: "p.Config"):
        for file in os.listdir(SMT2_DIR):
            file_path = os.path.join(SMT2_DIR, file)
            with open(file_path, "r") as f:
                content = f.read()
            d = p.Smt2Driver(config)
            assert d.parse_string(content, file_path)
