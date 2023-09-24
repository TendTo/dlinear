import os
import pydlinear as pdl
import pytest

FILES_DIR = os.path.join(os.path.dirname(__file__), "files")

PARAMETERS: "list[tuple[str, pdl.LPSolver, int, str]]" = [
    ("ite_02.smt2", pdl.LPSolver.QSOPTEX, 1, "delta-sat with delta = 5e-324 ( > 0)"),
    (
        "ite_02.smt2",
        pdl.LPSolver.SOPLEX,
        1,
        "delta-sat with delta = 0.0009999999999999998 ( > 2305843009213693/2305843009213693952)",
    ),
    ("ite_03.smt2", pdl.LPSolver.QSOPTEX, 1, "unsat"),
    ("ite_03.smt2", pdl.LPSolver.SOPLEX, 1, "unsat"),
]


@pytest.fixture(scope="function")
def config() -> "pdl.Config":
    return pdl.Config()


class TestSolver:
    @pytest.mark.parametrize("input_file,lp_solver,phase,expected", PARAMETERS)
    def test_constructor(self, input_file: "str", lp_solver: "pdl.LPSolver", phase: "int", expected: "str"):
        conf = pdl.Config()
        conf.filename = os.path.join(FILES_DIR, input_file)
        conf.lp_solver = lp_solver
        conf.simplex_sat_phase = phase

        s = pdl.Solver(conf)
        res = str(s.CheckSat())
        assert res.strip() == expected.strip()
