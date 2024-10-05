import pydlinear as pdl
import pytest
import os

FILES_DIR = tuple(map(lambda x: os.path.join("pydlinear", "test", "files", x), ["ite_02.smt2", "ite_03.smt2"]))

PARAMETERS: "list[tuple[str, pdl.LPSolver, tuple[pdl.SmtResult, ...]]]" = [
    (FILES_DIR[0], (pdl.SmtResult.DELTA_SAT, pdl.SmtResult.SAT)),
    (FILES_DIR[1], (pdl.SmtResult.UNSAT,)),
]
LP_SOLVERS: "list[pdl.LPSolver]" = [pdl.LPSolver.SOPLEX]


class TestSolver:
    @pytest.mark.parametrize("input_file,expected", PARAMETERS)
    @pytest.mark.parametrize("lp_solver", LP_SOLVERS)
    def test_constructor(self, input_file: "str", lp_solver: "pdl.LPSolver", expected: "tuple[pdl.SmtResult, ...]"):
        conf = pdl.Config()
        conf.filename = input_file
        conf.lp_solver = lp_solver
        s = pdl.SmtSolver(conf)
        res = s.Parse()
        assert res.result in expected
