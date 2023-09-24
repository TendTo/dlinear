import pydlinear as pdl
import pytest


@pytest.fixture(scope="function", autouse=True)
def solver() -> "pdl.Solver":
    with pdl.Solver() as s:
        yield s


class TestExpression:
    def test_constructor(self):
        e = pdl.Expression()

    def test_constructor_float(self):
        e = pdl.Expression(1.5)

    def test_constructor_variable(self):
        v = pdl.Variable("v")
        e = pdl.Expression(v)

    def test_evaluate(self):
        e = pdl.Expression()
        e.Evaluate()
