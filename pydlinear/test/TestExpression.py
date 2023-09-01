import pydlinear as p
import pytest


class TestExpression:
    def test_constructor(self):
        e = p.Expression()

    def test_constructor_float(self):
        e = p.Expression(1.5)

    def test_constructor_variable(self):
        v = p.Variable("v")
        e = p.Expression(v)

    def test_evaluate(self):
        e = p.Expression()
        e.Evaluate()
