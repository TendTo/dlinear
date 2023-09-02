import pydlinear as p
import pytest


class TestVariable:
    def test_variable_constructor(self):
        a = p.Variable("a")
        assert a.get_id() == 1
        assert a.get_type() == p.VariableType.Real

    def test_variable_constructor_with_type(self):
        a = p.Variable("a", p.VariableType.Int)
        assert a.get_type() == p.VariableType.Int

        b = p.Variable("b", p.VariableType.Binary)
        assert b.get_type() == p.VariableType.Binary

        c = p.Variable("c", p.VariableType.Bool)
        assert c.get_type() == p.VariableType.Bool

        d = p.Variable("d", p.VariableType.Real)
        assert d.get_type() == p.VariableType.Real
