import pydlinear as pdl


class TestVariable:
    def test_variable_constructor(self):
        a = pdl.Variable("a")
        assert a.get_id() == 1
        assert a.get_type() == pdl.VariableType.Real
        assert str(a) == "a"

    def test_variable_constructor_with_type(self):
        a = pdl.Variable("a", pdl.VariableType.Int)
        assert a.get_type() == pdl.VariableType.Int

        b = pdl.Variable("b", pdl.VariableType.Binary)
        assert b.get_type() == pdl.VariableType.Binary

        c = pdl.Variable("c", pdl.VariableType.Bool)
        assert c.get_type() == pdl.VariableType.Bool

        d = pdl.Variable("d", pdl.VariableType.Real)
        assert d.get_type() == pdl.VariableType.Real
