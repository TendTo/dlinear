import pydlinear as pdl


class TestExpression:
    def test_constructor(self):
        e = pdl.Expression()
        assert "0" == e.to_string()

    def test_constructor_float(self):
        e = pdl.Expression(1.5)
        assert "3/2" == e.to_string()

    def test_constructor_variable(self):
        v = pdl.Variable("v")
        e = pdl.Expression(v)
        assert "v" == e.to_string()

    def test_evaluate(self):
        e = pdl.Expression()
        assert 0 == e.Evaluate()
