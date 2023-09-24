"""dlinear python bindings"""
from __future__ import annotations
import pydlinear._pydlinear
import typing

__all__ = [
    "AUTO",
    "Binary",
    "Bool",
    "Box",
    "Config",
    "Context",
    "Expression",
    "FALSE",
    "Format",
    "Formula",
    "Int",
    "Interval",
    "JEROS_LOW_WANG",
    "LPSolver",
    "MPS",
    "MpqArray",
    "QSOPTEX",
    "RANDOM_INITIAL_PHASE",
    "Real",
    "SMT2",
    "SOPLEX",
    "SatDefaultPhase",
    "Solver",
    "SolverOutput",
    "TRUE",
    "Variable",
    "VariableType",
    "Variables",
    "set_verbosity"
]


class Box():
    def Add(self, arg0: Variable) -> None: ...
    def MaxDiam(self) -> typing.Tuple[mpq_class, int]: ...
    def __delitem__(self, arg0: Variable) -> None: ...
    def __eq__(self, arg0: Box) -> bool: ...
    @typing.overload
    def __getitem__(self, arg0: Variable) -> Interval: ...
    @typing.overload
    def __getitem__(self, arg0: int) -> Interval: ...
    def __init__(self, arg0: typing.List[Variable]) -> None: ...
    def __len__(self) -> int: ...
    def __ne__(self, arg0: Box) -> bool: ...
    def __repr__(self) -> str: ...
    @typing.overload
    def __setitem__(self, arg0: Variable, arg1: Interval) -> None: ...
    @typing.overload
    def __setitem__(self, arg0: int, arg1: Interval) -> None: ...
    def __str__(self) -> str: ...
    @typing.overload
    def bisect(self, arg0: int) -> typing.Tuple[Box, Box]: ...
    @typing.overload
    def bisect(self, arg0: Variable) -> typing.Tuple[Box, Box]: ...
    def clear(self) -> None: ...
    def empty(self) -> bool: ...
    def has_key(self, arg0: Variable) -> bool: ...
    def index(self, arg0: Variable) -> int: ...
    def items(self) -> typing.List[typing.Tuple[Variable, Interval]]: ...
    def keys(self) -> typing.List[Variable]: ...
    def set(self, arg0: Box) -> Box: ...
    def set_empty(self) -> None: ...
    def size(self) -> int: ...
    def values(self) -> typing.List[Interval]: ...
    def variable(self, arg0: int) -> Variable: ...
    __hash__: typing.ClassVar[None] = None
    pass
class Config():
    def __init__(self) -> None: ...
    def __str__(self) -> str: ...
    @staticmethod
    def from_command_line(arg0: typing.List[str]) -> Config: ...
    @property
    def continuous_output(self) -> bool:
        """
        :type: bool
        """
    @continuous_output.setter
    def continuous_output(self, arg1: bool) -> None:
        pass
    @property
    def debug_parsing(self) -> bool:
        """
        :type: bool
        """
    @debug_parsing.setter
    def debug_parsing(self, arg1: bool) -> None:
        pass
    @property
    def debug_scanning(self) -> bool:
        """
        :type: bool
        """
    @debug_scanning.setter
    def debug_scanning(self, arg1: bool) -> None:
        pass
    @property
    def filename(self) -> str:
        """
        :type: str
        """
    @filename.setter
    def filename(self, arg1: str) -> None:
        pass
    @property
    def format(self) -> Format:
        """
        :type: Format
        """
    @format.setter
    def format(self, arg1: Format) -> None:
        pass
    @property
    def lp_solver(self) -> LPSolver:
        """
        :type: LPSolver
        """
    @lp_solver.setter
    def lp_solver(self, arg1: LPSolver) -> None:
        pass
    @property
    def nlopt_ftol_abs(self) -> float:
        """
        :type: float
        """
    @nlopt_ftol_abs.setter
    def nlopt_ftol_abs(self, arg1: bool) -> None:
        pass
    @property
    def nlopt_ftol_rel(self) -> float:
        """
        :type: float
        """
    @nlopt_ftol_rel.setter
    def nlopt_ftol_rel(self, arg1: bool) -> None:
        pass
    @property
    def nlopt_maxeval(self) -> int:
        """
        :type: int
        """
    @nlopt_maxeval.setter
    def nlopt_maxeval(self, arg1: bool) -> None:
        pass
    @property
    def nlopt_maxtime(self) -> float:
        """
        :type: float
        """
    @nlopt_maxtime.setter
    def nlopt_maxtime(self, arg1: bool) -> None:
        pass
    @property
    def number_of_jobs(self) -> int:
        """
        :type: int
        """
    @number_of_jobs.setter
    def number_of_jobs(self, arg1: int) -> None:
        pass
    @property
    def precision(self) -> float:
        """
        :type: float
        """
    @precision.setter
    def precision(self, arg1: float) -> None:
        pass
    @property
    def produce_models(self) -> bool:
        """
        :type: bool
        """
    @produce_models.setter
    def produce_models(self, arg1: bool) -> None:
        pass
    @property
    def random_seed(self) -> int:
        """
        :type: int
        """
    @random_seed.setter
    def random_seed(self, arg1: int) -> None:
        pass
    @property
    def read_from_stdin(self) -> bool:
        """
        :type: bool
        """
    @read_from_stdin.setter
    def read_from_stdin(self, arg1: bool) -> None:
        pass
    @property
    def sat_default_phase(self) -> SatDefaultPhase:
        """
        :type: SatDefaultPhase
        """
    @sat_default_phase.setter
    def sat_default_phase(self, arg1: SatDefaultPhase) -> None:
        pass
    @property
    def silent(self) -> bool:
        """
        :type: bool
        """
    @silent.setter
    def silent(self, arg1: bool) -> None:
        pass
    @property
    def simplex_sat_phase(self) -> int:
        """
        :type: int
        """
    @simplex_sat_phase.setter
    def simplex_sat_phase(self, arg1: int) -> None:
        pass
    @property
    def skip_check_sat(self) -> bool:
        """
        :type: bool
        """
    @skip_check_sat.setter
    def skip_check_sat(self, arg1: bool) -> None:
        pass
    @property
    def use_local_optimization(self) -> bool:
        """
        :type: bool
        """
    @use_local_optimization.setter
    def use_local_optimization(self, arg1: bool) -> None:
        pass
    @property
    def use_polytope(self) -> bool:
        """
        :type: bool
        """
    @use_polytope.setter
    def use_polytope(self, arg1: bool) -> None:
        pass
    @property
    def use_polytope_in_forall(self) -> bool:
        """
        :type: bool
        """
    @use_polytope_in_forall.setter
    def use_polytope_in_forall(self, arg1: bool) -> None:
        pass
    @property
    def use_worklist_fixpoint(self) -> bool:
        """
        :type: bool
        """
    @use_worklist_fixpoint.setter
    def use_worklist_fixpoint(self, arg1: bool) -> None:
        pass
    @property
    def verbose_dlinear(self) -> int:
        """
        :type: int
        """
    @verbose_dlinear.setter
    def verbose_dlinear(self, arg1: int) -> None:
        pass
    @property
    def verbose_simplex(self) -> int:
        """
        :type: int
        """
    @verbose_simplex.setter
    def verbose_simplex(self, arg1: int) -> None:
        pass
    @property
    def with_timings(self) -> bool:
        """
        :type: bool
        """
    @with_timings.setter
    def with_timings(self, arg1: bool) -> None:
        pass
    pass
class Context():
    @typing.overload
    def __init__(self) -> None: ...
    @typing.overload
    def __init__(self, arg0: Config) -> None: ...
    pass
class Expression():
    def Differentiate(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def Evaluate(self) -> float: ...
    @typing.overload
    def Evaluate(self, arg0: typing.Dict[Variable, float]) -> float: ...
    def EvaluatePartial(self, arg0: typing.Dict[Variable, float]) -> Expression: ...
    def Expand(self) -> Expression: ...
    def Substitute(self, arg0: Variable, arg1: Expression) -> Expression: ...
    def __abs__(self) -> Expression: ...
    @typing.overload
    def __add__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __add__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __add__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __eq__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __eq__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __eq__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __ge__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __ge__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __ge__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __gt__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __gt__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __gt__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __iadd__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __iadd__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __iadd__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __imul__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __imul__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __imul__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __init__(self) -> None: ...
    @typing.overload
    def __init__(self, arg0: float) -> None: ...
    @typing.overload
    def __init__(self, arg0: Variable) -> None: ...
    @typing.overload
    def __isub__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __isub__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __isub__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __itruediv__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __itruediv__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __itruediv__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __le__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __le__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __le__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __lt__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __lt__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __lt__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __mul__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __mul__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __mul__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __ne__(self, arg0: Expression) -> Formula: ...
    @typing.overload
    def __ne__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __ne__(self, arg0: float) -> Formula: ...
    def __neg__(self) -> Expression: ...
    def __pow__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __radd__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __radd__(self, arg0: float) -> Expression: ...
    def __repr__(self) -> str: ...
    @typing.overload
    def __rmul__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __rmul__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __rsub__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __rsub__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __rtruediv__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __rtruediv__(self, arg0: float) -> Expression: ...
    def __str__(self) -> str: ...
    @typing.overload
    def __sub__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __sub__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __sub__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __truediv__(self, arg0: Expression) -> Expression: ...
    @typing.overload
    def __truediv__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __truediv__(self, arg0: float) -> Expression: ...
    def to_string(self) -> str: ...
    __hash__: typing.ClassVar[None] = None
    pass
class Format():
    """
    Members:

      AUTO

      SMT2

      MPS
    """
    def __eq__(self, other: object) -> bool: ...
    def __getstate__(self) -> int: ...
    def __hash__(self) -> int: ...
    def __index__(self) -> int: ...
    def __init__(self, value: int) -> None: ...
    def __int__(self) -> int: ...
    def __ne__(self, other: object) -> bool: ...
    def __repr__(self) -> str: ...
    def __setstate__(self, state: int) -> None: ...
    @property
    def name(self) -> str:
        """
        :type: str
        """
    @property
    def value(self) -> int:
        """
        :type: int
        """
    AUTO: pydlinear._pydlinear.Format # value = <Format.AUTO: 0>
    MPS: pydlinear._pydlinear.Format # value = <Format.MPS: 2>
    SMT2: pydlinear._pydlinear.Format # value = <Format.SMT2: 1>
    __members__: dict # value = {'AUTO': <Format.AUTO: 0>, 'SMT2': <Format.SMT2: 1>, 'MPS': <Format.MPS: 2>}
    pass
class Formula():
    def EqualTo(self, arg0: Formula) -> bool: ...
    def Evaluate(self) -> bool: ...
    @staticmethod
    def FALSE() -> Formula: ...
    def GetFreeVariables(self) -> Variables: ...
    def Substitute(self, arg0: Variable, arg1: Expression) -> Formula: ...
    @staticmethod
    def TRUE() -> Formula: ...
    @typing.overload
    def __eq__(self, arg0: Formula) -> bool: ...
    @typing.overload
    def __eq__(self, arg0: Variable) -> Formula: ...
    def __hash__(self) -> int: ...
    def __init__(self, arg0: Variable) -> None: ...
    @typing.overload
    def __ne__(self, arg0: Formula) -> bool: ...
    @typing.overload
    def __ne__(self, arg0: Variable) -> Formula: ...
    def __nonzero__(self) -> bool: ...
    def __repr__(self) -> str: ...
    def __str__(self) -> str: ...
    def to_string(self) -> str: ...
    pass
class Interval():
    def __eq__(self, arg0: Interval) -> bool: ...
    @typing.overload
    def __init__(self) -> None: ...
    @typing.overload
    def __init__(self, arg0: float, arg1: float) -> None: ...
    @typing.overload
    def __init__(self, arg0: float) -> None: ...
    def __ne__(self, arg0: Interval) -> bool: ...
    def __repr__(self) -> str: ...
    def __str__(self) -> str: ...
    def bisect(self, arg0: mpq_class) -> typing.Tuple[Interval, Interval]: ...
    def diam(self) -> mpq_class: ...
    def is_bisectable(self) -> bool: ...
    def is_degenerated(self) -> bool: ...
    def is_empty(self) -> bool: ...
    def lb(self) -> mpq_class: ...
    def mid(self) -> mpq_class: ...
    def set_empty(self) -> None: ...
    def ub(self) -> mpq_class: ...
    __hash__: typing.ClassVar[None] = None
    pass
class LPSolver():
    """
    Members:

      QSOPTEX

      SOPLEX
    """
    def __eq__(self, other: object) -> bool: ...
    def __getstate__(self) -> int: ...
    def __hash__(self) -> int: ...
    def __index__(self) -> int: ...
    def __init__(self, value: int) -> None: ...
    def __int__(self) -> int: ...
    def __ne__(self, other: object) -> bool: ...
    def __repr__(self) -> str: ...
    def __setstate__(self, state: int) -> None: ...
    @property
    def name(self) -> str:
        """
        :type: str
        """
    @property
    def value(self) -> int:
        """
        :type: int
        """
    QSOPTEX: pydlinear._pydlinear.LPSolver # value = <LPSolver.QSOPTEX: 1>
    SOPLEX: pydlinear._pydlinear.LPSolver # value = <LPSolver.SOPLEX: 0>
    __members__: dict # value = {'QSOPTEX': <LPSolver.QSOPTEX: 1>, 'SOPLEX': <LPSolver.SOPLEX: 0>}
    pass
class MpqArray():
    def __getitem__(self, arg0: int) -> float: ...
    def __init__(self, arg0: int) -> None: ...
    def __len__(self) -> int: ...
    pass
class SatDefaultPhase():
    """
    Members:

      RANDOM_INITIAL_PHASE

      FALSE

      TRUE

      JEROS_LOW_WANG
    """
    def __eq__(self, other: object) -> bool: ...
    def __getstate__(self) -> int: ...
    def __hash__(self) -> int: ...
    def __index__(self) -> int: ...
    def __init__(self, value: int) -> None: ...
    def __int__(self) -> int: ...
    def __ne__(self, other: object) -> bool: ...
    def __repr__(self) -> str: ...
    def __setstate__(self, state: int) -> None: ...
    @property
    def name(self) -> str:
        """
        :type: str
        """
    @property
    def value(self) -> int:
        """
        :type: int
        """
    FALSE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.FALSE: 0>
    JEROS_LOW_WANG: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.JEROS_LOW_WANG: 2>
    RANDOM_INITIAL_PHASE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.RANDOM_INITIAL_PHASE: 3>
    TRUE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.TRUE: 1>
    __members__: dict # value = {'RANDOM_INITIAL_PHASE': <SatDefaultPhase.RANDOM_INITIAL_PHASE: 3>, 'FALSE': <SatDefaultPhase.FALSE: 0>, 'TRUE': <SatDefaultPhase.TRUE: 1>, 'JEROS_LOW_WANG': <SatDefaultPhase.JEROS_LOW_WANG: 2>}
    pass
class Solver():
    def CheckSat(self) -> SolverOutput: ...
    def __enter__(self) -> Solver: ...
    def __exit__(self, arg0: object, arg1: object, arg2: object) -> None: ...
    @typing.overload
    def __init__(self) -> None: ...
    @typing.overload
    def __init__(self, arg0: Config) -> None: ...
    @typing.overload
    def __init__(self, arg0: str) -> None: ...
    pass
class SolverOutput():
    def __str__(self) -> str: ...
    @property
    def actual_precision(self) -> mpq_class:
        """
        :type: mpq_class
        """
    @property
    def is_sat(self) -> bool:
        """
        :type: bool
        """
    @property
    def lower_bound(self) -> mpq_class:
        """
        :type: mpq_class
        """
    @property
    def model(self) -> Box:
        """
        :type: Box
        """
    @property
    def n_assertions(self) -> int:
        """
        :type: int
        """
    @property
    def produce_models(self) -> bool:
        """
        :type: bool
        """
    @property
    def result(self) -> dlinear::SolverResult:
        """
        :type: dlinear::SolverResult
        """
    @property
    def upper_bound(self) -> mpq_class:
        """
        :type: mpq_class
        """
    @property
    def with_timings(self) -> bool:
        """
        :type: bool
        """
    pass
class Variable():
    def __abs__(self) -> Expression: ...
    @typing.overload
    def __add__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __add__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __eq__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __eq__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __ge__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __ge__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __gt__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __gt__(self, arg0: float) -> Formula: ...
    def __hash__(self) -> int: ...
    @typing.overload
    def __init__(self, arg0: str) -> None: ...
    @typing.overload
    def __init__(self, arg0: str, arg1: VariableType) -> None: ...
    @typing.overload
    def __le__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __le__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __lt__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __lt__(self, arg0: float) -> Formula: ...
    @typing.overload
    def __mul__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __mul__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __ne__(self, arg0: Variable) -> Formula: ...
    @typing.overload
    def __ne__(self, arg0: float) -> Formula: ...
    def __neg__(self) -> Expression: ...
    def __pos__(self) -> Expression: ...
    def __pow__(self, arg0: Expression) -> Expression: ...
    def __radd__(self, arg0: float) -> Expression: ...
    def __repr__(self) -> str: ...
    def __rmul__(self, arg0: float) -> Expression: ...
    def __rsub__(self, arg0: float) -> Expression: ...
    def __rtruediv__(self, arg0: float) -> Expression: ...
    def __str__(self) -> str: ...
    @typing.overload
    def __sub__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __sub__(self, arg0: float) -> Expression: ...
    @typing.overload
    def __truediv__(self, arg0: Variable) -> Expression: ...
    @typing.overload
    def __truediv__(self, arg0: float) -> Expression: ...
    def get_id(self) -> int: ...
    def get_type(self) -> VariableType: ...
    pass
class VariableType():
    """
    Members:

      Real

      Int

      Bool

      Binary
    """
    def __eq__(self, other: object) -> bool: ...
    def __getstate__(self) -> int: ...
    def __hash__(self) -> int: ...
    def __index__(self) -> int: ...
    def __init__(self, value: int) -> None: ...
    def __int__(self) -> int: ...
    def __ne__(self, other: object) -> bool: ...
    def __repr__(self) -> str: ...
    def __setstate__(self, state: int) -> None: ...
    @property
    def name(self) -> str:
        """
        :type: str
        """
    @property
    def value(self) -> int:
        """
        :type: int
        """
    Binary: pydlinear._pydlinear.VariableType # value = <VariableType.Binary: 2>
    Bool: pydlinear._pydlinear.VariableType # value = <VariableType.Bool: 3>
    Int: pydlinear._pydlinear.VariableType # value = <VariableType.Int: 1>
    Real: pydlinear._pydlinear.VariableType # value = <VariableType.Real: 0>
    __members__: dict # value = {'Real': <VariableType.Real: 0>, 'Int': <VariableType.Int: 1>, 'Bool': <VariableType.Bool: 3>, 'Binary': <VariableType.Binary: 2>}
    pass
class Variables():
    def IsStrictSubsetOf(self, arg0: Variables) -> bool: ...
    def IsStrictSupersetOf(self, arg0: Variables) -> bool: ...
    def IsSubsetOf(self, arg0: Variables) -> bool: ...
    def IsSupersetOf(self, arg0: Variables) -> bool: ...
    @typing.overload
    def __add__(self, arg0: Variables) -> Variables: ...
    @typing.overload
    def __add__(self, arg0: Variable) -> Variables: ...
    def __contains__(self, arg0: Variable) -> bool: ...
    def __eq__(self, arg0: Variables) -> bool: ...
    def __hash__(self) -> int: ...
    @typing.overload
    def __init__(self) -> None: ...
    @typing.overload
    def __init__(self, arg0: typing.List[Variable]) -> None: ...
    def __iter__(self) -> typing.Iterator: ...
    def __len__(self) -> int: ...
    def __lt__(self, arg0: Variables) -> bool: ...
    def __radd__(self, arg0: Variable) -> Variables: ...
    def __repr__(self) -> str: ...
    def __str__(self) -> str: ...
    @typing.overload
    def __sub__(self, arg0: Variables) -> Variables: ...
    @typing.overload
    def __sub__(self, arg0: Variable) -> Variables: ...
    def empty(self) -> bool: ...
    @typing.overload
    def erase(self, arg0: Variable) -> int: ...
    @typing.overload
    def erase(self, arg0: Variables) -> int: ...
    def include(self, arg0: Variable) -> bool: ...
    @typing.overload
    def insert(self, arg0: Variable) -> None: ...
    @typing.overload
    def insert(self, arg0: Variables) -> None: ...
    def size(self) -> int: ...
    def to_string(self) -> str: ...
    pass
def set_verbosity(arg0: int) -> None:
    """
    Set the verbosity level of dlinear.
    -1: off
    0: critical
    1: error
    2: warn
    3: info
    4: debug
    5: trace
    """
AUTO: pydlinear._pydlinear.Format # value = <Format.AUTO: 0>
Binary: pydlinear._pydlinear.VariableType # value = <VariableType.Binary: 2>
Bool: pydlinear._pydlinear.VariableType # value = <VariableType.Bool: 3>
FALSE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.FALSE: 0>
Int: pydlinear._pydlinear.VariableType # value = <VariableType.Int: 1>
JEROS_LOW_WANG: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.JEROS_LOW_WANG: 2>
MPS: pydlinear._pydlinear.Format # value = <Format.MPS: 2>
QSOPTEX: pydlinear._pydlinear.LPSolver # value = <LPSolver.QSOPTEX: 1>
RANDOM_INITIAL_PHASE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.RANDOM_INITIAL_PHASE: 3>
Real: pydlinear._pydlinear.VariableType # value = <VariableType.Real: 0>
SMT2: pydlinear._pydlinear.Format # value = <Format.SMT2: 1>
SOPLEX: pydlinear._pydlinear.LPSolver # value = <LPSolver.SOPLEX: 0>
TRUE: pydlinear._pydlinear.SatDefaultPhase # value = <SatDefaultPhase.TRUE: 1>
__version__ = '0.0.1'
