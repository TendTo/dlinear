import sys
import pydlinear as pdl


def main():
    config = pdl.Config.from_args(sys.argv)
    solver = pdl.SmtSolver(config)
    result = solver.Parse()
    if result.result == pdl.SmtResult.UNSOLVED and config.enforce_check_sat:
        result = solver.CheckSat()
    if not config.silent and not result.matched_expectation(solver.GetExpected()):
        print(f"WARNING: Expected {solver.GetExpected()} but got {result.result}")
    if not config.silent and config.verify and result.is_sat:
        if solver.Verify(result.complete_model):
            print("Model correctly satisfies the input")
        else:
            print("WARNING: Model does not satisfy the input")
    sys.exit(result.exit_code)


if __name__ == "__main__":
    main()
