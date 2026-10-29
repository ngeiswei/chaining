"""Inductive decision procedure for minimal factored forms (MFF).

Decides whether a factored form over {∧, ∨, ¬-on-leaves} has the minimum
possible number of literals among all equivalent factored forms.
"""
from .ast import (And, G0, G1, Gnd, Lit, Node, Or, ascii_repr, cofactor_expr,
                  eval_node, parse, rho, simplify, to_str, vars_of)
from .boolfunc import (BoolFunc, alpha_beta, cofactor, eq, essential_vars,
                       is_one, is_zero, lower_bound, truth_table, var_status)
from .certify import (BudgetExceeded, Certifier, Result, Verdict, certify,
                      render_result)

__version__ = "0.1.0"

__all__ = [
    "And", "Or", "Lit", "Gnd", "G0", "G1", "Node",
    "parse", "to_str", "ascii_repr", "rho", "vars_of", "eval_node",
    "cofactor_expr", "simplify",
    "BoolFunc", "truth_table", "cofactor", "eq", "is_zero", "is_one",
    "var_status", "alpha_beta", "lower_bound", "essential_vars",
    "Certifier", "Result", "Verdict", "certify", "render_result",
    "BudgetExceeded",
]