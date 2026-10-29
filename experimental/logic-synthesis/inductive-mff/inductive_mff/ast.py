"""Expression AST for factored forms over the restricted grammar

    form     ::= 0 | 1 | literal | '(' form '∨' form ')' | '(' form '∧' form ')'
    literal  ::= VAR | '¬' VAR
    VAR      ::= [A-Za-z_][A-Za-z0-9_]*

Negation is confined to the leaves (literals), exactly as requested.
ASCII aliases are accepted for convenience:
    ∧  ≡  &  *  ·
    ∨  ≡  |  +
    ¬  ≡  ~  !  or a trailing apostrophe (e.g.  a' ).

The AST is deliberately immutable (frozen dataclasses) so trees can be used
as dictionary keys in the memoising decision procedure.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Set, Tuple, Union


# --------------------------------------------------------------------------
# AST nodes
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class Gnd:
    """Ground constant 0 (False) or 1 (True)."""

    value: bool


@dataclass(frozen=True)
class Lit:
    """A literal: a variable, possibly negated."""

    var: str
    neg: bool = False


@dataclass(frozen=True)
class And:
    left: "Node"
    right: "Node"


@dataclass(frozen=True)
class Or:
    left: "Node"
    right: "Node"


Node = Union[Gnd, Lit, And, Or]

G0 = Gnd(False)
G1 = Gnd(True)


# --------------------------------------------------------------------------
# Pretty printing
# --------------------------------------------------------------------------
def to_str(node: Node, *, ascii_: bool = False) -> str:
    """Render a node in infix notation, fully parenthesised."""
    if isinstance(node, Gnd):
        return "1" if node.value else "0"
    if isinstance(node, Lit):
        if ascii_:
            return ("~" if node.neg else "") + node.var
        return ("¬" if node.neg else "") + node.var
    if isinstance(node, And):
        op = "&" if ascii_ else "∧"
        return f"({to_str(node.left, ascii_=ascii_)} {op} {to_str(node.right, ascii_=ascii_)})"
    if isinstance(node, Or):
        op = "|" if ascii_ else "∨"
        return f"({to_str(node.left, ascii_=ascii_)} {op} {to_str(node.right, ascii_=ascii_)})"
    raise TypeError(f"not a node: {node!r}")


def ascii_repr(node: Node) -> str:
    return to_str(node, ascii_=True)


# --------------------------------------------------------------------------
# Syntactic measures
# --------------------------------------------------------------------------
def rho(node: Node) -> int:
    """Number of literals (leaf count); constants contribute 0."""
    if isinstance(node, Gnd):
        return 0
    if isinstance(node, Lit):
        return 1
    if isinstance(node, (And, Or)):
        return rho(node.left) + rho(node.right)
    raise TypeError(node)


def vars_of(node: Node) -> Set[str]:
    """Set of variable names occurring syntactically in the expression."""
    if isinstance(node, Gnd):
        return set()
    if isinstance(node, Lit):
        return {node.var}
    if isinstance(node, (And, Or)):
        return vars_of(node.left) | vars_of(node.right)
    raise TypeError(node)


def eval_node(node: Node, assignment: Dict[str, int]) -> bool:
    """Evaluate a node under a complete assignment (bool for each variable)."""
    if isinstance(node, Gnd):
        return node.value
    if isinstance(node, Lit):
        v = bool(assignment[node.var])
        return (not v) if node.neg else v
    if isinstance(node, And):
        return eval_node(node.left, assignment) and eval_node(node.right, assignment)
    if isinstance(node, Or):
        return eval_node(node.left, assignment) or eval_node(node.right, assignment)
    raise TypeError(node)


# --------------------------------------------------------------------------
# Constant folding / local simplification
#
# `simplify` only applies *equivalence-preserving, literal-count non-increasing*
# rewrites at every level:
#     And(0, x) -> 0        Or(1, x) -> 1
#     And(1, x) -> x        Or(0, x) -> x
#     And(x, x) -> x        Or(x, x) -> x
#     And(x, ¬x) -> 0       Or(x, ¬x) -> 1   (x a literal)
# It never reorders operands.  It is used for witnesses and cofactors, *not*
# for the input the user asks about.
# --------------------------------------------------------------------------
def _is_complement(a: Node, b: Node) -> bool:
    return (
        isinstance(a, Lit)
        and isinstance(b, Lit)
        and a.var == b.var
        and a.neg != b.neg
    )


def simplify(node: Node) -> Node:
    if isinstance(node, (Gnd, Lit)):
        return node
    if isinstance(node, And):
        l = simplify(node.left)
        r = simplify(node.right)
        if isinstance(l, Gnd):
            return G0 if not l.value else r
        if isinstance(r, Gnd):
            return G0 if not r.value else l
        if l == r:
            return l
        if _is_complement(l, r):
            return G0
        return And(l, r)
    if isinstance(node, Or):
        l = simplify(node.left)
        r = simplify(node.right)
        if isinstance(l, Gnd):
            return G1 if l.value else r
        if isinstance(r, Gnd):
            return G1 if r.value else l
        if l == r:
            return l
        if _is_complement(l, r):
            return G1
        return Or(l, r)
    raise TypeError(node)


def cofactor_expr(node: Node, var: str, value: int) -> Node:
    """Cofactor an expression w.r.t. var=value (0 or 1), with local folding."""
    if isinstance(node, Gnd):
        return node
    if isinstance(node, Lit):
        if node.var == var:
            v = value if not node.neg else 1 - value
            return G1 if v else G0
        return node
    if isinstance(node, And):
        return simplify(And(cofactor_expr(node.left, var, value),
                            cofactor_expr(node.right, var, value)))
    if isinstance(node, Or):
        return simplify(Or(cofactor_expr(node.left, var, value),
                           cofactor_expr(node.right, var, value)))
    raise TypeError(node)


# --------------------------------------------------------------------------
# Parser
# --------------------------------------------------------------------------
def tokenize(s: str) -> List[Tuple]:
    toks: List[Tuple] = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c in "∧&*·":
            toks.append(("AND", c))
            i += 1
            continue
        if c in "∨|+":
            toks.append(("OR", c))
            i += 1
            continue
        if c in "¬~!":
            toks.append(("NOT", c))
            i += 1
            continue
        if c == "(":
            toks.append(("LP", c))
            i += 1
            continue
        if c == ")":
            toks.append(("RP", c))
            i += 1
            continue
        if c in "01":
            toks.append(("CONST", c))
            i += 1
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (s[j].isalnum() or s[j] == "_"):
                j += 1
            name = s[i:j]
            neg = False
            k = j
            while k < n and s[k] == "'":  # trailing apostrophe = negation
                neg = not neg
                k += 1
            toks.append(("ID", name, neg))
            i = k
            continue
        raise ValueError(f"unexpected character {c!r} at position {i}")
    return toks


class _Parser:
    def __init__(self, toks: List[Tuple]):
        self.toks = toks
        self.pos = 0

    def peek(self):
        return self.toks[self.pos] if self.pos < len(self.toks) else None

    def next_(self):
        t = self.peek()
        self.pos += 1
        return t

    def parse(self) -> Node:
        if not self.toks:
            raise ValueError("empty formula")
        node = self.parse_or()
        if self.peek() is not None:
            raise ValueError(f"unexpected token {self.peek()}")
        return node

    def parse_or(self) -> Node:
        node = self.parse_and()
        while self.peek() is not None and self.peek()[0] == "OR":
            self.next_()
            node = Or(node, self.parse_and())
        return node

    def parse_and(self) -> Node:
        node = self.parse_factor()
        while self.peek() is not None and self.peek()[0] == "AND":
            self.next_()
            node = And(node, self.parse_factor())
        return node

    def parse_factor(self) -> Node:
        t = self.next_()
        if t is None:
            raise ValueError("unexpected end of formula")
        kind = t[0]
        if kind == "NOT":
            atom = self.parse_factor()
            if isinstance(atom, Lit):
                return Lit(atom.var, not atom.neg)
            if isinstance(atom, Gnd):
                return G1 if not atom.value else G0
            raise ValueError("negation (¬) is only allowed on literals, "
                             "not on compound subformulas")
        if kind == "ID":
            return Lit(t[1], t[2])
        if kind == "CONST":
            return Gnd(t[1] == "1")
        if kind == "LP":
            node = self.parse_or()
            if self.peek() is None or self.peek()[0] != "RP":
                raise ValueError("missing closing parenthesis")
            self.next_()
            return node
        raise ValueError(f"unexpected token {t}")


def parse(s: str) -> Node:
    """Parse a formula string into the AST."""
    return _Parser(tokenize(s)).parse()