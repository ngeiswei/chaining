"""Tests for the AST: parsing, printing, simplification, cofactors."""
import unittest

from inductive_mff.ast import (And, G0, G1, Lit, Or, ascii_repr, cofactor_expr,
                               parse, rho, simplify, to_str, vars_of)


class TestParse(unittest.TestCase):
    def test_unicode_operators(self):
        e = parse("(a ∨ b) ∧ ¬c")
        self.assertEqual(to_str(e), "((a ∨ b) ∧ ¬c)")

    def test_ascii_aliases(self):
        e = parse("(a | b) & ~c")
        self.assertEqual(to_str(e), "((a ∨ b) ∧ ¬c)")

    def test_trailing_apostrophe(self):
        e = parse("a' ∨ b")
        self.assertEqual(to_str(e), "(¬a ∨ b)")

    def test_precedence_and_binds_tighter(self):
        e = parse("a ∨ b ∧ c")
        self.assertEqual(to_str(e), "(a ∨ (b ∧ c))")

    def test_negation_only_on_leaves(self):
        with self.assertRaises(ValueError):
            parse("¬(a ∨ b)")

    def test_constant_leaves(self):
        e = parse("1 ∧ a")
        self.assertEqual(to_str(e), "(1 ∧ a)")

    def test_empty(self):
        with self.assertRaises(ValueError):
            parse("")


class TestMeasures(unittest.TestCase):
    def test_rho(self):
        self.assertEqual(rho(parse("(a ∨ b) ∧ ¬c")), 3)
        self.assertEqual(rho(parse("1")), 0)
        self.assertEqual(rho(parse("a")), 1)

    def test_vars_of(self):
        self.assertEqual(vars_of(parse("(a ∨ b) ∧ ¬c")), {"a", "b", "c"})
        self.assertEqual(vars_of(G1), set())


class TestSimplify(unittest.TestCase):
    def test_identity_and_absorption(self):
        self.assertEqual(simplify(parse("a ∧ 1")), Lit("a"))
        self.assertEqual(simplify(parse("a ∧ 0")), G0)
        self.assertEqual(simplify(parse("a ∨ 1")), G1)
        self.assertEqual(simplify(parse("a ∨ 0")), Lit("a"))

    def test_idempotence(self):
        self.assertEqual(simplify(parse("a ∧ a")), Lit("a"))
        self.assertEqual(simplify(parse("a ∨ a")), Lit("a"))

    def test_complement(self):
        self.assertEqual(simplify(parse("a ∧ ¬a")), G0)
        self.assertEqual(simplify(parse("a ∨ ¬a")), G1)

    def test_no_reordering(self):
        e = parse("a ∧ b")
        self.assertIsInstance(simplify(e), And)


class TestCofactor(unittest.TestCase):
    def test_cofactor_literal_positive(self):
        self.assertEqual(cofactor_expr(parse("a ∨ b"), "a", 1), G1)

    def test_cofactor_removes_variable(self):
        e = cofactor_expr(parse("a ∨ b"), "a", 0)
        self.assertEqual(e, Lit("b"))

    def test_cofactor_negated_literal(self):
        self.assertEqual(cofactor_expr(parse("¬a"), "a", 0), G1)
        self.assertEqual(cofactor_expr(parse("¬a"), "a", 1), G0)

    def test_cofactor_compound(self):
        e = cofactor_expr(parse("(a ∨ b) ∧ (a ∨ c)"), "a", 0)
        self.assertEqual(e, parse("b ∧ c"))
        e = cofactor_expr(parse("(a ∨ b) ∧ (a ∨ c)"), "a", 1)
        self.assertEqual(e, G1)


if __name__ == "__main__":
    unittest.main()