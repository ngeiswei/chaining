"""Tests for the Boolean-function semantic oracle."""
import unittest

from inductive_mff.ast import parse
from inductive_mff.boolfunc import (BoolFunc, alpha_beta, cofactor, eq,
                                    essential_vars, is_one, is_zero,
                                    lower_bound, truth_table, var_status)

UNI = ("a", "b", "c")


def fn_of(s):
    return truth_table(parse(s), UNI)


class TestTruthTable(unittest.TestCase):
    def test_tautology(self):
        self.assertTrue(is_one(fn_of("a ∨ ¬a")))

    def test_contradiction(self):
        self.assertTrue(is_zero(fn_of("a ∧ ¬a")))

    def test_equivalence(self):
        self.assertTrue(eq(fn_of("(a ∨ b) ∧ (a ∨ c)"), fn_of("a ∨ (b ∧ c)")))


class TestCofactor(unittest.TestCase):
    def test_independent_variable(self):
        f = fn_of("a")
        self.assertTrue(eq(cofactor(f, "b", 0), f))

    def test_majority_fixed(self):
        f = fn_of("(a ∨ b) ∧ (a ∨ c) ∧ (b ∨ c)")
        self.assertTrue(eq(cofactor(f, "a", 0), fn_of("b ∧ c")))
        self.assertTrue(eq(cofactor(f, "a", 1), fn_of("b ∨ c")))


class TestClassification(unittest.TestCase):
    def test_unate(self):
        self.assertEqual(var_status(fn_of("a ∨ (b ∧ c)"), "a"), "pos-unate")
        self.assertEqual(var_status(fn_of("a ∨ (b ∧ c)"), "b"), "pos-unate")

    def test_binate(self):
        xor = fn_of("(a ∧ ¬b) ∨ (¬a ∧ b)")
        self.assertEqual(var_status(xor, "a"), "binate")
        self.assertEqual(var_status(xor, "b"), "binate")

    def test_neg_unate(self):
        self.assertEqual(var_status(fn_of("¬a ∨ b"), "a"), "neg-unate")

    def test_nonessential(self):
        self.assertEqual(var_status(fn_of("a"), "b"), "nonessential")

    def test_alpha_beta_majority(self):
        # majority-3: every variable is positive unate -> alpha=3, beta=0
        self.assertEqual(alpha_beta(fn_of("(a ∨ b) ∧ (a ∨ c) ∧ (b ∨ c)")), (3, 0))

    def test_alpha_beta_xor(self):
        # xor: two binate variables -> alpha=0, beta=2 -> LB = 4
        self.assertEqual(alpha_beta(fn_of("(a ∧ ¬b) ∨ (¬a ∧ b)")), (0, 2))

    def test_lower_bound(self):
        self.assertEqual(lower_bound(fn_of("(a ∧ ¬b) ∨ (¬a ∧ b)")), 4)
        self.assertEqual(lower_bound(fn_of("a ∨ (b ∧ c)")), 3)

    def test_essential_vars(self):
        self.assertEqual(essential_vars(fn_of("a ∨ (b ∧ c)")), {"a", "b", "c"})


if __name__ == "__main__":
    unittest.main()