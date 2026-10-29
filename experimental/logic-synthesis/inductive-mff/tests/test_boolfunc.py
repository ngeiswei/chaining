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


class TestMask(unittest.TestCase):
    """``BoolFunc.mask`` is the all-ones truth table: 2**(2**n) - 1 bits."""

    def test_mask_is_two_to_the_two_to_the_n_minus_one(self):
        for n in range(0, 6):
            fn = BoolFunc(tuple("abcdef"[:n]), 0)
            self.assertEqual(fn.mask, 2 ** (2 ** n) - 1, f"n={n}")

    def test_mask_values(self):
        expected = {0: 1, 1: 3, 2: 15, 3: 255, 4: 65535}
        for n, want in expected.items():
            self.assertEqual(BoolFunc(tuple("abcd"[:n]), 0).mask, want)

    def test_mask_does_not_depend_on_values(self):
        # mask is a property of the variable tuple only, not of the function
        a = BoolFunc(UNI, 0)
        b = BoolFunc(UNI, 0b101)
        self.assertEqual(a.mask, b.mask)

    def test_mask_is_the_tautology(self):
        for s in ("a ∨ ¬a", "1"):
            fn = fn_of(s)
            self.assertEqual(fn.tt, fn.mask)
            self.assertTrue(is_one(fn))

    def test_mask_is_never_the_contradiction(self):
        for n in range(0, 5):
            fn = BoolFunc(tuple("abcd"[:n]), 0)
            self.assertEqual(fn.tt, 0)
            self.assertNotEqual(fn.mask, 0)
            self.assertTrue(is_zero(fn))

    def test_mask_bit_count(self):
        # exactly one bit per assignment of the n variables
        for n in range(0, 5):
            self.assertEqual(BoolFunc(tuple("abcd"[:n]), 0).mask.bit_count(), 2 ** n)

    def test_mask_of_empty_universe(self):
        # n = 0: a single assignment (the empty one), so mask == 1 == True
        fn = BoolFunc((), 0)
        self.assertEqual(fn.n, 0)
        self.assertEqual(fn.mask, 1)


class TestCofactor(unittest.TestCase):
    def test_independent_variable(self):
        f = fn_of("a")
        self.assertTrue(eq(cofactor(f, "b", 0), f))

    def test_absorbs_into_or_when_a_positive(self):
        # (a ∨ (b ∧ c)): a=1 makes the disjunction true, a=0 leaves b ∧ c.
        f = fn_of("a ∨ (b ∧ c)")
        self.assertTrue(eq(cofactor(f, "a", 0), fn_of("b ∧ c")))
        self.assertTrue(eq(cofactor(f, "a", 1), fn_of("1")))
        self.assertTrue(is_one(cofactor(f, "a", 1)))

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