"""Tests for the inductive minimal-factored-form decision procedure."""
import unittest

from inductive_mff import certify
from inductive_mff.ast import parse, rho, to_str
from inductive_mff.boolfunc import eq, truth_table
from inductive_mff.certify import Verdict


def check_smaller_equivalent(res):
    """A NOT_MINIMAL certificate must be equivalent and strictly smaller."""
    assert res.verdict == Verdict.NOT_MINIMAL
    uni = res.fn.vars
    assert eq(truth_table(res.best, uni), res.fn)
    assert rho(res.best) < res.input_cost


class TestMinimal(unittest.TestCase):
    def test_single_literal(self):
        self.assertEqual(certify("a").verdict, Verdict.MINIMAL)

    def test_negated_literal(self):
        self.assertEqual(certify("¬a").verdict, Verdict.MINIMAL)

    def test_disjoint_sum(self):
        r = certify("(a ∨ b) ∧ (c ∨ d)")
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual(r.cost, 4)

    def test_disjoint_product_of_sums(self):
        r = certify("(¬a ∨ b) ∧ (¬c ∨ d)")
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual(r.cost, 4)

    def test_rpo_tight_binate_xor(self):
        # XOR is binate in both variables; LB = 2+2 = 4 == rho.
        r = certify("(a ∧ ¬b) ∨ (¬a ∧ b)")
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual(r.cost, 4)

    def test_three_unate(self):
        r = certify("a ∨ (b ∧ c)")
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual(r.cost, 3)


class TestNotMinimalWithoutExact(unittest.TestCase):
    def test_absorption(self):
        r = certify("(a ∨ b) ∧ (a ∨ c)")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("a ∨ (b ∧ c)"))
        self.assertEqual(r.cost, 3)

    def test_idempotent_operand(self):
        r = certify("a ∧ a")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("a"))

    def test_complement_or(self):
        r = certify("a ∨ ¬a")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("1"))

    def test_complement_and(self):
        r = certify("a ∧ ¬a")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("0"))

    def test_redundant_subformula(self):
        # a ∨ (b ∧ ¬b) ≡ a, and 1 < 3 literals.
        r = certify("a ∨ (b ∧ ¬b)")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("a"))

    def test_shannon_shared_variable(self):
        # (a ∨ b) ∧ (a ∨ c) ≡ a ∨ bc, handled by the Shannon-split merge.
        r = certify("(a ∨ b) ∧ (a ∨ c)")
        check_smaller_equivalent(r)
        self.assertEqual(to_str(r.best), "(a ∨ (b ∧ c))")

    def test_constant_absorption(self):
        r = certify("0 ∧ a")
        check_smaller_equivalent(r)
        self.assertEqual(r.best, parse("0"))

    def test_constant_identity(self):
        # 1 ∧ a ≡ a; same literal count, so MINIMAL (folded, then decided).
        r = certify("1 ∧ a")
        self.assertEqual(r.verdict, Verdict.MINIMAL)


class TestUnknownRequiresExact(unittest.TestCase):
    def test_majority3_six_literals_reduced_by_operand(self):
        # (a∨b)(a∨c)(b∨c) ≡ majority-3.  Its left operand (a∨b)(a∨c)
        # collapses to a∨bc, so the whole thing reduces to 5 literals.
        r = certify("(a ∨ b) ∧ (a ∨ c) ∧ (b ∨ c)")
        self.assertEqual(r.verdict, Verdict.NOT_MINIMAL)
        check_smaller_equivalent(r)
        self.assertEqual(r.cost, 5)

    def test_majority3_minimal_form_is_unknown(self):
        # The 5-literal minimum form itself cannot be inductively certified.
        r = certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)")
        self.assertEqual(r.verdict, Verdict.UNKNOWN)
        self.assertEqual(r.input_cost, 5)

    def test_majority3_exact_confirms_minimal(self):
        r = certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)", exact=True)
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual(r.cost, 5)

    def test_majority3_exact_reduces_6_to_5(self):
        r = certify("(a ∨ b) ∧ (a ∨ c) ∧ (b ∨ c)", exact=True)
        self.assertEqual(r.verdict, Verdict.NOT_MINIMAL)
        check_smaller_equivalent(r)
        self.assertEqual(r.cost, 5)


class TestExactCompletenessSmall(unittest.TestCase):
    def test_small_functions_all_certified(self):
        # A tiny sanity sweep: every factored form over {a,b} with <= 3
        # literals is decided (no UNKNOWN) when exact=True.
        forms = [
            "a", "¬a", "a ∨ b", "a ∧ b", "a ∨ ¬a", "a ∧ ¬a",
            "(a ∧ b) ∨ a", "a ∨ (a ∧ b)", "¬a ∨ (a ∧ b)",
        ]
        for s in forms:
            r = certify(s, exact=True)
            self.assertIn(r.verdict, (Verdict.MINIMAL, Verdict.NOT_MINIMAL), s)
            if r.verdict == Verdict.NOT_MINIMAL:
                check_smaller_equivalent(r)


class TestTiming(unittest.TestCase):
    def test_elapsed_is_recorded(self):
        r = certify("(a ∨ b) ∧ (a ∨ c)")
        self.assertIsInstance(r.elapsed, float)
        self.assertGreaterEqual(r.elapsed, 0.0)

    def test_elapsed_in_seconds_and_monotone_with_work(self):
        # The exact fallback does vastly more work than a lower-bound hit, so
        # its elapsed time must be recorded as strictly larger.
        quick = certify("(a ∨ b) ∧ (c ∨ d)")
        slow = certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)", exact=True)
        self.assertGreater(slow.elapsed, quick.elapsed)

    def test_render_includes_time(self):
        from inductive_mff import render_result
        self.assertIn("time", render_result(certify("a ∧ a")))


class TestRender(unittest.TestCase):
    def test_render_not_minimal(self):
        from inductive_mff import render_result
        r = certify("(a ∨ b) ∧ (a ∨ c)")
        out = render_result(r)
        self.assertIn("NOT_MINIMAL", out)
        self.assertIn("(a ∨ (b ∧ c))", out)


if __name__ == "__main__":
    unittest.main()