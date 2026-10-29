"""Tests for the inductive minimal-factored-form decision procedure.

Set ``INDUCTIVE_MFF_SKIP_SLOW=1`` to skip the exhaustive-search tests in
``TestSlowExact`` (they account for most of the suite's runtime).
"""
import os
import unittest

from inductive_mff import certify
from inductive_mff.ast import parse, rho, to_str
from inductive_mff.boolfunc import eq, truth_table
from inductive_mff.ast import And, Or
from inductive_mff.certify import Verdict, _fill, leaf_shapes

SKIP_SLOW = os.environ.get("INDUCTIVE_MFF_SKIP_SLOW", "") not in ("", "0", "false")


# universes for the exhaustive-search tests
U3 = ("a", "b", "c")
U4 = ("a", "b", "c", "d")
U5 = ("a", "b", "c", "d", "e")


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
    def test_unknown_without_exact_is_not_slow(self):
        # The inductive verdict is cheap; only the fallback is expensive.
        r = certify("(a ∧ (b ∨ c)) ∨ (b ∧ c)")
        self.assertEqual(r.verdict, Verdict.UNKNOWN)
        self.assertLess(r.elapsed, 1.0)
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


@unittest.skipIf(SKIP_SLOW, "slow exhaustive-search tests disabled by "
                             "INDUCTIVE_MFF_SKIP_SLOW")
class TestSlowExact(unittest.TestCase):
    """Exhaustive (``exact=True``) decisions on larger formulas.

    Each case forces the ``Σ₂ᴾ``-hard fallback rather than the inductive
    certificates, so these tests cost seconds rather than microseconds.  They
    are the only tests that pin down the *completeness* of the procedure on
    inputs the induction cannot resolve: with ``exact=True`` the verdict is
    always ``MINIMAL`` or ``NOT_MINIMAL``, never ``UNKNOWN``.

    Runtime is roughly 6 s for the four-variable cases plus ~9 s for the
    five-variable one.
    """

    BUDGET = 1_000_000

    def _decide(self, s, universe):
        return certify(s, universe=universe, exact=True, search_budget=self.BUDGET)

    def _assert_equivalent(self, res, universe):
        self.assertTrue(eq(truth_table(res.best, universe), res.fn))

    def _assert_decided(self, res):
        # exact=True must never leave a gap
        self.assertIn(res.verdict, (Verdict.MINIMAL, Verdict.NOT_MINIMAL), res.reason)

    # -- refutations: the exact search must find the smaller form ----------

    def test_consensus_term_is_redundant_4vars(self):
        # (ab ∨ ¬a·c ∨ bc) ≡ ab ∨ ¬a·c; the consensus term bc costs 2 literals.
        r = self._decide("(a ∧ b) ∨ (¬a ∧ c) ∨ (b ∧ c)", U4)
        self._assert_decided(r)
        check_smaller_equivalent(r)
        self.assertEqual(r.verdict, Verdict.NOT_MINIMAL)
        self.assertEqual(r.input_cost, 6)
        self.assertEqual(r.cost, 4)
        self.assertEqual(r.best, parse("(a ∧ b) ∨ (¬a ∧ c)"))

    def test_term_absorbed_by_4var_product(self):
        # (a∨b)(c∨d) ∨ ac ≡ (a∨b)(c∨d), because ac ⇒ (a∨b)(c∨d).
        r = self._decide("((a ∨ b) ∧ (c ∨ d)) ∨ (a ∧ c)", U4)
        self._assert_decided(r)
        check_smaller_equivalent(r)
        self.assertEqual(r.verdict, Verdict.NOT_MINIMAL)
        self.assertEqual((r.input_cost, r.cost), (6, 4))
        self.assertEqual(r.best, parse("(a ∨ b) ∧ (c ∨ d)"))

    def test_consensus_in_second_polarity(self):
        # (a∨b)(¬a∨c)(b∨c) ≡ ac ∨ ¬a·b; consensus again removed.
        r = self._decide("(a ∨ b) ∧ (¬a ∨ c) ∧ (b ∨ c)", U4)
        self._assert_decided(r)
        check_smaller_equivalent(r)
        self.assertEqual(r.verdict, Verdict.NOT_MINIMAL)
        self.assertEqual(r.cost, 4)

    # -- minimality proofs: the exact search must fail to find anything ----

    def test_majority_is_minimal_in_4var_universe(self):
        # majority-3 lifted into a 4-variable universe (d is inessential):
        # the search must still prove that no 4-literal form exists.
        r = self._decide("(a ∧ (b ∨ c)) ∨ (b ∧ c)", U4)
        self._assert_decided(r)
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual((r.input_cost, r.cost), (5, 5))
        self._assert_equivalent(r, U4)

    def test_majority_dual_form_is_minimal(self):
        # (a ∨ bc)(b ∨ c) ≡ majority-3 as well, same 5-literal cost.
        r = self._decide("(a ∨ (b ∧ c)) ∧ (b ∨ c)", U4)
        self._assert_decided(r)
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual((r.input_cost, r.cost), (5, 5))
        self._assert_equivalent(r, U4)

    # -- a genuinely larger input ------------------------------------------

    def test_five_var_composition_with_majority_kernel(self):
        # A 5-variable expression whose inductive certificates only get as far
        # as UNKNOWN on the majority kernel; exact=True closes the gap and the
        # disjoint-support composition step (d ∨ e) then certifies the whole.
        r = self._decide("((a ∧ (b ∨ c)) ∨ (b ∧ c)) ∧ (d ∨ e)", U5)
        self._assert_decided(r)
        self.assertEqual(r.verdict, Verdict.MINIMAL)
        self.assertEqual((r.input_cost, r.cost), (7, 7))
        self._assert_equivalent(r, U5)
        # without exact=True the same input is only partially decided
        plain = certify("((a ∧ (b ∨ c)) ∨ (b ∧ c)) ∧ (d ∨ e)", universe=U5)
        self.assertEqual(plain.verdict, Verdict.UNKNOWN)


class TestLeafShapes(unittest.TestCase):
    """``leaf_shapes(k)``: all ordered full binary ∧/∨ trees with k leaves.

    Leaves are ``None`` placeholders; `_fill` substitutes literals later.
    The count is Catalan(k-1) * 2^(k-1): 1, 2, 8, 40, 224, ...
    """

    @staticmethod
    def _leaf_count(shape):
        if shape is None:
            return 1
        return TestLeafShapes._leaf_count(shape.left) + \
            TestLeafShapes._leaf_count(shape.right)

    @staticmethod
    def _depth(shape):
        if shape is None:
            return 0
        return 1 + max(TestLeafShapes._depth(shape.left),
                       TestLeafShapes._depth(shape.right))

    def test_base_case_is_single_placeholder(self):
        self.assertEqual(leaf_shapes(1), (None,))

    def test_counts_are_catalan_times_two_to_the_k_minus_one(self):
        for k, expected in ((1, 1), (2, 2), (3, 8), (4, 40), (5, 224)):
            self.assertEqual(len(leaf_shapes(k)), expected, f"k={k}")

    def test_two_leaves_gives_one_and_and_one_or(self):
        self.assertEqual(leaf_shapes(2),
                         (And(None, None), Or(None, None)))

    def test_every_shape_has_exactly_k_leaves(self):
        for k in range(1, 6):
            for shape in leaf_shapes(k):
                self.assertEqual(self._leaf_count(shape), k)

    def test_internal_nodes_are_and_or_only(self):
        for k in range(2, 5):
            for shape in leaf_shapes(k):
                if shape is None:
                    continue
                self.assertIsInstance(shape, (And, Or))
                self.assertIsInstance(shape.left, (And, Or, type(None)))
                self.assertIsInstance(shape.right, (And, Or, type(None)))

    def test_shapes_are_pairwise_distinct(self):
        for k in range(1, 6):
            shapes = leaf_shapes(k)
            self.assertEqual(len(set(shapes)), len(shapes), f"k={k}")

    def test_shapes_are_full_binary_trees(self):
        # every internal node has exactly two children, so depth <= k-1
        for k in range(1, 6):
            for shape in leaf_shapes(k):
                self.assertLessEqual(self._depth(shape), max(k - 1, 0))

    def test_three_leaf_shapes_cover_both_operator_orders(self):
        shapes = leaf_shapes(3)
        # left-deep and right-deep, each with the two operator choices
        self.assertIn(And(None, And(None, None)), shapes)
        self.assertIn(And(And(None, None), None), shapes)
        self.assertIn(Or(None, Or(None, None)), shapes)
        self.assertIn(Or(Or(None, None), None), shapes)
        # mixed operators too
        self.assertIn(And(None, Or(None, None)), shapes)
        self.assertIn(Or(And(None, None), None), shapes)

    def test_result_is_cached(self):
        # lru_cache: same object, so callers may share the tuple safely
        self.assertIs(leaf_shapes(4), leaf_shapes(4))

    def test_fill_substitutes_leaves_in_order(self):
        from inductive_mff.ast import Lit
        shapes = leaf_shapes(3)
        first = shapes[0]                      # And(None, And(None, None))
        filled = _fill(first, [Lit("a"), Lit("b"), Lit("c")])
        self.assertEqual(filled, And(Lit("a"), And(Lit("b"), Lit("c"))))
        self.assertEqual(rho(filled), 3)

    def test_fill_into_single_placeholder(self):
        from inductive_mff.ast import Lit
        self.assertEqual(_fill(None, [Lit("x")]), Lit("x"))


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