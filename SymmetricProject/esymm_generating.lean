import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Init.Order.Defs
import Init.Data.Nat.Basic
import SymmetricProject.esymm_basic
/- The purpose of this file is to prove the generating function identity

$$\prod_{i=1}^n (z - x_i) = \sum_{k=0}^n (-1)^k S_{n,k}(x) z^{n-k}$$

(equation (1.1) in the paper)
-/

-- basic facts about the expression "esymm n k x" (or $S_{n,k}(x)$) - the k^th elementary symmetric polynomial of the first n variables of an infinite sequence x of real variables


open Finset
open BigOperators
open Polynomial

/-- We have two lemmas to help with the proof.  The first lemma asserts that

$$ \sum_{k=0}^n a_k z^{n-k} = \sum_{k=0}^{n+1} 1_{k > 0} a_{k-1} z^{n+1-k}$$

and the second asserts that

$$ \sum_{k=0}^n a_k z^{n-k+1} = \sum_{k=0}^{n+1} 1_{k \leq n} a_k z^{n+1-k}.$$
-/

lemma powerseries_inc_n (n : ℕ) (a : ℕ → ℝ) : ∑ k in range (n+1), monomial (n-k) (a k) = ∑ k in range (n+1+1), monomial (n+1-k) (if k > 0 then a (k-1) else 0) := by
  rw [sum_range_succ' _ (n+1)]
  /-
  Original:
    simp

  LLM-aesop:
  -/
  simp_all only [ge_iff_le, add_le_add_iff_right, Nat.succ_sub_succ_eq_sub, gt_iff_lt, add_pos_iff, or_true,
    add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right, ite_true, add_eq_zero_iff, and_false, tsub_zero,
    tsub_eq_zero_of_le, ite_false, map_zero, add_zero]

lemma powerseries_inc_n_mul (n : ℕ) (a : ℕ → ℝ) : ∑ k in range (n+1), monomial (n-k+1) (a k) = ∑ k in range (n+1+1), monomial (n+1-k) (if k ≤ n then a k else 0) := by
  rw [sum_range_succ _ (n+1)]
  simp
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by
    /-
    Original:
      rw [mem_range] at hk
      linarith

    LLM-aesop:
    -/
    simp_all only [mem_range]
    linarith
  /-
  Original:
    congr
    . simp [Nat.sub_add_comm hk']
    simp [hk']

  LLM-aesop
  -/
  simp_all only [mem_range, ge_iff_le, ite_true]
  rw [Nat.succ_sub hk']

-- Now we can prove the main result, basically by induction on n and using the Pascal identity.  The above lemmas are used to align the series to each other so that we can compare coefficients easily.

-- TODO: refactor this using Polynomial.coeff_eq_esymm_roots_of_card
theorem esymm_genfn (n : ℕ) (x : ℕ → ℝ): ∏ i in (range n), (X - C (x i)) = ∑ k in range (n+1), monomial (n-k) ((-1) ^ ↑k * esymm n k x) := by
  induction' n with n hn
  . /-
    Original:
      simp [esymm, set_binom]

    LLM-aesop:
    -/
    simp_all only [Nat.zero_eq, range_zero, prod_empty, zero_add, range_one, ge_iff_le, zero_le, tsub_eq_zero_of_le,
      monomial_zero_left, map_mul, map_pow, map_neg, map_one, sum_singleton, pow_zero, esymm_zero_eq_one, mul_one]
  rw [Nat.succ_eq_add_one, prod_range_succ, hn, mul_sub, sum_mul, sum_mul]
  simp
  rw [powerseries_inc_n, powerseries_inc_n_mul]
  symm
  rw [eq_sub_iff_add_eq, <-sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [<- monomial_add]
  congr
  rcases k with _ | k
  . /-
    Original:
      simp [esymm, set_binom]

    LLM-aesop:
    -/
    simp_all only [ge_iff_le, Nat.zero_eq, mem_range, add_pos_iff, or_true, or_self, pow_zero, esymm_zero_eq_one,
      mul_one, tsub_eq_zero_of_le, one_mul, ite_false, add_zero, zero_le, ite_true]
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  have h : k+1 > 0 := by linarith
  simp [h]
  clear hn hk h
  have h : (if k + 1 ≤ n then (-1) ^ (k + 1) * esymm n (k + 1) x else 0) = (-1) ^ (k + 1) * esymm n (k + 1) x := by
    rcases em (k + 1 ≤ n) with hkn | hkn
    . simp [hkn]
    simp [hkn]
    apply esymm_eq_zero
    /-
    Original:
      linarith

    LLM-aesop:
    -/
    simp_all only [not_le]
  rw [h]
  clear h
  have h : (-1)^k = (-1)^(k+1) * (-1:ℝ) := by
    /-
    Original:
      rw [pow_add]
      simp

    LLM-aesop:
    -/
    simp_all only [mul_neg, mul_one]
    simp [pow_succ]
  rw [h]
  clear h
  rw [esymm_pascal]
  ring
