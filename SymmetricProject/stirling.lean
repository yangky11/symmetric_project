import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the some "cheap" Stirling bounds for factorial and binomial coefficients.
-/

open Real
open Nat
open Finset
open BigOperators

/-- n! is upper bounded by n^n -/
lemma factorial_le {n : ℕ} : n ! ≤ n^n := by
  induction' n with m hm
  . simp
  rw [factorial_succ, Nat.pow_succ, succ_eq_add_one, mul_comm]
  gcongr
  apply le_trans hm
  gcongr
  /-
  Original:
    linarith

  LLM-aesop:
  -/
  simp_all only [le_add_iff_nonneg_right]

/-- n! is lower bounded by n^n/e^n -/
lemma factorial_ge {n : ℕ} : n ! ≥ n^n / exp n := by
  have h := calc
    exp n ≥ ∑ k in range (n+1), (n:ℝ)^k / k ! := by
      rw [ge_iff_le]
      apply Real.sum_le_exp_of_nonneg
      positivity
    _ ≥ (n:ℝ)^n/n ! := by
      rw [sum_range_succ]
      simp
      apply sum_nonneg
      intro k _
      positivity
  apply_fun (fun (X:ℝ) =>  X * (n ! / exp n)) at h
  . have h1 : (n !: ℝ) ≠ 0 := by
      /-
      Original:
        positivity

      LLM-aesop:
      -/
      simp_all only [gt_iff_lt, ne_eq, cast_eq_zero]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [CharP.cast_eq_zero, div_zero, zero_div, mul_zero, le_refl]
      apply factorial_ne_zero n a
    have h2 : exp n ≠ 0 := by
      /-
        Original:
          positivity

        LLM-aesop:
        -/
      simp_all only [gt_iff_lt, ne_eq, cast_eq_zero]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only [div_zero, mul_zero, le_refl]
      simp only [exp_ne_zero] at a
    /-
    Original:
      field_simp at h
      rw [ge_iff_le]
      convert h using 1
      . congr
        norm_cast
      field_simp
      ring

    LLM-aesop:-/
    simp_all only [gt_iff_lt, ne_eq, cast_eq_zero, cast_pow, ge_iff_le]
    norm_cast at h
    simp_all only [cast_pow, gt_iff_lt]
    convert h using 1
    · field_simp
    · rw [mul_div_cancel' _ h2]
  /-
  Original:
    rw [monotone_iff_forall_lt]
    intro a b hab
    gcongr

  LLM-aesop:
  -/
  simp_all only [ge_iff_le]
  intro a b hab
  simp_all only [gt_iff_lt]
  gcongr

/-- choose n k can be written as a product --/
lemma choose_eq {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k = (∏ j in range k, (1 - (j:ℝ)/n)) * n^k / k ! := by
  have : choose n k = (descFactorial n k : ℝ) / k ! := by
    rw [descFactorial_eq_factorial_mul_choose]
    /-
    Original:
      have hk : k ! ≠ 0 := by positivity
      field_simp [hk]
      ring

    LLM-aesop:
    -/
    simp_all only [cast_mul]
    field_simp
    rw [mul_comm]
  rw [this]
  congr
  have : n ^ k = ∏ j in range k, (n:ℝ) := by
    /-
    Original:
      rw [prod_const, card_range]
      norm_cast

    LLM-aesop
    ;-/
    simp_all only [cast_pow, prod_const, card_range]
  rw [this, <- prod_mul_distrib, descFactorial_eq_prod_range]
  rw [(show ∏ i in range k, (n-i) = ∏ i in range k, ((n - i : ℕ) : ℝ) by norm_cast)]
  apply prod_congr rfl
  intro j hj
  simp at hj
  field_simp [(show n ≠ 0 by linarith)]
  symm
  rw [sub_eq_iff_eq_add]
  /-
  Original:
    norm_cast
    rw [Nat.sub_add_cancel]
    linarith
  LLM-aesop:
  -/
  rename_i this_1
  simp_all only [cast_pow, prod_const, card_range, ge_iff_le]
  norm_cast
  rw [tsub_add_cancel_of_le]
  linarith

/-- choose n k is bounded above by n^k/k! -/
lemma choose_le {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≤ (n:ℝ)^k / k ! := by
  have h1 : (n:ℝ)^k/k ! = (∏ j in range k, (1:ℝ)) * n^k / (k !:ℝ) := by rw [prod_const_one]; norm_cast; simp
  rw [h1, choose_eq h]
  show (∏ j in range k, (1 - (j:ℝ) / n)) * (n ^ k : ℕ) / (k !:ℝ) ≤ (∏ j in range k, (1:ℝ)) * (n ^ k : ℕ) / (k !:ℝ)
  gcongr with i hi
  /-
  Original:
    . intro i hi
      simp at hi; field_simp
      rw [div_le_iff]
      . simp; linarith
      norm_cast; linarith [hi, h]
    simp at hi; field_simp; positivity

  LLM-aesop:
  -/
  intro i a
  simp_all only [prod_const_one, cast_pow, one_mul, mem_range, sub_nonneg]
  rw [div_le_iff']
  · simp_all only [mul_one, cast_le]
    linarith
  · simp_all only [cast_pos]
    linarith

/-- choose n k is bounded below by n^k/k^k -/
lemma choose_ge {n : ℕ} {k : ℕ} (h : k ≤ n) : choose n k ≥ (n:ℝ)^k / (k:ℝ)^k := by
  suffices : (k:ℝ)^k * choose n k ≥  (choose k k) * n^k
  . simp at this
    rw [ge_iff_le, div_le_iff, mul_comm]
    .
      /-
      Original:
        exact this

      LLM-aesop:
      -/
      simp_all only
    induction' k with m _
    /-
    Original:
      . simp
      positivity

    LLM-aesop:
    -/
    rename_i h_1 this_1
    simp_all only [zero_eq, _root_.zero_le, _root_.pow_zero, CharP.cast_eq_zero, choose_zero_right, cast_one, mul_one, le_refl, zero_lt_one]
    rename_i h_1 this_1 n_ih
    simp_all only [gt_iff_lt, cast_pos, cast_succ]
    positivity

  rw [choose_eq h, choose_eq (show k ≤ k by linarith)]
  field_simp
  rw [<-mul_assoc, mul_comm ((k:ℝ)^k) _]
  gcongr with i hi
  /-
  Original:
    . intro i hi
      simp at hi; field_simp
      rw [div_le_iff]
      . simp; linarith
      norm_cast; linarith [hi, h]
    simp at hi; norm_cast; linarith

  LLM-aesop:-/
  intro i a
  simp_all only [mem_range, sub_nonneg]
  rw [div_le_iff']
  · simp_all only [mul_one, cast_le]
    exact le_of_lt a
  · simp_all only [cast_pos]
    linarith
  simp_all only [mem_range, cast_pos]
  linarith


lemma choose_le' {n : ℕ} {k : ℕ} (h : k ≤ n) (h2 : 0 < k): (choose n k : ℝ)^((1:ℝ) / k) ≤ (exp 1) * n / k := by
  replace h2 : 0 < (k:ℝ) := by norm_cast
  rw [<- rpow_le_rpow_iff _ _ h2, <- rpow_mul, div_rpow, mul_rpow, (show 1/(k:ℝ) * k = 1 by field_simp), exp_one_rpow]
  . simp
    apply (le_trans (choose_le h) _)
    rw [div_le_div_iff]
    . calc
        (n:ℝ)^k * (k:ℝ)^k = (rexp k) * (n:ℝ)^k * ((k:ℝ)^k / (rexp k)) := by field_simp; ring
        _ ≤ (rexp k) * (n:ℝ)^k * k ! := by
          gcongr
          rw [<-ge_iff_le, (show (k:ℝ)^k = (k^k :ℕ) by norm_cast)]
          apply factorial_ge
    /-
    Original:
      all_goals {positivity}

    LLM-aesop:
    -/
    simp_all only [cast_pos]
    apply factorial_pos
    simp_all only [cast_pos, gt_iff_lt, pow_pos]

  /-
    Original:
      all_goals {positivity}

    LLM-aesop:
  -/
  simp_all only [cast_pos]
  positivity
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos, gt_iff_lt]
  positivity
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos, one_div]
  positivity
  simp_all only [cast_pos]
  positivity

lemma choose_ge' {n : ℕ} {k : ℕ} (h : k ≤ n) (h2 : 0 < k) : (choose n k : ℝ)^((1:ℝ) / k) ≥  n / k := by
  replace h2 : 0 < (k:ℝ) := by norm_cast
  rw [ge_iff_le, <- rpow_le_rpow_iff _ _ h2, <- rpow_mul, div_rpow, (show 1/(k:ℝ) * k = 1 by field_simp)]
  . simp
    rw [<-ge_iff_le]
    apply choose_ge
    simp_all only [cast_pos]
  /-
  Original:
    all_goals {positivity}

  LLM-aesop:
  -/
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos, cast_nonneg]
  simp_all only [cast_pos]
  positivity
  simp_all only [cast_pos, one_div]
  positivity
