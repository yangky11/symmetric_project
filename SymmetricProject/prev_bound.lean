import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Init.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import SymmetricProject.esymm_basic
import SymmetricProject.attainable
import SymmetricProject.stirling

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the bound

|s_l|^(1/2) ≪ l^(1/2) max |s_k|^(1/k), |s_{k+1}|^(1/k+1)

established by Gopalan-Yehudayoff.
-/

open Real
open Nat
open Finset
open BigOperators

lemma square (x : ℝ) : x^2 = |x|^2 := by
  rw [<- abs_of_nonneg (show (0:ℝ) ≤ x^2 by positivity), pow_abs]

/- the preliminary bound
|s_n|^(1/n) ≤ 2n max( |s_1|, |s_2|^(1/2))
-/
lemma prelim_bound {n : ℕ} {s : ℕ → ℝ} (h1 : n > 2) (h5 : attainable n s) : |s n|^((1:ℝ)/n) ≤ ((2:ℝ) * n)^((1:ℝ)/2) * max |s 1| (|s 2|^((1:ℝ)/2))  := by
  simp
  set X := max |s 1| (|s 2|^((2:ℝ)⁻¹))
  rcases h5 with ⟨ x, hx ⟩
  calc
    |s n|^((n:ℝ)⁻¹) = (abs (∏ j in range n, x j^2)^((n:ℝ)⁻¹))^((2:ℝ)⁻¹) := by
      rw [<- rpow_mul, mul_comm, rpow_mul]
      congr
      have := hx n (by linarith)
      simp at this
      rw [<- abs_rpow_of_nonneg, <- finset_prod_rpow, <- this, abs_prod, abs_prod]
      apply prod_congr rfl
      intro i _
      rw [square, (show |x i|^(2:ℕ) = |x i|^(2:ℝ) by norm_cast), <-rpow_mul]
      simp
      . positivity
      . intro i _; positivity
      . apply prod_nonneg; intro i _; positivity
      . positivity
      . positivity
    _ ≤ (abs (∑ j in range n, x j^2) / n)^((2:ℝ)⁻¹) := by
      apply rpow_le_rpow
      . positivity
      . rw [abs_prod, abs_of_nonneg (show (0:ℝ) ≤ ∑ j in range n, x j^2 by norm_cast; apply sum_nonneg; intro i _; positivity), <- finset_prod_rpow, sum_div]
        have : ∑ j in range n, x j^2 / n = ∑ j in range n, ((n:ℝ)⁻¹)* |x j^2| := by
          congr
          ext j
          field_simp
        rw [this]
        apply geom_mean_le_arith_mean_weighted
        . intro i _; positivity
        . rw [sum_const]; simp; field_simp
        . intro i _; positivity
        . intro i _; positivity
      positivity
    _ ≤ (((esymm n 1 x)^2 + 2 * abs (esymm n 2 x))/n)^((2:ℝ)⁻¹) := by
      gcongr
      rw [newton_two]
      apply le_trans (abs_sub _ _) _
      gcongr
      . simp
      rw [abs_mul]
      simp
    _ ≤ ((2:ℝ) * n)^((2:ℝ)⁻¹) * X := by
      rw [hx 1 (by linarith), hx 2 (by linarith), <- rpow_le_rpow_iff _ _ (show 0 < 2 by norm_num), <- rpow_mul, mul_rpow, <-rpow_mul]
      simp
      rw [div_le_iff, (show (2:ℝ) * n * (X ^ 2) * n = (X * n)^2 + (n * X)^2 by ring), square (s 1 * n), abs_mul]
      simp
      gcongr
      . apply le_max_left
      . rw [mul_pow, abs_mul, mul_comm |s 2| _, <-mul_assoc]
        gcongr
        . have := choose_le (show 2 ≤ n by linarith)
          rw [(show 2! = 2 by norm_num)] at this
          simp
          field_simp at this
          linarith
        rw [<- rpow_le_rpow_iff _ _ (show 0 < (2:ℝ)⁻¹ by norm_num), (show X^(2:ℕ) = X^(2:ℝ) by norm_cast), <- rpow_mul]
        simp
        all_goals {positivity}
      all_goals {positivity}
