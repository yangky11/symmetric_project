import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Init.Data.Nat.Basic
import SymmetricProject.attainable

/- hack to avoid the real powers bug -/
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

/- The purpose of this file is to prove the Newton identity

$$ s_{n,k}(x) s_{n,k+2}(x) ≤ s_{n,k+1}(x)^2.$$

This turns out to be straightforward with the tools from the attainable file.
-/

theorem newton_identity (n k : ℕ) (h: k+2 ≤ n) : ∀ s : ℕ → ℝ, attainable n s → s k * s (k+2) ≤ s (k+1)^2 := by
  intro s ha

  -- first step: reduce to (n,k) = (k+2,k)

  have h1 : attainable (k+2) s := attainable_truncate n (k+2) s h ha
  clear ha h n
  -- second step: reduce to (n,k) = (k+2,0)

  suffices : ∀ s : ℕ → ℝ, attainable (k+2) s → s 0 * s 2 ≤ s 1^2
  . rcases em (s (k+2) = 0) with vanish | non_vanish
    . /-
      Original:
        rw [vanish]
        simp
        nlinarith

      LLM-aesop:
      -/
      simp_all only [mul_zero, ge_iff_le]
      apply sq_nonneg
    let s' := fun (m:ℕ) => s (k+2-m) / s (k+2)
    have h2 : attainable (k+2) s' := by
      apply attainable_reflect (k+2) s h1 non_vanish
    have h3 := this s' h2
    have hs': ∀ m : ℕ, s' m = s (k+2-m) / s (k+2) := by
      /-
      Original:
        intro m
        rfl
      LLM-aesop:
      -/
      intro m
      simp_all only [ge_iff_le, nonpos_iff_eq_zero, add_eq_zero, and_false, tsub_zero, ne_eq, not_false_eq_true,
        div_self, add_le_iff_nonpos_left, add_tsub_cancel_right, one_mul, Nat.succ_sub_succ_eq_sub, div_pow]
    rw [hs' 0, hs' 1, hs' 2] at h3
    -- thanks to Heather Macbeth for simplifications to the field calculations below.
    field_simp at h3
    calc s k * s (k + 2) = (s k / s (k + 2)) * s (k + 2) ^ 2 := by
          field_simp
          ring
      _ ≤ (s (k + 1) ^ 2 / s (k + 2) ^ 2) * s (k + 2) ^ 2 := by gcongr
      _ = s (k + 1) ^ 2 := by field_simp

  -- third step: reduce to (n,k)=(2,0)
  clear s h1
  suffices : ∀ s : ℕ → ℝ, attainable 2 s → s 0 * s 2 ≤ s 1^2
  . intro s ha
    have h1 : attainable 2 s := attainable_truncate (k+2) 2 s (show 2 ≤ k+2 by linarith) ha
    /-
    Original:
      clear ha
      exact this s h1

    LLM-aesop:
    -/
    simp_all only

  intro s ha
  simp [attainable] at ha
  rcases ha with ⟨ x, hx ⟩
  have h0 := hx 0 (show 0 ≤ 2 by norm_num)
  have h1 := hx 1 (show 1 ≤ 2 by norm_num)
  have h2 := hx 2 (show 2 ≤ 2 by norm_num)
  rw [esymm_zero_eq_one] at h0
  rw [esymm_sum] at h1
  rw [esymm_prod] at h2
  simp at h0
  simp at h1
  simp at h2
  have r : Finset.range 2 = {0,1} := by
    /-
    Original:
      rfl

    LLM-aesop:
    -/
    simp_all only
  rw [r, Finset.sum_pair] at h1
  rw [r, Finset.prod_pair] at h2
  rw [<- h0, <- h2]
  have h1' : s 1 = (x 0 + x 1)/2 := by
    field_simp [h1]
    /-
    Original:
      left
      norm_num
    LLM-aesop:
    -/
    simp_all only
    apply Or.inl
    linarith
  rw [h1']
  clear k hx h0 h1 h2 r h1'
  field_simp
  rw [<- sub_nonneg]
  field_simp
  have h : (2:ℝ) ^ 2 = 4 := by
    /-
    Original:
      norm_num

    LLM-aesop:
    -/
    norm_num
  rw [h]
  have h' : (x 0 + x 1) ^ 2 - 4 * (x 0 * x 1) = (x 0 - x 1) * (x 0 - x 1) := by
    /-
    Original:
      ring

    LLM-aesop:
    -/
    ring

  /-
  Original:
    rw [h']
    nlinarith
    norm_num
    norm_num

  LLM-aesop:
  -/
  simp_all only [ge_iff_le]
  nlinarith
  simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.prod_insert, Finset.prod_singleton]
  simp_all only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Finset.prod_insert, Finset.prod_singleton]
