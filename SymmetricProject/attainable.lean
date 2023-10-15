import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import SymmetricProject.esymm_basic
import SymmetricProject.esymm_generating

-- this file sets up the concept of an attainable sequence - a tuple of real numbers that can be attained as elementary symmetric means.  It also establishes [Lemma 2.1 of the paper], which is a key tool in what follows.

open Finset
open BigOperators
open Polynomial
open Nat

/-- attainable n s holds if there exists a sequence of real numbers x such that 
$$ S_k(x) = s_k \binom{n}{k}$$
for all $0 \leq k \leq n$. 
-/
def attainable (n : ℕ) (s : ℕ → ℝ) : Prop := ∃ (x : ℕ → ℝ), ∀ k : ℕ, k ≤ n → esymm n k x = (s k) * (choose n k)

/-- Any attainable sequence starts at one. -/
lemma attainable_zero_eq_one (n : ℕ) (s : ℕ → ℝ) : attainable n s → s 0 = 1 := by
  intro h
  rcases h with ⟨ x, hx ⟩
  have h0: 0 ≤ n := by linarith
  have esymm0 := hx 0 h0
  simp [esymm_zero_eq_one] at esymm0
  symm
  assumption

/-- An attainable sequence can be scaled. [Lemma 2.1(i) in the paper]-/
lemma attainable_scaling (n : ℕ) (s : ℕ → ℝ) (a : ℝ) : attainable n s → attainable n (fun k => (a ^ k) * (s k) ) := by
  intro h
  rcases h with ⟨ x, hx ⟩
  use fun k => a * (x k)
  intro k hk
  simp
  rw [esymm_mul]
  simp [hx k hk]
  ring
  
/-- An attainable sequence can be reflected if its final entry is non-zero. [Lemma 2.1(ii) in the paper]-/
lemma attainable_reflect (n : ℕ) (s : ℕ → ℝ) : attainable n s → s n ≠ 0 → attainable n (fun k => s (n - k) / (s n)) := by
  intro h hn
  rcases h with ⟨ x, hx ⟩
  use fun k => 1 / (x k)
  intro k hk
  rw [esymm_reflect]
  have hnk : n-k ≤ n := by apply sub_le
  have hnn : n ≤ n := by linarith
  rw [hx (n-k) hnk, hx n hnn] 
  simp [choose_symm hk]
  ring
  . contrapose! hn
    have hnn : n ≤ n := by linarith
    rw [hx n hnn] at hn
    simp at hn
    assumption
  assumption

    

