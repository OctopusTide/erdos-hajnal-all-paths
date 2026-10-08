import RP5LayerInterfaces
import Mathlib.Data.List.Sort

namespace AllPathsLocal

open scoped BigOperators

/-- A telescoping majorant; its looser constant suffices because t >= 65536. -/
theorem inverse_cube_telescope (j : ℝ) (hj : 1 ≤ j) :
    1 / (j + 1)^3 ≤ 1 / j^2 - 1 / (j + 1)^2 := by
  have hj0 : 0 < j := by linarith
  have hj1 : 0 < j + 1 := by linarith
  apply (mul_le_mul_iff_right₀ (show 0 < j^2 * (j + 1)^3 by positivity)).mp
  field_simp
  nlinarith [sq_nonneg j]

theorem finite_inverse_cube_tail (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (∑ i : Fin n, 1 / ((a : ℝ) + i.val + 1)^3) ≤
      1 / (a : ℝ)^2 - 1 / ((a : ℝ) + n)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hj : (1 : ℝ) ≤ (a : ℝ) + n := by exact_mod_cast (show 1 ≤ a + n by omega)
    have h := inverse_cube_telescope ((a : ℝ) + n) hj
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one, ← add_assoc]
    linarith

theorem size_tail_numeric (t : ℕ) (ht : 16 ≤ t) :
    1 / (t : ℝ)^4 + 1 / ((t : ℝ) - 1)^2 < 3 / (8 * t) := by
  have htR : (16 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by linarith
  have ht2 : (256 : ℝ) ≤ (t : ℝ)^2 := by nlinarith
  have ht3 : (4096 : ℝ) ≤ (t : ℝ)^3 := by nlinarith [mul_le_mul_of_nonneg_left ht2 ht0.le]
  apply (mul_lt_mul_iff_right₀ (show 0 < 8 * (t : ℝ)^4 * ((t : ℝ) - 1)^2 by positivity)).mp
  field_simp
  nlinarith [sq_nonneg ((t : ℝ) - 1), mul_nonneg (show 0 ≤ (t : ℝ)^3 by positivity)
    (show 0 ≤ ((t : ℝ) - 1)^2 by positivity)]

#print axioms inverse_cube_telescope
#print axioms finite_inverse_cube_tail
#print axioms size_tail_numeric

theorem inverse_cube_tail_range (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / ((a : ℝ) + i + 1)^3) ≤
      1 / (a : ℝ)^2 - 1 / ((a : ℝ) + n)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hj : (1 : ℝ) ≤ (a : ℝ) + n := by exact_mod_cast (show 1 ≤ a + n by omega)
    have h := inverse_cube_telescope ((a : ℝ) + n) hj
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    linarith

#print axioms inverse_cube_tail_range

end AllPathsLocal
