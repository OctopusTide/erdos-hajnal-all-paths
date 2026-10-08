import RP5ThinLogError
import Mathlib.Algebra.Order.Floor.Semifield

namespace AllPathsLocal

theorem thin_parameter_log_bounds (epsilon : ℝ) (q : ℕ) (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/65536)
    (hqLower : 1/epsilon^2 ≤ (q : ℝ)) (hqUpper : (q : ℝ) ≤ 2/epsilon^2) :
    1 ≤ Real.log (1/epsilon) ∧ Real.log (256*(q : ℝ)) ≤ 3*Real.log (1/epsilon) ∧
      Real.log (128*(q : ℝ)) ≤ 3*Real.log (1/epsilon) := by
  have hq0 : (0 : ℝ) < q := (by positivity : (0 : ℝ) < 1/epsilon^2).trans_le hqLower
  have hx : (65536 : ℝ) ≤ 1/epsilon := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  have hL : 1 ≤ Real.log (1/epsilon) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (Real.exp_one_lt_three.le.trans (by linarith))
  have hp := (le_div_iff₀ (show 0 < epsilon^2 by positivity)).mp hqUpper
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 256*epsilon by positivity)
  have hden : 256*(q : ℝ) ≤ (1/epsilon)^3 := by
    rw [one_div_pow]
    apply (le_div_iff₀ (show 0 < epsilon^3 by positivity)).mpr
    nlinarith
  have h256 := Real.log_le_log (show 0 < 256*(q : ℝ) by positivity) hden
  rw [Real.log_pow] at h256
  norm_num at h256
  have h256' : Real.log (256*(q : ℝ)) ≤ 3*Real.log (1/epsilon) := by
    simpa [one_div, Real.log_inv] using h256
  have h128 := Real.log_le_log (show 0 < 128*(q : ℝ) by positivity)
    (show 128*(q : ℝ) ≤ 256*(q : ℝ) by nlinarith)
  exact ⟨hL, h256', h128.trans h256'⟩

/-- Integer r and its logarithmic error are controlled at the paper's small
    epsilon, for every q in the actual ceil(epsilon^-2) bounds. -/
theorem thin_parameter_record_error (epsilon : ℝ) (q : ℕ) (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/65536)
    (hqLower : 1/epsilon^2 ≤ (q : ℝ)) (hqUpper : (q : ℝ) ≤ 2/epsilon^2) :
    let r := Nat.ceil (Real.log (256*(q : ℝ))/epsilon)
    (r : ℝ)/(q : ℝ) * Real.log (128*(q : ℝ)) < 1 ∧ r < q := by
  let L := Real.log (1/epsilon)
  obtain ⟨hL, h256, h128⟩ := thin_parameter_log_bounds epsilon q he heSmall hqLower hqUpper
  have hq0 : (0 : ℝ) < q := (by positivity : (0 : ℝ) < 1/epsilon^2).trans_le hqLower
  have hqNat : 1 ≤ q := by exact_mod_cast (show (0 : ℝ) < q from hq0)
  have hlog0 : 0 ≤ Real.log (256*(q : ℝ)) := Real.log_nonneg (by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
    nlinarith)
  let r := Nat.ceil (Real.log (256*(q : ℝ))/epsilon)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr : (r : ℝ) ≤ 3*L/epsilon + 1 := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ Real.log (256*(q : ℝ))/epsilon by positivity)).le
    have hd := div_le_div_of_nonneg_right h256 he.le
    exact hh.trans (by dsimp [L]; linarith only [hd])
  have hmul := mul_le_mul_of_nonneg_right hr (show 0 ≤ epsilon^2 by positivity)
  have hBudget : (r : ℝ)*epsilon^2 ≤ 3*epsilon*L + epsilon^2 := by
    have hid : (3*L/epsilon+1)*epsilon^2 = 3*epsilon*L+epsilon^2 := by field_simp <;> ring
    rwa [hid] at hmul
  have hqprod := (div_le_iff₀ (show 0 < epsilon^2 by positivity)).mp hqLower
  have hmul2 := mul_le_mul_of_nonneg_left hqprod hr0
  have hmul3 := mul_le_mul_of_nonneg_left hBudget hq0.le
  have hRatio : (r : ℝ)/(q : ℝ) ≤ 3*epsilon*L+epsilon^2 := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith only [hmul2, hmul3]
  have hRatio0 : 0 ≤ (r : ℝ)/(q : ℝ) := div_nonneg hr0 hq0.le
  have hB0 : 0 ≤ 3*epsilon*L+epsilon^2 := by dsimp [L]; positivity
  have hError := thin_layer_log_error_bound epsilon he heSmall
  change 9*epsilon*L^2+3*epsilon^2*L < 1 at hError
  have hProduct : (r : ℝ)/(q : ℝ) * Real.log (128*(q : ℝ)) < 1 := by
    have hm1 := mul_le_mul_of_nonneg_left h128 hRatio0
    have hm2 := mul_le_mul_of_nonneg_right hRatio (show 0 ≤ 3*L by linarith)
    nlinarith only [hm1, hm2, hError]
  have hB : 3*epsilon*L+epsilon^2 < 1 := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ 3*L by linarith) hB0
    nlinarith only [hh, hError]
  have hrq : r < q := by
    have hh := (div_lt_iff₀ hq0).mp (hRatio.trans_lt hB)
    have hhR : (r : ℝ) < (q : ℝ) := by simpa only [one_mul] using hh
    exact_mod_cast hhR
  exact ⟨hProduct, hrq⟩

#print axioms thin_parameter_log_bounds
#print axioms thin_parameter_record_error
end AllPathsLocal
