import RP5BinomialRatio
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds

namespace AllPathsLocal

/-- A rigorous coarse bound suffices for the paper's logarithmic error.
    No numerical sampling of epsilon or floating-point arithmetic is used. -/
theorem large_inverse_log_error_bound (x : ℝ) (hx : 65536 ≤ x) :
    9 * (Real.log x)^2 / x + 3 * Real.log x / x^2 < 1 := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have he1 := Real.exp_one_lt_three
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 2 ≤ 65536 := by
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  have hL : Real.log 65536 ≤ 16 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hpow := Real.log_pow (2 : ℝ) 16
    norm_num at hpow
    nlinarith
  have hs : Real.sqrt 65536 = 256 := by norm_num
  have hmono := Real.log_div_sqrt_antitoneOn he2 (he2.trans hx) hx
  dsimp only at hmono
  rw [hs] at hmono
  have hratio : Real.log x / Real.sqrt x ≤ 1/16 := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hupper : Real.log x ≤ Real.sqrt x / 16 := by
    have hh := (div_le_iff₀ hs0).mp hratio
    linarith
  have hsq := pow_le_pow_left₀ hlog0 hupper 2
  have hxSq := Real.sq_sqrt hx0.le
  have hfirst : (Real.log x)^2 / x ≤ 1/256 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith
  have heOne : Real.exp 1 ≤ 65536 := by linarith
  have hmono1 := Real.log_div_self_antitoneOn heOne (heOne.trans hx) hx
  dsimp only at hmono1
  have hloglinear : Real.log x ≤ x / 4096 := by
    have hh : Real.log x / x ≤ 1/4096 := by linarith
    have ht := (div_le_iff₀ hx0).mp hh
    linarith
  have hsecond : Real.log x / x^2 ≤ 1 / (4096 * 65536) := by
    apply (div_le_iff₀ (show 0 < x^2 by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hx hx0.le
    nlinarith
  calc
    _ = 9 * ((Real.log x)^2 / x) + 3 * (Real.log x / x^2) := by ring
    _ ≤ 9 * (1/256) + 3 * (1/(4096*65536)) := by linarith only [hfirst, hsecond]
    _ < 1 := by norm_num

theorem thin_layer_log_error_bound (epsilon : ℝ) (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/65536) :
    9 * epsilon * (Real.log (1/epsilon))^2 +
      3 * epsilon^2 * Real.log (1/epsilon) < 1 := by
  have hx : (65536 : ℝ) ≤ 1/epsilon := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  have h := large_inverse_log_error_bound (1/epsilon) hx
  have heq : 9 * (Real.log (1/epsilon))^2 / (1/epsilon) +
      3 * Real.log (1/epsilon) / (1/epsilon)^2 =
      9 * epsilon * (Real.log (1/epsilon))^2 +
      3 * epsilon^2 * Real.log (1/epsilon) := by
    field_simp
    <;> ring
  rw [heq] at h
  exact h

#print axioms large_inverse_log_error_bound
#print axioms thin_layer_log_error_bound
end AllPathsLocal
