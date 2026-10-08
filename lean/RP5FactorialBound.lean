import RP5ThinParameterLogs
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds

namespace AllPathsLocal

/-- A weaker rational version of Stirling is enough for the thin-layer
    contradiction; exp(1) < 3 is an existing proved Mathlib theorem. -/
theorem factorial_third_lower (q : ℕ) : ((q : ℝ)/3)^q ≤ (q.factorial : ℝ) := by
  by_cases hq : q = 0
  · subst q
    norm_num
  · have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hpi := Real.two_le_pi
    have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi*(q : ℝ) by positivity)
    have hs0 := Real.sqrt_nonneg (2*Real.pi*(q : ℝ))
    have hm := mul_le_mul_of_nonneg_left hqR (show 0 ≤ 2*Real.pi by positivity)
    have hs : 1 ≤ Real.sqrt (2*Real.pi*(q : ℝ)) := by nlinarith
    have hd : (q : ℝ)/3 ≤ (q : ℝ)/Real.exp 1 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.exp_pos _) Real.exp_one_lt_three.le
    have hp := pow_le_pow_left₀ (show 0 ≤ (q : ℝ)/3 by positivity) hd q
    have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ ((q : ℝ)/Real.exp 1)^q by positivity)
    have hh' : ((q : ℝ)/Real.exp 1)^q ≤ Real.sqrt (2*Real.pi*(q : ℝ)) *
        ((q : ℝ)/Real.exp 1)^q := by simpa only [one_mul] using hh
    exact hp.trans (hh'.trans (Stirling.le_factorial_stirling q))

theorem split_factorial_sixth_lower (q r : ℕ) (hrq : r ≤ q) :
    ((q : ℝ)/6)^q ≤ (r.factorial : ℝ) * ((q-r).factorial : ℝ) := by
  have hi : (q.choose r : ℝ) * (r.factorial : ℝ) * ((q-r).factorial : ℝ) =
      (q.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hrq
  have hc : (q.choose r : ℝ) ≤ (2 : ℝ)^q := by
    exact_mod_cast Nat.choose_le_two_pow q r
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (r.factorial : ℝ)*((q-r).factorial : ℝ) by positivity)
  have hbound := factorial_third_lower q
  have heq : ((q : ℝ)/3)^q = (2 : ℝ)^q * ((q : ℝ)/6)^q := by
    rw [← mul_pow]
    congr 1
    ring
  rw [heq] at hbound
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < 2^q by positivity)).mp
  nlinarith only [hbound, hi, hm]

#print axioms factorial_third_lower
#print axioms split_factorial_sixth_lower
end AllPathsLocal
