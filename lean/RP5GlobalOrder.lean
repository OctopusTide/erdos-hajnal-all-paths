import RP5SeparatedQuantitative

namespace AllPathsLocal

theorem global_order_suffices (x m N : ℝ) (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16)
    (hm : 1 ≤ m) (hmupper : m ≤ 1 / x^27) (hN : 1 / x^600 ≤ N) :
    16 / (x / (64 * m^5))^3 ≤ N / m^6 := by
  have hm0 : 0 < m := by linarith
  have hxhalf : x ≤ 1 / 2 := hxsmall.trans (by norm_num)
  have hx30 := pow_le_pow_left₀ hx.le hxhalf 30
  have hconstant : (2 : ℝ)^22 * x^30 ≤ 1 := by norm_num at hx30; nlinarith
  have hm21 := pow_le_pow_left₀ hm0.le hmupper 21
  have he21 : (1 / x^27)^21 = 1 / x^567 := by field_simp <;> ring
  rw [he21] at hm21
  have hratio : (2 : ℝ)^22 / x^567 ≤ 1 / x^597 := by
    apply (div_le_div_iff₀ (by positivity : 0 < x^567) (by positivity : 0 < x^597)).mpr
    have h := mul_le_mul_of_nonneg_left hconstant (show 0 ≤ x^567 by positivity)
    nlinarith [show x^567 * x^30 = x^597 by ring]
  have hmbound : (2 : ℝ)^22 * m^21 ≤ 1 / x^597 :=
    (mul_le_mul_of_nonneg_left hm21 (by positivity)).trans (by simpa only [mul_one_div] using hratio)
  have hNmul := mul_le_mul_of_nonneg_right hN (show 0 ≤ x^3 by positivity)
  have heN : (1 / x^600) * x^3 = 1 / x^597 := by field_simp <;> ring
  rw [heN] at hNmul
  have hmass := hmbound.trans hNmul
  have he : 16 / (x / (64 * m^5))^3 = (2 : ℝ)^22 * m^15 / x^3 := by field_simp <;> ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < x^3) (by positivity : 0 < m^6)).mpr
  convert hmass using 1 <;> ring

theorem global_output_length_upper (x m K : ℝ) (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16)
    (hm : 0 ≤ m) (hmupper : m ≤ 1 / x^27) (hK : K ≤ 64 * m^5 / x) :
    K ≤ 1 / x^140 := by
  have hm5 := pow_le_pow_left₀ hm hmupper 5
  have he5 : (1 / x^27)^5 = 1 / x^135 := by field_simp <;> ring
  rw [he5] at hm5
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm5 (by norm_num : (0 : ℝ) ≤ 64)) hx.le
  have he : 64 * (1 / x^135) / x = 64 / x^136 := by field_simp <;> ring
  rw [he] at h
  have hxquarter : x ≤ 1 / 4 := hxsmall.trans (by norm_num)
  have hx4 := pow_le_pow_left₀ hx.le hxquarter 4
  have hconstant : 64 * x^4 ≤ 1 := by norm_num at hx4; nlinarith
  have hratio : 64 / x^136 ≤ 1 / x^140 := by
    apply (div_le_div_iff₀ (by positivity : 0 < x^136) (by positivity : 0 < x^140)).mpr
    have hh := mul_le_mul_of_nonneg_left hconstant (show 0 ≤ x^136 by positivity)
    nlinarith [show x^136 * x^4 = x^140 by ring]
  exact hK.trans (h.trans hratio)

#print axioms global_order_suffices
#print axioms global_output_length_upper

end AllPathsLocal
