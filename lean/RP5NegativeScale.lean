import RP5NegativeWeakChordal

namespace AllPathsLocal

theorem negative_layer_fraction_bound (N M t : ℝ) (hN : 0 ≤ N) (hM0 : 0 < M)
    (ht : 0 < t) (hM : 3 * N / (8 * t) ≤ M) :
    (N / t^6) / M ≤ 8 / (3 * t^5) := by
  have h := (div_le_iff₀ (show 0 < 8 * t by positivity)).mp hM
  apply (div_le_div_iff₀ hM0 (show 0 < 3 * t^5 by positivity)).mpr
  have he : (N / t^6) * (3 * t^5) = 3 * N / t := by field_simp <;> ring
  rw [he]
  apply (div_le_iff₀ ht).mpr
  nlinarith

theorem negative_fraction_y_bound (y t : ℝ) (hy : 0 < y) (hysmall : y ≤ 1 / 2^16)
    (ht : 1 / y^4 ≤ t) : 8 / (3 * t^5) ≤ y^16 / 128 := by
  have ht0 : 0 < t := (show 0 < 1 / y^4 by positivity).trans_le ht
  have ht5 := pow_le_pow_left₀ (show 0 ≤ 1 / y^4 by positivity) ht 5
  have he : (1 / y^4)^5 = 1 / y^20 := by field_simp <;> ring
  rw [he] at ht5
  have hrec : 1 / t^5 ≤ y^20 := by
    apply (div_le_iff₀ (show 0 < t^5 by positivity)).mpr
    have h := (div_le_iff₀ (show 0 < y^20 by positivity)).mp ht5
    nlinarith
  have hfirst : 8 / (3 * t^5) ≤ (8 / 3) * y^20 := by
    have h := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 8 / 3)
    convert h using 1 <;> ring
  have hy16 : y ≤ 1 / 16 := hysmall.trans (by norm_num)
  have hy4 := pow_le_pow_left₀ hy.le hy16 4
  have hc : (8 / 3) * y^4 ≤ 1 / 128 := by norm_num at hy4; nlinarith
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ y^16 by positivity)
  have hlast : (8 / 3) * y^20 ≤ y^16 / 128 := by
    convert hh using 1 <;> ring
  exact hfirst.trans hlast

theorem negative_thin_output_size (y t N M A : ℝ)
    (hy : 0 < y) (hysmall : y ≤ 1 / 2^16) (hN : 0 ≤ N) (ht : 0 < t)
    (htupper : t ≤ 2 / y^4) (hM : 3 * N / (8 * t) ≤ M)
    (hA : y^8 * M / 512 ≤ A) : y^18 * N ≤ A := by
  have hMt := (div_le_iff₀ (show 0 < 8 * t by positivity)).mp hM
  have hM0 : 0 ≤ M := (show 0 ≤ 3 * N / (8 * t) by positivity).trans hM
  have hprod := mul_le_mul_of_nonneg_left htupper (show 0 ≤ 8 * M by positivity)
  have hMlower : 3 * y^4 * N / 16 ≤ M := by
    have hm : 3 * N ≤ 16 * M / y^4 := by
      have he : 8 * M * (2 / y^4) = 16 * M / y^4 := by ring
      rw [he] at hprod
      nlinarith
    have hh := (le_div_iff₀ (show 0 < y^4 by positivity)).mp hm
    nlinarith
  have hAlower : 3 * y^12 * N / 8192 ≤ A := by
    have hh := mul_le_mul_of_nonneg_left hMlower (show 0 ≤ y^8 by positivity)
    nlinarith [show y^8 * y^4 = y^12 by ring]
  have hyhalf : y ≤ 1 / 4 := hysmall.trans (by norm_num)
  have hy6 := pow_le_pow_left₀ hy.le hyhalf 6
  have hc : y^6 ≤ 3 / 8192 := by norm_num at hy6; nlinarith
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ y^12 * N by positivity)
  have hfinal : y^18 * N ≤ 3 * y^12 * N / 8192 := by
    convert hh using 1 <;> ring
  exact hfinal.trans hAlower

#print axioms negative_layer_fraction_bound
#print axioms negative_fraction_y_bound
#print axioms negative_thin_output_size

end AllPathsLocal
