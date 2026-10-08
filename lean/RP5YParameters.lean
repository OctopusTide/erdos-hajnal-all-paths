import RP5Reduction
import Mathlib.Algebra.Order.Floor.Semifield

namespace AllPathsLocal

theorem paper_tree_parameter_bounds (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hySmall : y ≤ 1 / 2^16) :
    2^16 ≤ Nat.ceil (1 / y^4) ∧
      (1 / y^4 : ℝ) ≤ Nat.ceil (1 / y^4) ∧
      (Nat.ceil (1 / y^4) : ℝ) ≤ 2 / y^4 ∧
      (Nat.ceil (1 / y^4) : ℝ) ≤ 2 / x^4 := by
  have hy : 0 < y := hx.trans_le hxy
  have h4 := pow_le_pow_left₀ hy.le hySmall 4
  have hbig : (65536 : ℝ) ≤ 1 / y^4 := by
    apply (le_div_iff₀ (show 0 < y^4 by positivity)).mpr
    norm_num at h4
    nlinarith
  have hceil := Nat.le_ceil (1 / y^4 : ℝ)
  have hceilUpper : (Nat.ceil (1 / y^4) : ℝ) ≤ 2 / y^4 := by
    have hlow : (2 : ℝ)⁻¹ ≤ 1 / y^4 := (show (2 : ℝ)⁻¹ ≤ 65536 by norm_num).trans hbig
    have h := Nat.ceil_le_two_mul hlow
    convert h using 1 <;> ring
  have hxy4 := pow_le_pow_left₀ hx.le hxy 4
  have hrec : 2 / y^4 ≤ 2 / x^4 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hxy4
  refine ⟨?_, hceil, hceilUpper, hceilUpper.trans hrec⟩
  have h := hbig.trans hceil
  norm_num at h ⊢
  exact_mod_cast h

theorem clean_node_y_size (y t N : ℝ) (hy : 0 < y) (hySmall : y ≤ 1 / 2^16)
    (ht : 0 < t) (hN : 0 ≤ N) (htUpper : t ≤ 2 / y^4) :
    y^26 * N ≤ N / t^6 := by
  have ht6 := pow_le_pow_left₀ ht.le htUpper 6
  have he : (2 / y^4)^6 = 64 / y^24 := by field_simp <;> ring
  rw [he] at ht6
  have hy8 : y ≤ 1 / 8 := hySmall.trans (by norm_num)
  have hconstant : 64 * y^2 ≤ 1 := by nlinarith
  apply (le_div_iff₀ (show 0 < t^6 by positivity)).mpr
  have hprod := mul_le_mul_of_nonneg_left ht6 (show 0 ≤ y^26 * N by positivity)
  have heprod : (y^26 * N) * (64 / y^24) = (64 * y^2) * N := by field_simp <;> ring
  rw [heprod] at hprod
  exact hprod.trans (by simpa using mul_le_mul_of_nonneg_right hconstant hN)

theorem paper_output_length_lower (y K : ℝ) (hy : 0 < y) (hK0 : 0 ≤ K)
    (hpow : 1 / y^4 ≤ K^4) : 1 / y ≤ K := by
  by_contra! hK
  have hmul : K * y < 1 := (lt_div_iff₀ hy).mp hK
  have hnon : 0 ≤ K * y := mul_nonneg hK0 hy.le
  have h2 : (K * y)^2 < 1 := by nlinarith
  have h4 : (K * y)^4 < 1 := by nlinarith [sq_nonneg (K * y)]
  have hh := (div_le_iff₀ (show 0 < y^4 by positivity)).mp hpow
  nlinarith [show (K * y)^4 = K^4 * y^4 by ring]

#print axioms paper_tree_parameter_bounds
#print axioms clean_node_y_size
#print axioms paper_output_length_lower

end AllPathsLocal
