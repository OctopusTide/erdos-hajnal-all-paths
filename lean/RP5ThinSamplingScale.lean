import RP5NegativeScale

namespace AllPathsLocal

theorem thin_layer_sampling_scale (ε q lam : ℝ) (hε : 0 < ε) (hq : 0 < q)
    (hqUpper : q ≤ 2 / ε^2) (hlam0 : 0 ≤ lam) (hlam : lam ≤ ε^4 / 128) :
    32 * q^2 * lam ≤ 1 ∧ ε^2 / 512 ≤ 1 / (256 * q) := by
  have hq2 := pow_le_pow_left₀ hq.le hqUpper 2
  have hprod1 := mul_le_mul_of_nonneg_left hlam (show 0 ≤ 32 * q^2 by positivity)
  have hprod2 := mul_le_mul_of_nonneg_right hq2 (show 0 ≤ ε^4 / 4 by positivity)
  have he : (2 / ε^2)^2 * (ε^4 / 4) = 1 := by field_simp <;> ring
  constructor
  · rw [he] at hprod2
    nlinarith
  · apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 512) (by positivity : 0 < 256 * q)).mpr
    have hqmul := (le_div_iff₀ (show 0 < ε^2 by positivity)).mp hqUpper
    nlinarith

theorem thin_sampling_collision_scale (q lam : ℝ) (hq : 0 < q)
    (hlam : 32 * q^2 * lam ≤ 1) : 2 * (q^2)^2 * lam ≤ q^2 / 16 := by
  have h := mul_le_mul_of_nonneg_left hlam (show 0 ≤ q^2 by positivity)
  nlinarith

theorem thin_layer_required_order (q lam M : ℝ) (hq : 0 < q) (hlam : 0 < lam)
    (hthin : 32 * q^2 * lam ≤ 1) (hM : 1 / lam ≤ M) :
    32 * q^2 ≤ M ∧ 2 * q^2 ≤ M := by
  have hfirst : 32 * q^2 ≤ 1 / lam := (le_div_iff₀ hlam).mpr (by simpa only [mul_comm] using hthin)
  exact ⟨hfirst.trans hM, by nlinarith⟩

#print axioms thin_layer_sampling_scale
#print axioms thin_sampling_collision_scale
#print axioms thin_layer_required_order

end AllPathsLocal
