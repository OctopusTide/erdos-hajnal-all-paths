import RP5FrontierPipeline

namespace AllPathsLocal

/-- Scalar side conditions for III.4 at the exact first-Tooth parameter
    xi_0=tau/(64m^5). The much larger degree bound supplies the second-Tooth size. -/
theorem frontier_paper_scalar_bounds (m r τ : ℝ)
    (hm : 65536 ≤ m) (hr0 : 0 ≤ r) (hr : r ≤ m) (hτ0 : 0 < τ) (hτ : τ ≤ 1) :
    let x := τ / (64 * m ^ 5)
    0 < x ∧ x ≤ 1 / 2 ^ 20 ∧ m ≤ 2 / Real.sqrt x ∧
      x / 4 ≤ τ / (256 * m ^ 5) ∧
      2 * (2 * m ^ 2 * (x / 4)) ≤ 1 ∧
      r * (2 * m ^ 2 * (x / 4)) ≤ τ ∧
      16 * m ^ 7 ≤ 16 / x ^ 3 := by
  dsimp only
  let x := τ / (64 * m ^ 5)
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hp25 : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by decide)
  have hp35 : m ^ 3 ≤ m ^ 5 := pow_le_pow_right₀ hm1 (by decide)
  have hx2 : x ≤ 1 / m ^ 2 := by
    have hd : m ^ 2 ≤ 64 * m ^ 5 := by nlinarith [show 0 ≤ m ^ 5 by positivity]
    exact (div_le_div_of_nonneg_right hτ (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hd)
  have hx3 : x ≤ 1 / m ^ 3 := by
    have hd : m ^ 3 ≤ 64 * m ^ 5 := by nlinarith [show 0 ≤ m ^ 5 by positivity]
    exact (div_le_div_of_nonneg_right hτ (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) hd)
  have hx20 : x ≤ 1 / 2 ^ 20 := by
    apply hx2.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    norm_num
    nlinarith
  have hsqrt : Real.sqrt x ≤ 1 / m := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    convert hx2 using 1 <;> ring
  have hk : m ≤ 2 / Real.sqrt x := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
    have hh := mul_le_mul_of_nonneg_left hsqrt hm0.le
    have heq : m * (1 / m) = 1 := by field_simp
    rw [heq] at hh
    linarith
  have hxτ : x / 4 = τ / (256 * m ^ 5) := by dsimp [x]; ring
  have heqβ : 2 * (2 * m ^ 2 * (x / 4)) = τ / (64 * m ^ 3) := by
    dsimp [x]
    field_simp
    ring
  have hβ : 2 * (2 * m ^ 2 * (x / 4)) ≤ 1 := by
    rw [heqβ]
    apply (div_le_iff₀ (by positivity : 0 < 64 * m ^ 3)).mpr
    have hp : (1 : ℝ) ≤ m ^ 3 := one_le_pow₀ hm1
    nlinarith
  have hp13 : m ≤ m ^ 3 := by
    simpa using (pow_le_pow_right₀ hm1 (by decide : 1 ≤ 3))
  have heqprecision : r * (2 * m ^ 2 * (x / 4)) = r * τ / (128 * m ^ 3) := by
    dsimp [x]
    field_simp
    ring
  have hprecision : r * (2 * m ^ 2 * (x / 4)) ≤ τ := by
    rw [heqprecision]
    apply (div_le_iff₀ (by positivity : 0 < 128 * m ^ 3)).mpr
    have hc : r ≤ 128 * m ^ 3 := by nlinarith [show 0 ≤ m ^ 3 by positivity]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc hτ0.le
  have hprod : x * m ^ 3 ≤ 1 := (le_div_iff₀ (by positivity : 0 < m ^ 3)).mp hx3
  have hcubed : x ^ 3 * m ^ 9 ≤ 1 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ x * m ^ 3) hprod 3
    convert hh using 1 <;> ring
  have hp79 : m ^ 7 ≤ m ^ 9 := pow_le_pow_right₀ hm1 (by decide)
  have hsize : 16 * m ^ 7 ≤ 16 / x ^ 3 := by
    apply (le_div_iff₀ (by positivity : 0 < x ^ 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hp79 (show 0 ≤ x ^ 3 by positivity)
    nlinarith
  exact ⟨hx0, hx20, hk, hxτ.le, hβ, hprecision, hsize⟩

#print axioms frontier_paper_scalar_bounds

end AllPathsLocal
