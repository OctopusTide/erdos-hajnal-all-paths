import RP5FactorialBound

namespace AllPathsLocal

/-- Convert the actual integer binomial container count into the rational
    power bound used in the final contradiction. -/
theorem container_binomial_power_upper (M u q r : ℕ) (hq : 1 ≤ q) (hrq : r ≤ q)
    (hu : (u : ℝ) ≤ (M : ℝ)/(128*(q : ℝ))) :
    (M.choose r : ℝ) * (u.choose (q-r) : ℝ) ≤
      (M : ℝ)^q / (128*(q : ℝ))^(q-r) * (6/(q : ℝ))^q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrF : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have haF : (0 : ℝ) < (q-r).factorial := by exact_mod_cast Nat.factorial_pos (q-r)
  have hden : (0 : ℝ) < ((q : ℝ)/6)^q := by positivity
  have hF := split_factorial_sixth_lower q r hrq
  have h1 : (M.choose r : ℝ) ≤ (M : ℝ)^r / (r.factorial : ℝ) := by
    simpa only [Nat.cast_pow] using (Nat.choose_le_pow_div (α := ℝ) r M)
  have h2 : (u.choose (q-r) : ℝ) ≤ (u : ℝ)^(q-r) / ((q-r).factorial : ℝ) := by
    simpa only [Nat.cast_pow] using (Nat.choose_le_pow_div (α := ℝ) (q-r) u)
  have hm := mul_le_mul h1 h2 (Nat.cast_nonneg _) (show 0 ≤ (M : ℝ)^r / (r.factorial : ℝ) by positivity)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg u) hu (q-r)
  have hn := mul_le_mul_of_nonneg_left hp (show 0 ≤ (M : ℝ)^r by positivity)
  have hd := div_le_div_of_nonneg_left
    (show 0 ≤ (M : ℝ)^r * ((M : ℝ)/(128*(q : ℝ)))^(q-r) by positivity) hden hF
  have hpowM : (M : ℝ)^r * (M : ℝ)^(q-r) = (M : ℝ)^q := by
    rw [← pow_add, Nat.add_sub_of_le hrq]
  calc
    _ ≤ (M : ℝ)^r / (r.factorial : ℝ) * ((u : ℝ)^(q-r) / ((q-r).factorial : ℝ)) := hm
    _ = (M : ℝ)^r * (u : ℝ)^(q-r) / ((r.factorial : ℝ)*((q-r).factorial : ℝ)) := by ring
    _ ≤ (M : ℝ)^r * ((M : ℝ)/(128*(q : ℝ)))^(q-r) /
        ((r.factorial : ℝ)*((q-r).factorial : ℝ)) :=
      div_le_div_of_nonneg_right hn (mul_pos hrF haF).le
    _ ≤ (M : ℝ)^r * ((M : ℝ)/(128*(q : ℝ)))^(q-r) / ((q : ℝ)/6)^q := hd
    _ = _ := by
      rw [div_pow]
      simp only [← mul_div_assoc]
      rw [hpowM]
      have hi : ((q : ℝ)/6)⁻¹ = 6/(q : ℝ) := by field_simp
      rw [div_eq_mul_inv ((M : ℝ)^q / (128*(q : ℝ))^(q-r)) (((q : ℝ)/6)^q),
        ← inv_pow, hi]

#print axioms container_binomial_power_upper
end AllPathsLocal
