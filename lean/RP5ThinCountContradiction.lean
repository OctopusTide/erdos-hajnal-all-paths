import RP5ThinScalarContradiction

namespace AllPathsLocal

theorem thin_counts_inconsistent (M u q r H : ℕ) (hM : 1 ≤ M) (hq : 2 ≤ q) (hrq : r ≤ q)
    (hu : (u : ℝ) ≤ (M : ℝ)/(128*(q : ℝ)))
    (herror : (r : ℝ)/(q : ℝ)*Real.log (128*(q : ℝ)) < 1)
    (hLower : (M : ℝ)^q ≤ 2*(H : ℝ)*(2*(q : ℝ)^2)^q)
    (hUpper : H ≤ 2*(M.choose r*u.choose (q-r))) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hU : (H : ℝ) ≤ 2*((M.choose r : ℝ)*(u.choose (q-r) : ℝ)) := by exact_mod_cast hUpper
  have hmH := mul_le_mul_of_nonneg_right hU (show 0 ≤ 2*(2*(q : ℝ)^2)^q by positivity)
  have hmiddle : (M : ℝ)^q ≤ 4*((M.choose r : ℝ)*(u.choose (q-r) : ℝ))*(2*(q : ℝ)^2)^q := by
    nlinarith only [hmH, hLower]
  have hC := container_binomial_power_upper M u q r (by omega) hrq hu
  have hm := mul_le_mul_of_nonneg_right hC (show 0 ≤ 4*(2*(q : ℝ)^2)^q by positivity)
  have hp : (6/(q : ℝ))^q*(2*(q : ℝ)^2)^q = (12*(q : ℝ))^q := by
    rw [← mul_pow]
    congr 1
    field_simp
    <;> ring
  have heq : 4*((M : ℝ)^q/(128*(q : ℝ))^(q-r)*(6/(q : ℝ))^q)*(2*(q : ℝ)^2)^q =
      (M : ℝ)^q*(4*(12*(q : ℝ))^q/(128*(q : ℝ))^(q-r)) := by
    calc
      _ = (M : ℝ)^q*(4*((6/(q : ℝ))^q*(2*(q : ℝ)^2)^q)/(128*(q : ℝ))^(q-r)) := by ring
      _ = _ := by rw [hp]
  have hm' : 4*((M.choose r : ℝ)*(u.choose (q-r) : ℝ))*(2*(q : ℝ)^2)^q ≤
      (M : ℝ)^q*(4*(12*(q : ℝ))^q/(128*(q : ℝ))^(q-r)) := by
    calc
      _ = ((M.choose r : ℝ)*(u.choose (q-r) : ℝ))*(4*(2*(q : ℝ)^2)^q) := by ring
      _ ≤ _ := hm
      _ = _ := by convert heq using 1 <;> ring
  have hFinal := hmiddle.trans hm'
  have hOne : 1 ≤ 4*(12*(q : ℝ))^q/(128*(q : ℝ))^(q-r) := by
    apply (mul_le_mul_iff_left₀ (show 0 < (M : ℝ)^q by positivity)).mp
    simpa only [mul_one, one_mul, mul_comm] using hFinal
  have hcompare := (le_div_iff₀ (show 0 < (128*(q : ℝ))^(q-r) by positivity)).mp hOne
  exact thin_scalar_power_inconsistent q r hq hrq herror (by simpa only [one_mul] using hcompare)

#print axioms thin_counts_inconsistent
end AllPathsLocal
