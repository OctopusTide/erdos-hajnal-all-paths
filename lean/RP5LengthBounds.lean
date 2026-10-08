import RP5ExactLengths

namespace AllPathsLocal

/-- The TL2 integer length is at least sqrt(m), despite the constants 8 and 9.
    The paper's m>=2^16 is used essentially in this conversion. -/
theorem tl2_length_bounds (m L : ℝ) (hm : 65536 ≤ m) (hL : 0 ≤ L)
    (hlow : m ^ 3 ≤ (9 * L) ^ 4) (hupp : (8 * L) ^ 4 ≤ m ^ 3) :
    m ≤ L ^ 2 ∧ 2 ≤ L ∧ L ≤ m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 1 ≤ m := by linarith
  have hlow' : m ^ 3 ≤ 6561 * L ^ 4 := by nlinarith [hlow]
  have hupp' : 4096 * L ^ 4 ≤ m ^ 3 := by nlinarith [hupp]
  have hsq : m ≤ L ^ 2 := by
    by_contra h
    have hlt : L ^ 2 < m := lt_of_not_ge h
    have hp : L ^ 4 < m ^ 2 := by
      calc
        L ^ 4 = (L ^ 2) ^ 2 := by ring
        _ < m ^ 2 := by gcongr
    have hpositive : 0 < (m - 6561) * m ^ 2 := mul_pos (by linarith) (by positivity)
    nlinarith
  have hL2 : 2 ≤ L := by nlinarith
  have hLm : L ≤ m := by
    by_contra h
    have hlt : m < L := lt_of_not_ge h
    have hp : m ^ 4 ≤ L ^ 4 := by gcongr
    have hm34 : m ^ 3 ≤ m ^ 4 := pow_le_pow_right₀ hm1 (by decide)
    have hpos : 0 < L ^ 4 := by positivity
    nlinarith
  exact ⟨hsq, hL2, hLm⟩

/-- Both floor lengths in TL3 and TL4 are at least m and no more than 1/x. -/
theorem tooth_floor_length_bounds (m : ℕ) (x : ℝ) (hm : 2 ≤ m)
    (hx : 0 < x) (hxsmall : x ≤ 1 / (m : ℝ) ^ 2) :
    m ≤ ⌊1 / x⌋₊ ∧ m ≤ ⌊1 / (x * m)⌋₊ ∧
      (⌊1 / x⌋₊ : ℝ) ≤ 1 / x ∧ (⌊1 / (x * m)⌋₊ : ℝ) ≤ 1 / x := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hprod : x * (m : ℝ) ^ 2 ≤ 1 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).mp hxsmall
  have hxm : x * (m : ℝ) ≤ 1 := by
    have hmp : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      simpa using pow_le_pow_right₀ hm1 (by decide : 1 ≤ 2)
    have hh : x * (m : ℝ) ≤ x * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hmp hx.le
    exact hh.trans hprod
  have h3 : (m : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by nlinarith)
  have h4 : (m : ℝ) ≤ 1 / (x * m) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < x * m)).mpr (by nlinarith)
  have hf3 := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / x)
  have hf4 := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / (x * m))
  have hden : x ≤ x * (m : ℝ) := by nlinarith
  exact ⟨Nat.le_floor h3, Nat.le_floor h4, hf3,
    hf4.trans (div_le_div_of_nonneg_left (by norm_num) hx hden)⟩

/-- Exact floor lengths retain reciprocal information, with no unjustified
    replacement of floor(a) by a. -/
theorem reciprocal_floor_lower (a : ℝ) (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have hlt := Nat.lt_floor_add_one a
  have hf : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
    exact_mod_cast (Nat.le_floor (n := 1) (by norm_num; linarith : ((1 : ℕ) : ℝ) ≤ a))
  linarith

#print axioms tl2_length_bounds
#print axioms tooth_floor_length_bounds
#print axioms reciprocal_floor_lower

end AllPathsLocal
