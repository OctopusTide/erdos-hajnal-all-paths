import RP5ExactLengths

namespace AllPathsLocal

/-- Convert polynomial width loss using m<=K^4, preserving a concrete exponent. -/
theorem polynomial_width_convert (m K N A : ℝ) (p q d : ℕ)
    (hm : 0 ≤ m) (hK : 1 ≤ K) (hA : 0 ≤ A) (hN : N ≤ m ^ p * A)
    (hmK : m ≤ K ^ 4) (hexp : 4 * p + q ≤ d) :
    N / K ^ d ≤ A / K ^ q := by
  have hK0 : 0 < K := by linarith
  have hmp : m ^ p ≤ K ^ (4 * p) := by
    have h := pow_le_pow_left₀ hm hmK p
    simpa only [← pow_mul] using h
  have hden : m ^ p * K ^ q ≤ K ^ d := by
    calc
      m ^ p * K ^ q ≤ K ^ (4 * p) * K ^ q :=
        mul_le_mul_of_nonneg_right hmp (by positivity)
      _ = K ^ (4 * p + q) := by rw [pow_add]
      _ ≤ K ^ d := pow_le_pow_right₀ hK hexp
  apply (div_le_div_iff₀ (by positivity : 0 < K ^ d) (by positivity : 0 < K ^ q)).mpr
  calc
    N * K ^ q ≤ (m ^ p * A) * K ^ q := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = A * (m ^ p * K ^ q) := by ring
    _ ≤ A * K ^ d := mul_le_mul_of_nonneg_left hden hA

/-- One reciprocal-bound calculation covers TL2, TL3 and TL4, including every
    factor 2, floor loss and ambient m power. No asymptotic rounding is used. -/
theorem scaled_width_convert (m K N A x : ℝ) (z p a b q d D : ℕ)
    (hm : 1 ≤ m) (hK : 2 ≤ K) (hA : 0 ≤ A) (hx0 : 0 ≤ x)
    (hN : N ≤ m ^ p * A) (hmK : m ≤ K ^ z)
    (hx : 1 ≤ (2 * m ^ a * K) * x)
    (hexp : z * p + d + z * b + q * (z * a + 2) ≤ D) :
    N / K ^ D ≤ x ^ q * A / (2 ^ d * m ^ b) := by
  have hm0 : 0 < m := by linarith
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hmPow : ∀ n : ℕ, m ^ n ≤ K ^ (z * n) := by
    intro n
    simpa only [← pow_mul] using pow_le_pow_left₀ hm0.le hmK n
  have hden : 2 ^ d * m ^ b ≤ K ^ (d + z * b) := by
    calc
      2 ^ d * m ^ b ≤ K ^ d * K ^ (z * b) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hK d) (hmPow b) (by positivity) (by positivity)
      _ = K ^ (d + z * b) := by rw [pow_add]
  have hscale : 2 * m ^ a * K ≤ K ^ (z * a + 2) := by
    calc
      2 * m ^ a * K ≤ K * K ^ (z * a) * K := by gcongr; exact hmPow a
      _ = K ^ (z * a + 2) := by rw [pow_add]; ring
  have hscaleq : (2 * m ^ a * K) ^ q ≤ K ^ (q * (z * a + 2)) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * m ^ a * K) hscale q
    simpa only [← pow_mul, Nat.mul_comm] using h
  have htotal : m ^ p * (2 ^ d * m ^ b) * (2 * m ^ a * K) ^ q ≤ K ^ D := by
    calc
      m ^ p * (2 ^ d * m ^ b) * (2 * m ^ a * K) ^ q ≤
          K ^ (z * p) * K ^ (d + z * b) * K ^ (q * (z * a + 2)) := by
        gcongr
        · exact hmPow p
      _ = K ^ (z * p + d + z * b + q * (z * a + 2)) := by
        simp only [← pow_add]
        congr 1
        omega
      _ ≤ K ^ D := pow_le_pow_right₀ hK1 hexp
  have hrecip : 1 ≤ (2 * m ^ a * K) ^ q * x ^ q := by
    simpa only [one_pow, mul_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx q
  have hmain : m ^ p * (2 ^ d * m ^ b) ≤ K ^ D * x ^ q := by
    calc
      m ^ p * (2 ^ d * m ^ b) ≤
          (m ^ p * (2 ^ d * m ^ b)) * ((2 * m ^ a * K) ^ q * x ^ q) := by
        simpa using mul_le_mul_of_nonneg_left hrecip (show 0 ≤ m ^ p * (2 ^ d * m ^ b) by positivity)
      _ = (m ^ p * (2 ^ d * m ^ b) * (2 * m ^ a * K) ^ q) * x ^ q := by ring
      _ ≤ K ^ D * x ^ q := mul_le_mul_of_nonneg_right htotal (by positivity)
  apply (div_le_div_iff₀ (by positivity : 0 < K ^ D)
    (by positivity : 0 < (2 : ℝ) ^ d * m ^ b)).mpr
  calc
    N * (2 ^ d * m ^ b) ≤ (m ^ p * A) * (2 ^ d * m ^ b) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = A * (m ^ p * (2 ^ d * m ^ b)) := by ring
    _ ≤ A * (K ^ D * x ^ q) := mul_le_mul_of_nonneg_left hmain hA
    _ = (x ^ q * A) * K ^ D := by ring

#print axioms polynomial_width_convert
#print axioms scaled_width_convert

end AllPathsLocal
