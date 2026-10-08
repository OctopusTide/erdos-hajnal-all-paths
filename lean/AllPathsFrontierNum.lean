import AllPathsFrontierCore

/-!
Scalar side conditions of the RPq frontier lemma (main paper, subsections "Two
preparatory passes", "Offending pairs and the RP(q-2) pass" and "Order hypotheses
and early outputs"). Throughout `u = 1/m` and
`a₀ = τ u^(4A+10)/2^12`, `a₁ = τ u^2/64`, `η = u^(A+2)/16`, `w = u^A`,
`β = τ u^(3A+10)/2^13`, `β' = τ u^(2A+10)/2^12`.
-/

namespace AllPathsLocal

theorem fn_u_small {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (j : ℕ) : u ^ j ≤ 1 :=
  pow_le_one₀ hu0.le (hu.trans (by norm_num))

theorem fn_b2 {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A : ℕ) :
    (1 / u) * (τ * u ^ (4 * A + 10) / 2 ^ 12 / 4 / (u ^ (A + 2) / 16) / u ^ A +
      τ * u ^ 2 / 64 / 4) ≤ 1 / 8 := by
  have e1 : τ * u ^ (4 * A + 10) / 2 ^ 12 / 4 / (u ^ (A + 2) / 16) / u ^ A =
      τ * u ^ (2 * A + 8) / 2 ^ 10 := by
    rw [show 4 * A + 10 = (2 * A + 8) + (A + 2) + A by ring, pow_add, pow_add]
    field_simp
    ring
  have e2 : (1 / u) * (τ * u ^ (2 * A + 8) / 2 ^ 10 + τ * u ^ 2 / 64 / 4) =
      τ * u ^ (2 * A + 7) / 2 ^ 10 + τ * u / 256 := by
    rw [show 2 * A + 8 = (2 * A + 7) + 1 by ring, pow_succ]
    field_simp
    ring
  rw [e1, e2]
  have h1 : u ^ (2 * A + 7) ≤ 1 := fn_u_small hu0 hu _
  have h2 : τ * u ^ (2 * A + 7) ≤ 1 := by
    have := mul_le_mul hτ1 h1 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h3 : τ * u ≤ 1 := by
    have := mul_le_mul hτ1 (hu.trans (by norm_num : (1 : ℝ) / 2 ^ 16 ≤ 1)) hu0.le
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h4 : τ * u ^ (2 * A + 7) / 2 ^ 10 ≤ 1 / 2 ^ 10 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h5 : τ * u / 256 ≤ 1 / 256 := div_le_div_of_nonneg_right h3 (by norm_num)
  have h6 : (1 : ℝ) / 2 ^ 10 + 1 / 256 ≤ 1 / 8 := by norm_num
  linarith

theorem fn_b2' {u : ℝ} (hu0 : 0 < u) (A : ℕ) :
    (1 / u) ^ 2 * (u ^ (A + 2) / 16) ≤ u ^ A / 16 := by
  have e : (1 / u) ^ 2 * (u ^ (A + 2) / 16) = u ^ A / 16 := by
    rw [pow_add]
    field_simp
  exact le_of_eq e

theorem fn_βθ {u τ : ℝ} (hu0 : 0 < u) (hτ0 : 0 < τ) (A : ℕ) :
    τ * u ^ (4 * A + 10) / 2 ^ 12 / 4 ≤ τ * u ^ (3 * A + 10) / 2 ^ 13 * (13 * u ^ A / 16) := by
  have e : τ * u ^ (3 * A + 10) / 2 ^ 13 * (13 * u ^ A / 16) =
      τ * u ^ (4 * A + 10) * (13 / 2 ^ 17) := by
    rw [show 4 * A + 10 = (3 * A + 10) + A by ring, pow_add]
    ring
  rw [e]
  have hp : 0 ≤ τ * u ^ (4 * A + 10) := by positivity
  have : τ * u ^ (4 * A + 10) / 2 ^ 12 / 4 = τ * u ^ (4 * A + 10) * (8 / 2 ^ 17) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by norm_num) hp

theorem fn_β {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (j : ℕ) : 2 * (τ * u ^ j / 2 ^ 13) ≤ 1 := by
  have h1 : u ^ j ≤ 1 := fn_u_small hu0 hu _
  have h2 : τ * u ^ j ≤ 1 := by
    have := mul_le_mul hτ1 h1 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h3 : τ * u ^ j / 2 ^ 13 ≤ 1 / 2 ^ 13 := div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : (2 : ℝ) * (1 / 2 ^ 13) ≤ 1 := by norm_num
  linarith

theorem fn_b3 {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A : ℕ) :
    (1 / u) * (τ * u ^ (3 * A + 10) / 2 ^ 13 / (1 / 2) / u ^ A + τ * u ^ 2 / 64 / 4) ≤
      1 / 8 := by
  have e1 : τ * u ^ (3 * A + 10) / 2 ^ 13 / (1 / 2) / u ^ A = τ * u ^ (2 * A + 10) / 2 ^ 12 := by
    rw [show 3 * A + 10 = (2 * A + 10) + A by ring, pow_add]
    field_simp
  have e2 : (1 / u) * (τ * u ^ (2 * A + 10) / 2 ^ 12 + τ * u ^ 2 / 64 / 4) =
      τ * u ^ (2 * A + 9) / 2 ^ 12 + τ * u / 256 := by
    rw [show 2 * A + 10 = (2 * A + 9) + 1 by ring, pow_succ]
    field_simp
    ring
  rw [e1, e2]
  have h1 : u ^ (2 * A + 9) ≤ 1 := fn_u_small hu0 hu _
  have h2 : τ * u ^ (2 * A + 9) ≤ 1 := by
    have := mul_le_mul hτ1 h1 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h3 : τ * u ≤ 1 := by
    have := mul_le_mul hτ1 (hu.trans (by norm_num : (1 : ℝ) / 2 ^ 16 ≤ 1)) hu0.le
      (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h4 : τ * u ^ (2 * A + 9) / 2 ^ 12 ≤ 1 / 2 ^ 12 :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h5 : τ * u / 256 ≤ 1 / 256 := div_le_div_of_nonneg_right h3 (by norm_num)
  have h6 : (1 : ℝ) / 2 ^ 12 + 1 / 256 ≤ 1 / 8 := by norm_num
  linarith

theorem fn_β'β {u τ : ℝ} (hu0 : 0 < u) (hτ0 : 0 < τ) (A : ℕ) :
    τ * u ^ (3 * A + 10) / 2 ^ 13 ≤ τ * u ^ (2 * A + 10) / 2 ^ 12 * (13 * u ^ A / 16) := by
  have e : τ * u ^ (2 * A + 10) / 2 ^ 12 * (13 * u ^ A / 16) =
      τ * u ^ (3 * A + 10) * (13 / 2 ^ 16) := by
    rw [show 3 * A + 10 = (2 * A + 10) + A by ring, pow_add]
    ring
  rw [e]
  have hp : 0 ≤ τ * u ^ (3 * A + 10) := by positivity
  have : τ * u ^ (3 * A + 10) / 2 ^ 13 = τ * u ^ (3 * A + 10) * (8 / 2 ^ 16) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (by norm_num) hp

theorem fn_β'1 {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (j : ℕ) : τ * u ^ j / 2 ^ 12 ≤ 1 := by
  have h1 : u ^ j ≤ 1 := fn_u_small hu0 hu _
  have h2 : τ * u ^ j ≤ 1 := by
    have := mul_le_mul hτ1 h1 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have h3 : τ * u ^ j / 2 ^ 12 ≤ 1 / 2 ^ 12 := div_le_div_of_nonneg_right h2 (by positivity)
  linarith [show (1 : ℝ) / 2 ^ 12 ≤ 1 by norm_num]

theorem fn_β'τ {u τ r : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / u) (A : ℕ) :
    r * (τ * u ^ (2 * A + 10) / 2 ^ 12) ≤ τ := by
  have h1 : r * u ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hr hu0.le
    rwa [one_div, inv_mul_cancel₀ hu0.ne'] at this
  have h2 : u ^ (2 * A + 9) ≤ 1 := fn_u_small hu0 hu _
  have e : r * (τ * u ^ (2 * A + 10) / 2 ^ 12) = (r * u) * (τ * u ^ (2 * A + 9)) / 2 ^ 12 := by
    rw [show 2 * A + 10 = (2 * A + 9) + 1 by ring, pow_succ]
    ring
  rw [e]
  have h3 : τ * u ^ (2 * A + 9) ≤ τ := by
    have := mul_le_mul_of_nonneg_left h2 hτ0.le
    linarith
  have h4 : (r * u) * (τ * u ^ (2 * A + 9)) ≤ 1 * τ :=
    mul_le_mul h1 h3 (by positivity) (by norm_num)
  have h5 : (r * u) * (τ * u ^ (2 * A + 9)) / 2 ^ 12 ≤ τ / 2 ^ 12 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have h6 : τ / 2 ^ 12 ≤ τ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Basic facts about the two fine parameters. -/
theorem fn_fine {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A : ℕ) :
    0 < τ * u ^ (4 * A + 10) / 2 ^ 12 ∧ τ * u ^ (4 * A + 10) / 2 ^ 12 ≤ τ * u ^ 2 / 64 ∧
    0 < τ * u ^ 2 / 64 ∧ τ * u ^ 2 / 64 ≤ u ∧ τ * u ^ 2 / 64 ≤ τ := by
  have hu1 : u ≤ 1 := hu.trans (by norm_num)
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · have h1 : u ^ (4 * A + 10) ≤ u ^ 2 := pow_le_pow_of_le_one hu0.le hu1 (by omega)
    have h2 : τ * u ^ (4 * A + 10) ≤ τ * u ^ 2 := mul_le_mul_of_nonneg_left h1 hτ0.le
    have h3 : τ * u ^ (4 * A + 10) / 2 ^ 12 ≤ τ * u ^ 2 / 2 ^ 12 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have h4 : τ * u ^ 2 / 2 ^ 12 ≤ τ * u ^ 2 / 64 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
    linarith
  · have h1 : τ * u ^ 2 ≤ 1 * u := by
      have : τ * u ^ 2 = (τ * u) * u := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hu0.le
      have := mul_le_mul hτ1 hu1 hu0.le (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    have h2 : τ * u ^ 2 / 64 ≤ τ * u ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]
      have : 0 ≤ τ * u ^ 2 := by positivity
      linarith
    linarith
  · have h1 : u ^ 2 ≤ 1 := fn_u_small hu0 hu 2
    have h2 : τ * u ^ 2 ≤ τ := by
      have := mul_le_mul_of_nonneg_left h1 hτ0.le
      linarith
    have h3 : τ * u ^ 2 / 64 ≤ τ * u ^ 2 := by
      rw [div_le_iff₀ (by norm_num)]
      have : 0 ≤ τ * u ^ 2 := by positivity
      linarith
    linarith

/-- `(τ/m)^(4A+11) ≤ a₀`. -/
theorem fn_a0_low {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A : ℕ) : (τ * u) ^ (4 * A + 11) ≤ τ * u ^ (4 * A + 10) / 2 ^ 12 := by
  have h1 : τ ^ (4 * A + 11) ≤ τ := by
    calc τ ^ (4 * A + 11) ≤ τ ^ 1 := pow_le_pow_of_le_one hτ0.le hτ1 (by omega)
      _ = τ := pow_one τ
  have h2 : u ≤ 1 / 2 ^ 12 := hu.trans (by norm_num)
  have e : (τ * u) ^ (4 * A + 11) = τ ^ (4 * A + 11) * (u ^ (4 * A + 10) * u) := by
    rw [mul_pow, show 4 * A + 11 = (4 * A + 10) + 1 by ring, pow_succ u]
  rw [e]
  have h3 : u ^ (4 * A + 10) * u ≤ u ^ (4 * A + 10) * (1 / 2 ^ 12) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : τ ^ (4 * A + 11) * (u ^ (4 * A + 10) * u) ≤ τ * (u ^ (4 * A + 10) * (1 / 2 ^ 12)) :=
    mul_le_mul h1 h3 (by positivity) hτ0.le
  linarith [show τ * (u ^ (4 * A + 10) * (1 / 2 ^ 12)) = τ * u ^ (4 * A + 10) / 2 ^ 12 by ring]

/-- `a₀^(-j) ≤ (m/τ)^(j(4A+11))`. -/
theorem fn_a0_pow {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A j : ℕ) :
    1 / (τ * u ^ (4 * A + 10) / 2 ^ 12) ^ j ≤ (1 / (τ * u)) ^ (j * (4 * A + 11)) := by
  have hlow := fn_a0_low hu0 hu hτ0 hτ1 A
  have hpos : 0 < (τ * u) ^ (4 * A + 11) := by positivity
  have h1 : ((τ * u) ^ (4 * A + 11)) ^ j ≤ (τ * u ^ (4 * A + 10) / 2 ^ 12) ^ j :=
    pow_le_pow_left₀ hpos.le hlow j
  have e : (1 / (τ * u)) ^ (j * (4 * A + 11)) = 1 / ((τ * u) ^ (4 * A + 11)) ^ j := by
    rw [one_div_pow, ← pow_mul, Nat.mul_comm (4 * A + 11) j]
  rw [e]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h1

/-- The order requirement of the second and third lower calls. -/
theorem fn_ord3 {u τ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2 ^ 16) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (A E : ℕ) (hE : 1 ≤ E) :
    1 / (τ * u ^ 2 / 64) ^ E ≤
      13 * (u ^ A * (u ^ A * (1 / (τ * u)) ^ (E * (4 * A + 11)))) / 16 := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 / (τ * u) := ⟨_, rfl⟩
  have hτu : 0 < τ * u := by positivity
  have hu1 : u ≤ 1 := hu.trans (by norm_num)
  have hPu : 1 / u ≤ P := by
    rw [hP]
    apply div_le_div_of_nonneg_left (by norm_num) hτu
    have := mul_le_mul_of_nonneg_right hτ1 hu0.le
    linarith
  have hu16 : (2 : ℝ) ^ 16 ≤ 1 / u := by
    rw [le_div_iff₀ hu0]
    have := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 2 ^ 16 by positivity)
    norm_num at this ⊢
    linarith
  have hP16 : (2 : ℝ) ^ 16 ≤ P := hu16.trans hPu
  have hP1 : 1 ≤ P := le_trans (by norm_num) hP16
  have hP0 : 0 < P := by linarith
  have huP : 1 ≤ u * P := by
    have := mul_le_mul_of_nonneg_left hPu hu0.le
    rwa [mul_one_div, div_self hu0.ne'] at this
  -- 1/a₁ ≤ P^3
  have h1 : 1 / (τ * u ^ 2 / 64) ≤ P ^ 3 := by
    have e : 1 / (τ * u ^ 2 / 64) = 64 * (1 / u) * P := by
      rw [hP]; field_simp
    rw [e]
    have h64 : (64 : ℝ) ≤ P := le_trans (by norm_num) hP16
    have : 64 * (1 / u) * P ≤ P * P * P := by
      apply mul_le_mul_of_nonneg_right _ hP0.le
      exact mul_le_mul h64 hPu (by positivity) hP0.le
    linarith [show P * P * P = P ^ 3 by ring]
  have ha1pos : 0 < τ * u ^ 2 / 64 := by positivity
  have h2 : 1 / (τ * u ^ 2 / 64) ^ E ≤ (P ^ 3) ^ E := by
    rw [← one_div_pow]
    exact pow_le_pow_left₀ (by positivity) h1 E
  rw [← hP]
  refine h2.trans ?_
  -- P^(3E) ≤ (13/16) u^(2A) P^(E(4A+11))
  have e3 : (P ^ 3) ^ E = P ^ (3 * E) := (pow_mul P 3 E).symm
  have hsplit : P ^ (3 * E) * P ^ (4 * A + 8) ≤ P ^ (E * (4 * A + 11)) := by
    rw [← pow_add]
    apply pow_le_pow_right₀ hP1
    nlinarith
  have hmain : (16 : ℝ) / 13 ≤ u ^ A * (u ^ A * P ^ (4 * A + 8)) := by
    have e4 : u ^ A * (u ^ A * P ^ (4 * A + 8)) = (u * P) ^ (2 * A) * P ^ (2 * A + 8) := by
      rw [show 4 * A + 8 = 2 * A + (2 * A + 8) by ring, pow_add, mul_pow]
      rw [show 2 * A = A + A by ring, pow_add, pow_add]
      ring
    rw [e4]
    have h5 : 1 ≤ (u * P) ^ (2 * A) := one_le_pow₀ huP
    have h6 : (2 : ℝ) ≤ P ^ (2 * A + 8) := by
      have : P ^ 1 ≤ P ^ (2 * A + 8) := pow_le_pow_right₀ hP1 (by omega)
      rw [pow_one] at this
      linarith [show (2 : ℝ) ≤ 2 ^ 16 by norm_num]
    nlinarith
  rw [e3]
  have hP3 : 0 ≤ P ^ (3 * E) := by positivity
  have h7 : P ^ (3 * E) * (16 / 13) ≤ P ^ (3 * E) * (u ^ A * (u ^ A * P ^ (4 * A + 8))) :=
    mul_le_mul_of_nonneg_left hmain hP3
  have h8 : u ^ A * (u ^ A * (P ^ (3 * E) * P ^ (4 * A + 8))) ≤
      u ^ A * (u ^ A * P ^ (E * (4 * A + 11))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsplit (by positivity)
  have e9 : P ^ (3 * E) * (u ^ A * (u ^ A * P ^ (4 * A + 8))) =
      u ^ A * (u ^ A * (P ^ (3 * E) * P ^ (4 * A + 8))) := by ring
  nlinarith

/-- Restricted early outputs: size conversion to the common exponent. -/
theorem fn_conv_restricted {u z N Zc Xc Wc : ℝ} {A b₀ e : ℕ} (hu0 : 0 < u)
    (hu : u ≤ 1 / 2 ^ 16) (hz0 : 0 < z) (hzu : z ≤ u) (hN : 0 ≤ N)
    (hZ : N * u ^ b₀ ≤ Zc) (hX : u ^ (2 * A) * Zc / 2 ≤ Xc) (hW : z ^ e * Xc ≤ Wc) :
    z ^ (e + b₀ + 2 * A + 1) * N ≤ Wc := by
  refine le_trans ?_ hW
  have hz2 : z ≤ 1 / 2 := hzu.trans (hu.trans (by norm_num))
  have h1 : z ^ b₀ ≤ u ^ b₀ := pow_le_pow_left₀ hz0.le hzu _
  have h2 : z ^ (2 * A) ≤ u ^ (2 * A) := pow_le_pow_left₀ hz0.le hzu _
  have h3 : z ^ b₀ * N ≤ Zc := by
    have := mul_le_mul_of_nonneg_right h1 hN
    linarith [mul_comm N (u ^ b₀)]
  have hZc0 : 0 ≤ Zc := le_trans (by positivity) h3
  have h4 : z ^ (2 * A) * (z ^ b₀ * N) ≤ u ^ (2 * A) * Zc :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  have h5 : z * (z ^ (2 * A) * (z ^ b₀ * N)) ≤ u ^ (2 * A) * Zc / 2 := by
    have h6 : z * (z ^ (2 * A) * (z ^ b₀ * N)) ≤ 1 / 2 * (z ^ (2 * A) * (z ^ b₀ * N)) :=
      mul_le_mul_of_nonneg_right hz2 (by positivity)
    linarith
  have e1 : z ^ (e + b₀ + 2 * A + 1) * N = z ^ e * (z * (z ^ (2 * A) * (z ^ b₀ * N))) := by
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left (h5.trans hX) (by positivity)

/-- Blockade early outputs: width conversion to the common exponent. -/
theorem fn_conv_blockade {u K N Zc Xc : ℝ} {A b₀ d : ℕ} (hu0 : 0 < u)
    (hK : 1 / u ≤ K) (hK2 : 2 ≤ K) (hN : 0 ≤ N)
    (hZ : N * u ^ b₀ ≤ Zc) (hX : u ^ (2 * A) * Zc / 2 ≤ Xc) :
    N / K ^ (3 * b₀ + 9 * A + d + 3) ≤ Xc / K ^ d := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have huK : 1 ≤ u * K := by
    have := mul_le_mul_of_nonneg_left hK hu0.le
    rwa [mul_one_div, div_self hu0.ne'] at this
  -- N ≤ Xc * K^(b₀ + 2A + 1)
  have h1 : N ≤ Zc * K ^ b₀ := by
    have h := mul_le_mul_of_nonneg_right hZ (pow_nonneg hK0.le b₀)
    have e : N * u ^ b₀ * K ^ b₀ = N * (u * K) ^ b₀ := by rw [mul_pow]; ring
    have h2 : N * 1 ≤ N * (u * K) ^ b₀ := mul_le_mul_of_nonneg_left (one_le_pow₀ huK) hN
    linarith
  have hZc0 : 0 ≤ Zc := le_trans (by positivity) hZ
  have h3 : Zc ≤ Xc * (2 * K ^ (2 * A)) := by
    have h := mul_le_mul_of_nonneg_right hX (show (0 : ℝ) ≤ 2 * K ^ (2 * A) by positivity)
    have e : u ^ (2 * A) * Zc / 2 * (2 * K ^ (2 * A)) = Zc * (u * K) ^ (2 * A) := by
      rw [mul_pow]; ring
    have h2 : Zc * 1 ≤ Zc * (u * K) ^ (2 * A) :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ huK) hZc0
    linarith
  have hXc0 : 0 ≤ Xc := le_trans (by positivity) hX
  have h4 : N ≤ Xc * K ^ (b₀ + 2 * A + 1) := by
    have h5 : Zc * K ^ b₀ ≤ Xc * (2 * K ^ (2 * A)) * K ^ b₀ :=
      mul_le_mul_of_nonneg_right h3 (pow_nonneg hK0.le _)
    have h6 : Xc * (2 * K ^ (2 * A)) * K ^ b₀ ≤ Xc * (K * K ^ (2 * A)) * K ^ b₀ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK0.le _)
      apply mul_le_mul_of_nonneg_left _ hXc0
      exact mul_le_mul_of_nonneg_right hK2 (pow_nonneg hK0.le _)
    have e : Xc * (K * K ^ (2 * A)) * K ^ b₀ = Xc * K ^ (b₀ + 2 * A + 1) := by ring
    linarith
  rw [div_le_div_iff₀ (pow_pos hK0 _) (pow_pos hK0 _)]
  have h7 : N * K ^ d ≤ Xc * K ^ (b₀ + 2 * A + 1) * K ^ d :=
    mul_le_mul_of_nonneg_right h4 (pow_nonneg hK0.le _)
  have h8 : K ^ (b₀ + 2 * A + 1 + d) ≤ K ^ (3 * b₀ + 9 * A + d + 3) :=
    pow_le_pow_right₀ hK1 (by omega)
  have h9 : Xc * K ^ (b₀ + 2 * A + 1 + d) ≤ Xc * K ^ (3 * b₀ + 9 * A + d + 3) :=
    mul_le_mul_of_nonneg_left h8 hXc0
  have e2 : Xc * K ^ (b₀ + 2 * A + 1) * K ^ d = Xc * K ^ (b₀ + 2 * A + 1 + d) := by
    rw [pow_add _ (b₀ + 2 * A + 1) d]; ring
  linarith

/-- The main blockade: width conversion with `r = ⌊√m⌋`, `m ≤ r^3`. -/
theorem fn_conv_main {u r N Wmin : ℝ} {A b₀ d : ℕ} (hu0 : 0 < u) (hr2 : 2 ≤ r)
    (hur : 1 ≤ u * r ^ 3) (hN : 0 ≤ N) (hW : N * u ^ b₀ ≤ Wmin) :
    N / r ^ (3 * b₀ + 9 * A + d + 3) ≤
      13 * (u ^ A * (13 * (u ^ A * (u ^ A * Wmin)) / 16)) / 16 / r := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hW0 : 0 ≤ Wmin := le_trans (by positivity) hW
  have e : 13 * (u ^ A * (13 * (u ^ A * (u ^ A * Wmin)) / 16)) / 16 / r =
      (169 / 256) * (u ^ (3 * A) * Wmin) / r := by
    rw [show 3 * A = A + A + A by ring, pow_add, pow_add]; ring
  rw [e, div_le_div_iff₀ (pow_pos hr0 _) hr0]
  -- N ≤ u^(3A+b₀) N r^(3(3A+b₀)); and u^(3A) Wmin ≥ u^(3A+b₀) N
  have h1 : N * u ^ (3 * A + b₀) ≤ u ^ (3 * A) * Wmin := by
    have := mul_le_mul_of_nonneg_left hW (pow_nonneg hu0.le (3 * A))
    have e1 : u ^ (3 * A) * (N * u ^ b₀) = N * u ^ (3 * A + b₀) := by rw [pow_add]; ring
    linarith
  have h2 : N * 1 ≤ N * (u * r ^ 3) ^ (3 * A + b₀) :=
    mul_le_mul_of_nonneg_left (one_le_pow₀ hur) hN
  have e2 : N * (u * r ^ 3) ^ (3 * A + b₀) = N * u ^ (3 * A + b₀) * r ^ (9 * A + 3 * b₀) := by
    rw [mul_pow, ← pow_mul]
    rw [show 3 * (3 * A + b₀) = 9 * A + 3 * b₀ by ring]
    ring
  have h3 : N ≤ u ^ (3 * A) * Wmin * r ^ (9 * A + 3 * b₀) := by
    have := mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0.le (9 * A + 3 * b₀))
    linarith
  have hX0 : 0 ≤ u ^ (3 * A) * Wmin := by positivity
  -- N * r ≤ (169/256) X r^(dexp)
  have h4 : r ^ (9 * A + 3 * b₀) * r * 2 ≤ r ^ (3 * b₀ + 9 * A + d + 3) := by
    have h5 : r ^ (9 * A + 3 * b₀) * r * 2 ≤ r ^ (9 * A + 3 * b₀) * r * r :=
      mul_le_mul_of_nonneg_left hr2 (by positivity)
    have e3 : r ^ (9 * A + 3 * b₀) * r * r = r ^ (9 * A + 3 * b₀ + 2) := by ring
    have h6 : r ^ (9 * A + 3 * b₀ + 2) ≤ r ^ (3 * b₀ + 9 * A + d + 3) :=
      pow_le_pow_right₀ hr1 (by omega)
    linarith
  have h7 : N * r ≤ u ^ (3 * A) * Wmin * r ^ (9 * A + 3 * b₀) * r :=
    mul_le_mul_of_nonneg_right h3 hr0.le
  have h8 : u ^ (3 * A) * Wmin * (r ^ (9 * A + 3 * b₀) * r * 2) ≤
      u ^ (3 * A) * Wmin * r ^ (3 * b₀ + 9 * A + d + 3) :=
    mul_le_mul_of_nonneg_left h4 hX0
  have h9 : 0 ≤ u ^ (3 * A) * Wmin * r ^ (3 * b₀ + 9 * A + d + 3) := by positivity
  nlinarith

#print axioms fn_b2
#print axioms fn_ord3
#print axioms fn_conv_restricted
#print axioms fn_conv_blockade
#print axioms fn_conv_main
end AllPathsLocal
