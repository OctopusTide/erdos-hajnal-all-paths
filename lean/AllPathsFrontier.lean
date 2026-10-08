import AllPathsFrontierNum
import RP5QuantitativeFrontier

/-!
# The RPq frontier purification lemma

Main paper, Lemma "RPq frontier purification", with the paper's parameters
`a₀ = τ/(2^12 m^(4A+10))`, `a₁ = τ/(64 m^2)`, `η = 1/(16 m^(A+2))`. For blocks of size
at least `(m/τ)^(E(4A+11))` and at least `N/m^b₀`, either a `z^4`-restricted set of
size `z^(e+b₀+2A+1) N` at an actual scale `z ∈ [(τ/m)^(c(4A+11)), 1/m]`, or a directed
`τ`-semisparse blockade of actual length `K` with `m ≤ K^4`, `K ≤ (m/τ)^(k(4A+11))`
and width `N/K^(3b₀+9A+d+3)`.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The two outcomes of the frontier lemma. -/
def FrontierOut (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (m : ℕ) (τ N : ℝ)
    (A e c k d b₀ : ℕ) : Prop :=
  (∃ z : ℝ, (τ / (m : ℝ)) ^ (c * (4 * A + 11)) ≤ z ∧ z ≤ 1 / (m : ℝ) ∧
    ∃ T ⊆ Y, z ^ (e + b₀ + 2 * A + 1) * N ≤ (T.card : ℝ) ∧ EHP6.Restricted G (z ^ 4) T) ∨
  (∃ K : ℕ, (m : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ ((m : ℝ) / τ) ^ (k * (4 * A + 11)) ∧
    ∃ γ : EHP6.Blockade Y K (N / (K : ℝ) ^ (3 * b₀ + 9 * A + d + 3)), γ.m = K ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G τ (γ.B j) (γ.B i))

set_option maxHeartbeats 1600000 in
theorem rpq_frontier (n : ℕ) {A e c k d E : ℕ} {η₀ : ℝ} (hE : 1 ≤ E) (hk : 1 ≤ k)
    (hT1 : LowerTooth G (n + 2) A e c k d E η₀) (hT2 : LowerTooth G (n + 1) A e c k d E η₀)
    {m : ℕ} (Z R : Fin m → Finset V) {U Y : Finset V}
    (hZY : ∀ i, Z i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hRU : ∀ i, R i ⊆ U) (hRc : ∀ i, (R i).card ≤ m)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n + 3) Y u)
    (hrootfull : ∀ j, ∀ r ∈ R j, ∀ v ∈ Z j, G.Adj r v)
    (hII : ∀ i j, i < j → ∀ v ∈ Z j, RootedPathFree G (n + 2) (Z i) v)
    (hIII : ∀ (N : ℕ) (f : Fin N → Fin m), StrictMono f →
      (∀ a b : Fin N, a.val + 1 = b.val → ¬ EHP6.Complete G (Z (f a)) (Z (f b))) →
      ∀ a b, a < b → ∃ u ∈ R (f a), RootSeparates G u (Z (f a)) (Z (f b)))
    {τ N : ℝ} {b₀ : ℕ} (hm : 2 ^ 16 ≤ m) (hmη : 1 / (m : ℝ) ≤ η₀)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hN : 0 ≤ N)
    (hsizeN : ∀ i, N / (m : ℝ) ^ b₀ ≤ ((Z i).card : ℝ))
    (hsizeQ : ∀ i, ((m : ℝ) / τ) ^ (E * (4 * A + 11)) ≤ ((Z i).card : ℝ)) :
    FrontierOut G Y m τ N A e c k d b₀ := by
  have hmpos : 0 < m := by omega
  have hmR : (2 : ℝ) ^ 16 ≤ m := by exact_mod_cast hm
  have hmR0 : (0 : ℝ) < m := by linarith [show (0 : ℝ) < 2 ^ 16 by positivity]
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (m : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu : u ≤ 1 / 2 ^ 16 := by
    rw [hudef]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hmR
  have hu1 : u ≤ 1 := hu.trans (by norm_num)
  have hmu : (m : ℝ) = 1 / u := by rw [hudef, one_div_one_div]
  have hτu : 0 < τ * u := by positivity
  have hτm : τ / (m : ℝ) = τ * u := by rw [hudef]; ring
  have hmτ : (m : ℝ) / τ = 1 / (τ * u) := by rw [hudef]; field_simp
  obtain ⟨hfa0, hfa01, hfa1, hfa1u, hfa1τ⟩ := fn_fine hu0 hu hτ0 hτ1 A
  obtain ⟨Wq, hWq⟩ : ∃ Wq : ℝ, Wq = (1 / (τ * u)) ^ (E * (4 * A + 11)) := ⟨_, rfl⟩
  have hWqpos : 0 < Wq := by rw [hWq]; positivity
  obtain ⟨Wmin, hWmindef⟩ : ∃ Wmin : ℝ, Wmin = max (N * u ^ b₀) Wq := ⟨_, rfl⟩
  have hWN : N * u ^ b₀ ≤ Wmin := by rw [hWmindef]; exact le_max_left _ _
  have hWQ : Wq ≤ Wmin := by rw [hWmindef]; exact le_max_right _ _
  have hWpos : 0 < Wmin := hWqpos.trans_le hWQ
  have hZN : ∀ i, N * u ^ b₀ ≤ ((Z i).card : ℝ) := by
    intro i
    have h := hsizeN i
    have e1 : N / (m : ℝ) ^ b₀ = N * u ^ b₀ := by
      rw [hudef, one_div_pow]; ring
    linarith
  have hWmin : ∀ i, Wmin ≤ ((Z i).card : ℝ) := by
    intro i
    rw [hWmindef]
    refine max_le (hZN i) ?_
    have h := hsizeQ i
    rw [hmτ] at h
    rw [hWq]
    exact h
  have huA1 : u ^ A ≤ 1 := fn_u_small hu0 hu A
  have huA0 : 0 < u ^ A := by positivity
  have hord1 : 1 / (τ * u ^ (4 * A + 10) / 2 ^ 12) ^ E ≤ Wmin :=
    (by rw [hWq]; exact fn_a0_pow hu0 hu hτ0 hτ1 A E : _ ≤ Wq).trans hWQ
  have hord3 : 1 / (τ * u ^ 2 / 64) ^ E ≤ 13 * (u ^ A * (u ^ A * Wmin)) / 16 := by
    have h1 := fn_ord3 hu0 hu hτ0 hτ1 A E hE
    rw [← hWq] at h1
    have h2 : u ^ A * (u ^ A * Wq) ≤ u ^ A * (u ^ A * Wmin) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWQ huA0.le) huA0.le
    linarith
  have hord2 : 1 / (τ * u ^ 2 / 64) ^ E ≤ u ^ A * Wmin := by
    have h1 : u ^ A * (u ^ A * Wmin) ≤ 1 * (u ^ A * Wmin) :=
      mul_le_mul_of_nonneg_right huA1 (by positivity)
    have h2 : 0 ≤ u ^ A * (u ^ A * Wmin) := by positivity
    linarith
  obtain ⟨hs256, hs3, hs4⟩ := sqrt_frontier_length_bounds m hm
  have hsR : (256 : ℝ) ≤ (Nat.sqrt m : ℝ) := by exact_mod_cast hs256
  have hsm : ((Nat.sqrt m : ℕ) : ℝ) ≤ 1 / u := by
    rw [← hmu]
    exact_mod_cast Nat.sqrt_le_self m
  have hlowc : (τ / (m : ℝ)) ^ (c * (4 * A + 11)) ≤ (τ * u ^ (4 * A + 10) / 2 ^ 12) ^ c := by
    rw [hτm, Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (fn_a0_low hu0 hu hτ0 hτ1 A) c
  have hcapk : 1 / (τ * u ^ (4 * A + 10) / 2 ^ 12) ^ k ≤
      ((m : ℝ) / τ) ^ (k * (4 * A + 11)) := by
    rw [hmτ]; exact fn_a0_pow hu0 hu hτ0 hτ1 A k
  -- conversion of an early output of any of the three lower calls
  have early : ∀ (X : Finset V) (a Zc : ℝ), X ⊆ Y → τ * u ^ (4 * A + 10) / 2 ^ 12 ≤ a →
      a ≤ τ → N * u ^ b₀ ≤ Zc → u ^ (2 * A) * Zc / 2 ≤ (X.card : ℝ) →
      ToothEarly G X a (1 / (m : ℝ)) e c k d → FrontierOut G Y m τ N A e c k d b₀ := by
    intro X a Zc hXY haa haτ hZc hXc hearly
    have ha0 : 0 < a := hfa0.trans_le haa
    rcases hearly with ⟨z, hz1, hz2, W, hWX, hWsize, hWres⟩ | ⟨K, hK1, hK2, γ, hγm, hγ⟩
    · left
      have hz0 : 0 < z := lt_of_lt_of_le (pow_pos ha0 _) hz1
      refine ⟨z, hlowc.trans ((pow_le_pow_left₀ hfa0.le haa c).trans hz1), hz2, W,
        hWX.trans hXY, ?_, hWres⟩
      exact fn_conv_restricted hu0 hu hz0 (by rw [hudef]; exact hz2) hN hZc hXc hWsize
    · right
      have hKm : (m : ℝ) ≤ K := by
        rw [one_div_one_div] at hK1
        exact hK1
      have hK1' : (1 : ℝ) ≤ K := le_trans (by linarith [show (1 : ℝ) ≤ 2 ^ 16 by norm_num]) hKm
      have hK2' : (2 : ℝ) ≤ K := le_trans (by linarith [show (2 : ℝ) ≤ 2 ^ 16 by norm_num]) hKm
      refine ⟨K, ?_, ?_, γ.mono hXY le_rfl ?_, hγm, fun i j hij => ?_⟩
      · calc (m : ℝ) ≤ K := hKm
          _ = (K : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (K : ℝ) ^ 4 := pow_le_pow_right₀ hK1' (by norm_num)
      · refine hK2.trans (le_trans ?_ hcapk)
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hfa0 _)
          (pow_le_pow_left₀ hfa0.le haa k)
      · exact fn_conv_blockade hu0 (by rw [← hmu]; exact hKm) hK2' hN hZc hXc
      · rcases hγ i j hij with h | h
        · exact Or.inl h
        · right
          intro v hv
          exact (h v hv).trans (mul_le_mul_of_nonneg_right haτ (Nat.cast_nonneg _))
  have hu2A : u ^ (2 * A) = u ^ A * u ^ A := by rw [show 2 * A = A + A by ring, pow_add]
  rcases rpq_frontier_core n hT1 hT2 Z R hZY hdisj hRU hRc hout hfree hrootfull hII hIII
      (a₀ := τ * u ^ (4 * A + 10) / 2 ^ 12) (a₁ := τ * u ^ 2 / 64) (η := u ^ (A + 2) / 16)
      (τ := τ) (Wmin := Wmin) (w := u ^ A) (β := τ * u ^ (3 * A + 10) / 2 ^ 13)
      (β' := τ * u ^ (2 * A + 10) / 2 ^ 12) (r₀ := Nat.sqrt m)
      (by rw [hudef]) hmpos hfa0 (by rw [← hudef]; exact hfa01.trans hfa1u) hfa1
      (by rw [← hudef]; exact hfa1u) hmη (by positivity) hWpos hWmin hord1 hord2 hord3
      (by rw [hmu]; exact fn_b2 hu0 hu hτ0 hτ1 A) (by rw [hmu]; exact fn_b2' hu0 A)
      (fn_βθ hu0 hτ0 A) (fn_β hu0 hu hτ0 hτ1 _)
      (by rw [hmu]; exact fn_b3 hu0 hu hτ0 hτ1 A) (fn_β'β hu0 hτ0 A)
      (fn_β'1 hu0 hu hτ0 hτ1 _)
      (fn_β'τ hu0 hu hτ0 (Nat.cast_nonneg _) hsm A) (by omega) (Nat.sqrt_le m) with
    ⟨i, hearly⟩ | ⟨j, B, hBZ, hBsize, hearly⟩ | ⟨j, C, hCZ, hCsize, hearly⟩ | ⟨γ, hγm, hγ⟩
  · refine early (Z i) _ ((Z i).card : ℝ) (hZY i) le_rfl ?_ (hZN i) ?_ hearly
    · exact hfa01.trans hfa1τ
    · have h1 : u ^ (2 * A) ≤ 1 := fn_u_small hu0 hu _
      have h0 : (0 : ℝ) ≤ (Z i).card := Nat.cast_nonneg _
      nlinarith
  · refine early B _ ((Z j).card : ℝ) (hBZ.trans (hZY j)) hfa01 hfa1τ (hZN j) ?_ hearly
    have h0 : (0 : ℝ) ≤ (Z j).card := Nat.cast_nonneg _
    have h1 : u ^ A * (u ^ A * ((Z j).card : ℝ)) ≤ 1 * (u ^ A * (Z j).card) :=
      mul_le_mul_of_nonneg_right huA1 (mul_nonneg huA0.le h0)
    have h2 : 0 ≤ u ^ A * (u ^ A * ((Z j).card : ℝ)) :=
      mul_nonneg huA0.le (mul_nonneg huA0.le h0)
    rw [hu2A]
    linarith [show u ^ A * u ^ A * ((Z j).card : ℝ) = u ^ A * (u ^ A * (Z j).card) by ring]
  · refine early C _ ((Z j).card : ℝ) (hCZ.trans (hZY j)) hfa01 hfa1τ (hZN j) ?_ hearly
    have h0 : (0 : ℝ) ≤ (Z j).card := Nat.cast_nonneg _
    have h2 : 0 ≤ u ^ A * (u ^ A * ((Z j).card : ℝ)) :=
      mul_nonneg huA0.le (mul_nonneg huA0.le h0)
    rw [hu2A]
    linarith [show u ^ A * u ^ A * ((Z j).card : ℝ) = u ^ A * (u ^ A * (Z j).card) by ring]
  · right
    have hr2 : (2 : ℝ) ≤ (Nat.sqrt m : ℝ) := by linarith
    have hur : 1 ≤ u * ((Nat.sqrt m : ℕ) : ℝ) ^ 3 := by
      have h3 : (m : ℝ) ≤ ((Nat.sqrt m : ℕ) : ℝ) ^ 3 := by exact_mod_cast hs3
      have := mul_le_mul_of_nonneg_left h3 hu0.le
      rw [hmu, mul_one_div, div_self hu0.ne'] at this
      exact this
    refine ⟨Nat.sqrt m, by exact_mod_cast hs4, ?_, γ.mono subset_rfl le_rfl
      (fn_conv_main hu0 hr2 hur hN hWN), hγm, hγ⟩
    have hP1 : (1 : ℝ) ≤ (m : ℝ) / τ := by
      rw [le_div_iff₀ hτ0]; linarith [show (1 : ℝ) ≤ 2 ^ 16 by norm_num]
    have hmP : (m : ℝ) ≤ (m : ℝ) / τ := by
      rw [le_div_iff₀ hτ0]
      nlinarith
    calc ((Nat.sqrt m : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sqrt_le_self m
      _ ≤ (m : ℝ) / τ := hmP
      _ = ((m : ℝ) / τ) ^ 1 := (pow_one _).symm
      _ ≤ ((m : ℝ) / τ) ^ (k * (4 * A + 11)) := pow_le_pow_right₀ hP1 (by nlinarith)

#print axioms rpq_frontier
end AllPathsLocal
