import RP5SeparatedPipeline
import RP5QuantitativeFrontier

namespace AllPathsLocal

section PaperFrontier

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {Z : List (Finset V)}

local notation "m" => Z.length
local notation "r" => Nat.sqrt m

/-- III.4 with the paper's first and second Tooth parameters and integer
    r=floor(sqrt(m)). Graph-theoretic inputs are only an actual rooted cut frontier
    and the original RP5 hypothesis. Every representative and root family is built. -/
theorem paper_separated_family (hsub : ∀ K ∈ Z, K ⊆ Y)
    (hroot : Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v))
    (hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j))
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hm : 2 ^ 16 ≤ m) {τ W : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1)
    (hWlarge : 16 / (τ / (64 * (m : ℝ) ^ 5)) ^ 3 ≤ W)
    (hwidth : ∀ i : Fin m, W ≤ ((Z.get i).card : ℝ)) :
    (∃ i : Fin m, RP4Early G (Z.get i) (τ / (64 * (m : ℝ) ^ 5)) m) ∨
    (∃ i : Fin m, ∃ B ⊆ Z.get i, ((Z.get i).card : ℝ) / m ≤ B.card ∧
      RP4Early G B (1 / (m : ℝ) ^ 2) m) ∨
    (∃ γ : EHP6.Blockade Y m (W / (2 * (m : ℝ) ^ 4)), γ.m = m ∧ γ.IsComplete G) ∨
    (∃ γ : EHP6.Blockade Y r (W / (2 * (m : ℝ) ^ 3 * r)), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G τ (γ.B j) (γ.B i)) := by
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hr256 : 256 ≤ r := Nat.le_sqrt.mpr (by norm_num at hm ⊢; exact hm)
  have hr2 : 2 ≤ r := by omega
  have hcount : r * (r - 1) ≤ m :=
    (Nat.mul_le_mul_left r (Nat.sub_le r 1)).trans (Nat.sqrt_le m)
  obtain ⟨hx, hx20, hkx, hxτ, hβ, hprecision, hlarge'⟩ :=
    frontier_paper_scalar_bounds (m : ℝ) (r : ℝ) τ hmR (by positivity)
      (by exact_mod_cast Nat.sqrt_le_self m) hτ0 hτ
  have hW : 0 ≤ W := (show (0 : ℝ) < 16 / (τ / (64 * (m : ℝ) ^ 5)) ^ 3 by positivity).le.trans hWlarge
  exact separated_family_pipeline G U Y hsub hroot hseparator hout hfree hx hx20 hm hkx hτ hxτ hβ hprecision
    hr2 hcount hW hwidth (fun i => hWlarge.trans (hwidth i))
    (fun i => (hlarge'.trans hWlarge).trans (hwidth i))

#print axioms paper_separated_family

end PaperFrontier

section Quantitative

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {Z : List (Finset V)}

local notation "m" => Z.length
local notation "r" => Nat.sqrt m

/-- A fully checked quantitative frontier conclusion sufficient for the RP5 Tooth
    main proof. Width N/m^6 also covers the stronger positive-layer N/m^3 input.
    The output length K is EXACT and satisfies every stated length bound. -/
theorem quantitative_separated_family (hsub : ∀ K ∈ Z, K ⊆ Y)
    (hroot : Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v))
    (hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j))
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hm : 2 ^ 16 ≤ m) {τ N : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1) (hN0 : 0 ≤ N)
    (horder : 16 / (τ / (64 * (m : ℝ) ^ 5)) ^ 3 ≤ N / (m : ℝ) ^ 6)
    (hwidth : ∀ i : Fin m, N / (m : ℝ) ^ 6 ≤ ((Z.get i).card : ℝ)) :
    ∃ K : ℕ, (m : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ 64 * (m : ℝ) ^ 5 / τ ∧
      ∃ γ : EHP6.Blockade Y K (N / (K : ℝ) ^ 64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G τ (γ.B j) (γ.B i) := by
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  let x := τ / (64 * (m : ℝ) ^ 5)
  have hx : 0 < x := by dsimp [x]; positivity
  obtain ⟨hxsmall, hupper⟩ := paper_parameter_reciprocal_bounds (m : ℝ) τ hm1 hτ0 hτ
  have hrecip : 1 / x = 64 * (m : ℝ) ^ 5 / τ := by dsimp [x]; field_simp
  have hNbound : ∀ i : Fin m, N ≤ (m : ℝ) ^ 6 * (Z.get i).card := by
    intro i
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 6)).mp (hwidth i)
  rcases paper_separated_family G U Y hsub hroot hseparator hout hfree hm hτ0 hτ horder hwidth with
    ⟨i, early⟩ | ⟨i, A, hAZ, hAc, early⟩ | ⟨γ, hγm, hcomplete⟩ | ⟨γ, hγm, htypes⟩
  · obtain ⟨K, hlo, hup, δ, hδm, hpure⟩ :=
      rp4_early_convert G (hAY := hsub _ (List.get_mem Z i))
        hm hx hxsmall (by decide : 6 ≤ 7) (hNbound i) early
    rw [hrecip] at hup
    exact ⟨K, hlo, hup, δ, hδm, pure_blockade_directed G δ hpure hτ0.le⟩
  · have hNboundA : N ≤ (m : ℝ) ^ 7 * A.card := by
      have hZi : ((Z.get i).card : ℝ) ≤ A.card * m := (div_le_iff₀ hm0).mp hAc
      calc
        N ≤ (m : ℝ) ^ 6 * (Z.get i).card := hNbound i
        _ ≤ (m : ℝ) ^ 6 * (A.card * m) := mul_le_mul_of_nonneg_left hZi (by positivity)
        _ = (m : ℝ) ^ 7 * A.card := by ring
    have hAY := hAZ.trans (hsub _ (List.get_mem Z i))
    obtain ⟨K, hlo, hup, δ, hδm, hpure⟩ :=
      rp4_early_convert G hAY hm (by positivity : (0 : ℝ) < 1 / (m : ℝ) ^ 2)
        le_rfl (by decide : 7 ≤ 7) hNboundA early
    have heq : 1 / (1 / (m : ℝ) ^ 2) = (m : ℝ) ^ 2 := by field_simp
    rw [heq] at hup
    exact ⟨K, hlo, hup.trans hupper, δ, hδm, pure_blockade_directed G δ hpure hτ0.le⟩
  · have hA0 : (0 : ℝ) ≤ N / (m : ℝ) ^ 6 := by positivity
    have hNexact : N ≤ (m : ℝ) ^ 6 * (N / (m : ℝ) ^ 6) := by field_simp; exact le_rfl
    have hw' := scaled_width_convert (m : ℝ) (m : ℝ) N (N / (m : ℝ) ^ 6) 1
      1 6 0 4 0 1 64 hm1 (by linarith) hA0 (by norm_num) hNexact
      (by simp) (by simp; linarith) (by decide)
    have hw : N / (m : ℝ) ^ 64 ≤ (N / (m : ℝ) ^ 6) / (2 * (m : ℝ) ^ 4) := by simpa using hw'
    have hlo : (m : ℝ) ≤ (m : ℝ) ^ 4 := by simpa using pow_le_pow_right₀ hm1 (by decide : 1 ≤ 4)
    have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by simpa using pow_le_pow_right₀ hm1 (by decide : 1 ≤ 2)
    let δ := γ.mono (Finset.Subset.refl Y) le_rfl hw
    exact ⟨m, hlo, hm2.trans hupper, δ, hγm, fun i j hij => Or.inl (hcomplete i j (ne_of_lt hij))⟩
  · obtain ⟨hr256, hmr3, hmr4⟩ := sqrt_frontier_length_bounds m hm
    have hrR : (256 : ℝ) ≤ r := by exact_mod_cast hr256
    have hr0 : (0 : ℝ) < r := by linarith
    have hA0 : (0 : ℝ) ≤ N / (m : ℝ) ^ 6 := by positivity
    have hNexact : N ≤ (m : ℝ) ^ 6 * (N / (m : ℝ) ^ 6) := by field_simp; exact le_rfl
    have hw' := scaled_width_convert (m : ℝ) (r : ℝ) N (N / (m : ℝ) ^ 6) 1
      3 6 0 3 0 1 63 hm1 (by linarith) hA0 (by norm_num) hNexact
      (by exact_mod_cast hmr3) (by simp; linarith) (by decide)
    have hwdiv := div_le_div_of_nonneg_right hw' hr0.le
    have hw : N / (r : ℝ) ^ 64 ≤ (N / (m : ℝ) ^ 6) / (2 * (m : ℝ) ^ 3 * r) := by
      convert hwdiv using 1 <;> ring
    let δ := γ.mono (Finset.Subset.refl Y) le_rfl hw
    have hlo : (m : ℝ) ≤ (r : ℝ) ^ 4 := by exact_mod_cast hmr4
    have hup : (r : ℝ) ≤ 64 * (m : ℝ) ^ 5 / τ :=
      (show (r : ℝ) ≤ m by exact_mod_cast Nat.sqrt_le_self m).trans
        ((show (m : ℝ) ≤ (m : ℝ) ^ 2 by simpa using pow_le_pow_right₀ hm1 (by decide : 1 ≤ 2)).trans hupper)
    exact ⟨r, hlo, hup, δ, hγm, htypes⟩

#print axioms quantitative_separated_family

end Quantitative

end AllPathsLocal
