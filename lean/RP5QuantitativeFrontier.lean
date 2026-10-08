import RP5EarlyConversion

namespace AllPathsLocal

theorem pure_blockade_directed {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y : Finset V} {k w τ : ℝ}
    (β : EHP6.Blockade Y k w) (hp : β.IsPure G) (hτ : 0 ≤ τ) :
    ∀ i j, i < j → EHP6.Complete G (β.B i) (β.B j) ∨ EHP6.SparseTo G τ (β.B j) (β.B i) := by
  intro i j hij
  rcases hp i j (ne_of_lt hij) with h | h
  · exact Or.inl h
  · right
    intro v hv
    have heq : EHP6.nbrs G v (β.B i) = ∅ := by
      ext b
      constructor
      · intro hb
        obtain ⟨hbi, hbv⟩ := Finset.mem_filter.mp hb
        exact False.elim (h b hbi v hv hbv.symm)
      · intro hb
        exact False.elim (by simpa using hb)
    rw [heq]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem sqrt_frontier_length_bounds (m : ℕ) (hm : 2 ^ 16 ≤ m) :
    256 ≤ Nat.sqrt m ∧ m ≤ (Nat.sqrt m) ^ 3 ∧ m ≤ (Nat.sqrt m) ^ 4 := by
  have hr : 256 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by norm_num at hm ⊢; exact hm)
  have hupper := Nat.lt_succ_sqrt m
  have hp := Nat.mul_le_mul_left (Nat.sqrt m * Nat.sqrt m) (show 3 ≤ Nat.sqrt m by omega)
  have hm3 : m ≤ (Nat.sqrt m) ^ 3 := by nlinarith
  have hm4 : m ≤ (Nat.sqrt m) ^ 4 := by
    exact hm3.trans (pow_le_pow_right₀ (show 1 ≤ Nat.sqrt m by omega) (by decide))
  exact ⟨hr, hm3, hm4⟩

theorem paper_parameter_reciprocal_bounds (m τ : ℝ) (hm : 1 ≤ m)
    (hτ0 : 0 < τ) (hτ : τ ≤ 1) :
    τ / (64 * m ^ 5) ≤ 1 / m ^ 2 ∧ m ^ 2 ≤ 64 * m ^ 5 / τ := by
  have hm0 : 0 < m := by linarith
  have h25 : m ^ 2 ≤ m ^ 5 := pow_le_pow_right₀ hm (by decide)
  have hden : m ^ 2 ≤ 64 * m ^ 5 := by nlinarith [show 0 ≤ m ^ 5 by positivity]
  have hprod : τ * m ^ 2 ≤ 64 * m ^ 5 :=
    (mul_le_mul_of_nonneg_right hτ (show 0 ≤ m ^ 2 by positivity)).trans (by simpa using hden)
  constructor
  · exact (div_le_div_iff₀ (by positivity : 0 < 64 * m ^ 5) (by positivity : 0 < m ^ 2)).mpr (by simpa using hprod)
  · exact (le_div_iff₀ hτ0).mpr (by simpa only [mul_comm] using hprod)

section Quantitative

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {S : Finset V} {Z : List (Finset V)}

local notation "m" => Z.length
local notation "r" => Nat.sqrt m

/-- A fully checked quantitative frontier conclusion sufficient for the RP5 Tooth
    main proof. Width N/m^6 also covers the stronger positive-layer N/m^3 input.
    The output length K is EXACT and satisfies every stated length bound. -/
theorem quantitative_frontier (hfront : OrderedCutFrontier G U S Z) (hSY : S ⊆ Y)
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
  rcases paper_frontier G U Y hfront hSY hout hfree hm hτ0 hτ horder hwidth with
    ⟨i, early⟩ | ⟨i, A, hAZ, hAc, early⟩ | ⟨γ, hγm, hcomplete⟩ | ⟨γ, hγm, htypes⟩
  · obtain ⟨K, hlo, hup, δ, hδm, hpure⟩ :=
      rp4_early_convert G (hAY := ((ordered_frontier_properties G U hfront).1 _ (List.get_mem Z i)).trans hSY)
        hm hx hxsmall (by decide : 6 ≤ 7) (hNbound i) early
    rw [hrecip] at hup
    exact ⟨K, hlo, hup, δ, hδm, pure_blockade_directed G δ hpure hτ0.le⟩
  · have hNboundA : N ≤ (m : ℝ) ^ 7 * A.card := by
      have hZi : ((Z.get i).card : ℝ) ≤ A.card * m := (div_le_iff₀ hm0).mp hAc
      calc
        N ≤ (m : ℝ) ^ 6 * (Z.get i).card := hNbound i
        _ ≤ (m : ℝ) ^ 6 * (A.card * m) := mul_le_mul_of_nonneg_left hZi (by positivity)
        _ = (m : ℝ) ^ 7 * A.card := by ring
    have hAY := hAZ.trans (((ordered_frontier_properties G U hfront).1 _ (List.get_mem Z i)).trans hSY)
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

#print axioms pure_blockade_directed
#print axioms sqrt_frontier_length_bounds
#print axioms paper_parameter_reciprocal_bounds
#print axioms quantitative_frontier

end Quantitative

end AllPathsLocal
