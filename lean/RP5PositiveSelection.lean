import RP5OrderedSelection
import RP5PositiveBounds
import RP5SeparatedQuantitative

namespace AllPathsLocal

theorem actual_positive_size_selection {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (t : ℕ) (ht : 16 ≤ t) (hN : 0 < (S.card : ℝ))
    (hscale : s = (S.card : ℝ) / (t : ℝ)^6)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G)
    (hmass : 3 * (S.card : ℝ) / (8 * t) ≤
      (P.map (fun a => ((positiveLayer s a).card : ℝ))).sum) :
    ∃ (m : ℕ) (Z : List (Finset V)), t ≤ m ∧ m ≤ (positiveBlocks s P).length ∧
      Z.Sublist (positiveBlocks s P) ∧ Z.length = m ∧
      ∀ K ∈ Z, (S.card : ℝ) / (m : ℝ)^3 ≤ (K.card : ℝ) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsmall : ∀ K ∈ positiveBlocks s P, (K.card : ℝ) ≤ (S.card : ℝ) / (t : ℝ)^5 := by
    intro K hK
    have h := (actual_positive_blocks_upper hP hSY t (by omega) hno K hK).le
    rw [hscale] at h
    have he : (t : ℝ) * ((S.card : ℝ) / (t : ℝ)^6) = (S.card : ℝ) / (t : ℝ)^5 := by field_simp
    simpa only [he] using h
  rw [← positive_blocks_mass_identity] at hmass
  exact ordered_size_selection (positiveBlocks s P) t (S.card : ℝ) ht hN hsmall hmass

/-- The selected positive layers carry the generic quantitative pipeline's
    actual graph premises. This constructs root separation on the final order. -/
theorem selected_positive_quantitative {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    {Z : List (Finset V)} (hZ : Z.Sublist (positiveBlocks s P))
    (hm : 2^16 ≤ Z.length) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1)
    (horder : 16 / (τ / (64 * (Z.length : ℝ)^5))^3 ≤ (S.card : ℝ) / (Z.length : ℝ)^6)
    (hwidth : ∀ K ∈ Z, (S.card : ℝ) / (Z.length : ℝ)^3 ≤ (K.card : ℝ)) :
    ∃ K : ℕ, (Z.length : ℝ) ≤ (K : ℝ)^4 ∧ (K : ℝ) ≤ 64 * (Z.length : ℝ)^5 / τ ∧
      ∃ γ : EHP6.Blockade Y K ((S.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G τ (γ.B j) (γ.B i) := by
  have hprops := actual_positive_blocks_properties hP hSY hout hfree
  have hpair := hprops.2.sublist hZ
  have hsub : ∀ K ∈ Z, K ⊆ Y := fun K hK => (hprops.1 K (hZ.subset hK)).1
  have hroot : Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v) :=
    hpair.imp (fun h => ⟨h.1, h.2.1⟩)
  have hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j) := by
    intro i j hij
    exact (List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hpair hij).2.2
  have hm1 : (1 : ℝ) ≤ Z.length := by exact_mod_cast (show 1 ≤ Z.length by omega)
  have hpow : (Z.length : ℝ)^3 ≤ (Z.length : ℝ)^6 := pow_le_pow_right₀ hm1 (by decide)
  have hwidth6 : ∀ i : Fin Z.length, (S.card : ℝ) / (Z.length : ℝ)^6 ≤ ((Z.get i).card : ℝ) := by
    intro i
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg S.card) (by positivity : (0 : ℝ) < (Z.length : ℝ)^3) hpow
    exact hh.trans (hwidth _ (List.get_mem Z i))
  exact quantitative_separated_family G U Y hsub hroot hseparator hout hfree hm hτ0 hτ
    (Nat.cast_nonneg _) horder hwidth6

#print axioms actual_positive_size_selection
#print axioms selected_positive_quantitative

end AllPathsLocal
