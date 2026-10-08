import RP5FrontierMass
import RP5Grouping

namespace AllPathsLocal

noncomputable def smallCutComponents {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) : Finset (Finset V) := by
  classical
  exact cut.C.filter (fun K => (K.card : ℝ) < s)

theorem small_components_mass_or_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S Y : Finset V} {u : V}
    (cut : RootCut G S u) (hSY : S ⊆ Y) (s : ℝ) (t : ℕ) (ht : 2 ≤ t) :
    (((smallCutComponents s cut).biUnion id).card : ℝ) < t * s ∨
    ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G := by
  classical
  let C := smallCutComponents s cut
  let D := C.biUnion id
  by_cases h : (D.card : ℝ) < t * s
  · exact Or.inl h
  right
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hmass : (t : ℝ) * s ≤ D.card := le_of_not_gt h
  have hsD : s ≤ (D.card : ℝ) / t := (le_div_iff₀ ht0).mpr (by nlinarith)
  have hsmall : ∀ A ∈ C, (A.card : ℝ) < (D.card : ℝ) / t := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2.trans_le hsD
  have hcomplete : ∀ A ∈ C, ∀ B ∈ C, A ≠ B → EHP6.Complete G A B := by
    intro A hA B hB hAB
    exact cut.completeC A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hAB
  obtain ⟨β, hm, hβ⟩ := complete_small_atoms_grouping G D C t ht rfl hcomplete hsmall
  have hDY : D ⊆ Y := by
    intro v hv
    obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hv
    exact hSY ((cut.properC A (Finset.mem_filter.mp hA).1).subset hvA)
  have hwidth : s / (t : ℝ) ≤ (D.card : ℝ) / (t : ℝ)^2 := by
    apply (div_le_div_iff₀ ht0 (sq_pos_of_pos ht0)).mpr
    nlinarith
  exact ⟨β.mono hDY le_rfl hwidth, hm, hβ⟩

theorem cut_atoms_component_decomposition {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) :
    cutAtoms s cut = (smallCutComponents s cut).biUnion id ∪
      (if (cut.A.card : ℝ) < s then cut.A else ∅) := by
  classical
  ext v
  simp only [cutAtoms, smallCutChildren, cutChildren, smallCutComponents,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert, id_eq]
  by_cases hA : (cut.A.card : ℝ) < s
  · simp only [hA, ite_true, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨K, ⟨rfl | hK, hsize⟩, hv⟩
      · exact Or.inr hv
      · exact Or.inl ⟨K, ⟨hK, hsize⟩, hv⟩
    · rintro (⟨K, hK, hv⟩ | hv)
      · exact ⟨K, ⟨Or.inr hK.1, hK.2⟩, hv⟩
      · exact ⟨cut.A, ⟨Or.inl rfl, hA⟩, hv⟩
  · simp only [hA, ite_false, Finset.union_empty, Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · rintro ⟨K, ⟨rfl | hK, hsize⟩, hv⟩
      · exact False.elim (hA hsize)
      · exact ⟨K, ⟨hK, hsize⟩, hv⟩
    · rintro ⟨K, hK, hv⟩
      exact ⟨K, ⟨Or.inr hK.1, hK.2⟩, hv⟩

theorem cut_atom_budget {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S Y : Finset V} {u : V}
    (cut : RootCut G S u) (hSY : S ⊆ Y) (s : ℝ) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ((cutAtoms s cut).card : ℝ) ≤ (t + 1) * s := by
  classical
  have hmass : (((smallCutComponents s cut).biUnion id).card : ℝ) < t * s := by
    rcases small_components_mass_or_complete G cut hSY s t ht with h | h
    · exact h
    · exact False.elim (hno h)
  rw [cut_atoms_component_decomposition]
  have hcard := Finset.card_union_le ((smallCutComponents s cut).biUnion id)
    (if (cut.A.card : ℝ) < s then cut.A else ∅)
  have hcardR : ((((smallCutComponents s cut).biUnion id) ∪
      (if (cut.A.card : ℝ) < s then cut.A else ∅)).card : ℝ) ≤
      ((smallCutComponents s cut).biUnion id).card +
      ((if (cut.A.card : ℝ) < s then cut.A else ∅).card : ℝ) := by exact_mod_cast hcard
  have hA : ((if (cut.A.card : ℝ) < s then cut.A else ∅).card : ℝ) ≤ s := by
    split
    · exact le_of_lt ‹_›
    · simpa using hs
  nlinarith

#print axioms small_components_mass_or_complete
#print axioms cut_atoms_component_decomposition
#print axioms cut_atom_budget

end AllPathsLocal
