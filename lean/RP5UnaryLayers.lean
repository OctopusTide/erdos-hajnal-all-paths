import RP5LabelledPath

namespace AllPathsLocal

theorem root_cut_components_cover_neighbors {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : cut.C.biUnion id = EHP6.nbrs G u S := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
    exact (cut.component K hK).1 hvK
  · intro v hv
    have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
    rw [← cut.cover] at hvS
    rcases Finset.mem_union.mp hvS with h | h
    · exact h
    · rw [cut.remainder] at h
      exact False.elim ((Finset.mem_sdiff.mp h).2 hv)

theorem unary_retained_child_unique {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) (hn : (retainedCutChildren s cut).card = 1)
    {K : Finset V} (hK : K ∈ retainedCutChildren s cut) :
    ∀ L ∈ retainedCutChildren s cut, L = K := by
  classical
  obtain ⟨A, hA⟩ := Finset.card_eq_one.mp hn
  rw [hA] at hK ⊢
  have hKA := Finset.mem_singleton.mp hK
  intro L hL
  exact (Finset.mem_singleton.mp hL).trans hKA.symm

/-- A unary cut continuing into A has exactly the entire root neighborhood as
    its positive atom layer; every original C child is small. -/
theorem unary_positive_layer {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) (hn : (retainedCutChildren s cut).card = 1)
    (hA : cut.A ∈ retainedCutChildren s cut) :
    cutAtoms s cut = EHP6.nbrs G u S ∧
      (∀ K ∈ cut.C, (K.card : ℝ) < s) ∧
      (∀ v ∈ cutAtoms s cut, G.Adj u v) ∧
      (∀ v ∈ cut.A, ¬ G.Adj u v) := by
  classical
  have hAsize : s ≤ (cut.A.card : ℝ) := (Finset.mem_filter.mp hA).2
  have hsmall : ∀ K ∈ cut.C, (K.card : ℝ) < s := by
    intro K hK
    by_contra! hlarge
    have hret : K ∈ retainedCutChildren s cut :=
      Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hK, hlarge⟩
    have heq := unary_retained_child_unique s cut hn hA K hret
    exact root_cut_remainder_not_component cut (heq ▸ hK)
  have hC : smallCutComponents s cut = cut.C := by
    ext K
    simp only [smallCutComponents, Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hsmall K h⟩⟩
  have hatoms : cutAtoms s cut = EHP6.nbrs G u S := by
    rw [cut_atoms_component_decomposition, hC,
      if_neg (not_lt_of_ge hAsize), Finset.union_empty, root_cut_components_cover_neighbors]
  refine ⟨hatoms, hsmall, ?_, ?_⟩
  · intro v hv
    rw [hatoms] at hv
    exact (Finset.mem_filter.mp hv).2
  · intro v hv huv
    rw [cut.remainder] at hv
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hv
    exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)

/-- A unary cut continuing into C has a small A negative layer, a unique large
    component, and only small other components. The root is anti to A and full
    to the continuation component. -/
theorem unary_negative_layer {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) (hn : (retainedCutChildren s cut).card = 1)
    (hA : cut.A ∉ retainedCutChildren s cut) :
    (cut.A.card : ℝ) < s ∧ ∃ K ∈ cut.C,
      s ≤ (K.card : ℝ) ∧ (∀ L ∈ cut.C, L ≠ K → (L.card : ℝ) < s) ∧
      (∀ v ∈ cut.A, ¬ G.Adj u v) ∧ (∀ v ∈ K, G.Adj u v) := by
  classical
  have hAsmall : (cut.A.card : ℝ) < s := by
    by_contra! hlarge
    exact hA (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hlarge⟩)
  obtain ⟨K, hK⟩ := Finset.card_pos.mp (show 0 < (retainedCutChildren s cut).card by omega)
  have hm := Finset.mem_filter.mp hK
  have hKC : K ∈ cut.C := by
    rcases Finset.mem_insert.mp hm.1 with heq | hKC
    · exact False.elim (hA (heq ▸ hK))
    · exact hKC
  refine ⟨hAsmall, K, hKC, hm.2, ?_, ?_, ?_⟩
  · intro L hL hLK
    by_contra! hlarge
    exact hLK (unary_retained_child_unique s cut hn hK L
      (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hL, hlarge⟩))
  · intro v hv huv
    rw [cut.remainder] at hv
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hv
    exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)
  · intro v hv
    exact (Finset.mem_filter.mp ((cut.component K hKC).1 hv)).2

#print axioms root_cut_components_cover_neighbors
#print axioms unary_retained_child_unique
#print axioms unary_positive_layer
#print axioms unary_negative_layer

end AllPathsLocal
