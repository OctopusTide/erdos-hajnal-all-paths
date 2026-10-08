import RP5OrderedLayers

namespace AllPathsLocal

noncomputable def positiveBlocks {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (P : List (RootCutStage G)) :
    List (Finset V) := by
  classical
  exact (P.filter (fun a => (positiveLayer s a).Nonempty)).map (positiveLayer s)

theorem actual_positive_blocks_properties {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u) :
    (∀ K ∈ positiveBlocks s P, K ⊆ Y ∧ K.Nonempty) ∧
    (positiveBlocks s P).Pairwise (fun A B => Disjoint A B ∧
      (∀ v ∈ B, RootedP4Free G A v) ∧ ∃ u ∈ U, RootSeparates G u A B) := by
  classical
  constructor
  · intro K hK
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hK
    have hm := List.mem_filter.mp ha
    exact ⟨(positive_layer_subset_source s a).trans
      ((actual_path_subsets_and_roots hP a hm.1).1.trans hSY), by simpa using hm.2⟩
  · apply List.pairwise_map.mpr
    have h := (actual_positive_layer_laws hP hSY hout hfree).sublist
      (show (P.filter (fun a => (positiveLayer s a).Nonempty)).Sublist P from List.filter_sublist)
    apply List.Pairwise.imp_of_mem ?_ h
    intro a b ha hb hab
    exact hab (by simpa using (List.mem_filter.mp ha).2)

/-- Any vertex in a negative layer cannot be an endpoint of a complement P4
    whose other three vertices lie in later negative layers. This is the actual
    root-prefix obstruction required before the transversal perfection step. -/
theorem actual_negative_endpoint_obstruction {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P R : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (a : RootCutStage G) (hsub : (a :: R).Sublist P)
    (v : V) (hv : v ∈ negativeLayer s a) :
    RootedP4Free G ((R.map (negativeLayer s)).toFinset.biUnion id) v := by
  classical
  have hneg : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut := by
    by_contra h
    simpa [negativeLayer, h] using hv
  have hvA : v ∈ a.cut.A := by simpa only [negativeLayer, if_pos hneg] using hv
  have ha : a ∈ P := hsub.subset (List.mem_cons_self)
  have hu := (actual_path_subsets_and_roots hP a ha).2
  have hforward := (List.pairwise_cons.mp ((actual_path_forward_laws hP).sublist hsub)).1
  have htailY : ((R.map (negativeLayer s)).toFinset.biUnion id) ⊆ Y := by
    intro w hw
    obtain ⟨K, hK, hwK⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    have hbP : b ∈ P := hsub.subset (List.mem_cons_of_mem a hb)
    exact hSY ((actual_path_subsets_and_roots hP b hbP).1 (negative_layer_subset_source s b hwK))
  have hanti : ¬ G.Adj a.u v := by
    rw [a.cut.remainder] at hvA
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
    intro huv
    exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)
  have hfull : ∀ w ∈ ((R.map (negativeLayer s)).toFinset.biUnion id), G.Adj a.u w := by
    intro w hw
    obtain ⟨K, hK, hwK⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    exact (hforward b hb).2.2.2 hneg.1 hneg.2 w (negative_layer_subset_source s b hwK)
  exact rp5_to_rp4 G (hout a.u hu)
    (hSY ((actual_path_subsets_and_roots hP a ha).1 (negative_layer_subset_source s a hv)))
    htailY (hfree a.u hu) hanti hfull

#print axioms actual_positive_blocks_properties
#print axioms actual_negative_endpoint_obstruction

end AllPathsLocal
