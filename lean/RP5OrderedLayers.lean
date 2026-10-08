import RP5DirectionalMass

namespace AllPathsLocal

theorem positive_layer_subset_atoms {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    positiveLayer s a ⊆ cutAtoms s a.cut := by
  classical
  unfold positiveLayer
  split
  · rename_i h
    rw [(unary_positive_layer s a.cut h.1 h.2).1]
  · exact Finset.empty_subset _

theorem negative_layer_subset_source {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    negativeLayer s a ⊆ a.S := by
  classical
  unfold negativeLayer
  split
  · exact a.cut.properA.subset
  · exact Finset.empty_subset _

theorem positive_layer_subset_source {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    positiveLayer s a ⊆ a.S := by
  classical
  unfold positiveLayer
  split
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

/-- Positive layers inherit the same one-sided endpoint-P4 law as a tree
    frontier, with actual roots separating every pair, even complete pairs. -/
theorem actual_positive_layer_laws {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u) :
    P.Pairwise (fun a b => (positiveLayer s a).Nonempty →
      Disjoint (positiveLayer s a) (positiveLayer s b) ∧
      (∀ v ∈ positiveLayer s b, RootedP4Free G (positiveLayer s a) v) ∧ ∃ u ∈ U,
        RootSeparates G u (positiveLayer s a) (positiveLayer s b)) := by
  classical
  apply List.Pairwise.imp_of_mem ?_ (actual_path_forward_laws hP)
  intro a b ha hb hab
  have haY := (actual_path_subsets_and_roots hP a ha).1.trans hSY
  have hbY := (actual_path_subsets_and_roots hP b hb).1.trans hSY
  have hu := (actual_path_subsets_and_roots hP a ha).2
  have hdis := hab.2.1.mono (positive_layer_subset_atoms s a) (positive_layer_subset_source s b)
  intro hnonempty
  obtain ⟨v, hv⟩ := hnonempty
  have hpos : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∈ retainedCutChildren s a.cut := by
    by_contra h
    simpa [positiveLayer, h] using hv
  have hfull : ∀ v ∈ positiveLayer s a, G.Adj a.u v := by
    intro v hv
    have hvN : v ∈ EHP6.nbrs G a.u a.S := by simpa only [positiveLayer, if_pos hpos] using hv
    exact (Finset.mem_filter.mp hvN).2
  have hanti : ∀ v ∈ positiveLayer s b, ¬ G.Adj a.u v := by
    intro v hv
    exact hab.2.2.1 hpos.1 hpos.2 v (positive_layer_subset_source s b hv)
  refine ⟨hdis, ?_, a.u, hu, hfull, hanti⟩
  intro v hv
  exact rp5_to_rp4 G (hout a.u hu) (hbY (positive_layer_subset_source s b hv))
    ((positive_layer_subset_source s a).trans haY) (hfree a.u hu) (hanti v hv) hfull

#print axioms positive_layer_subset_atoms
#print axioms negative_layer_subset_source
#print axioms positive_layer_subset_source
#print axioms actual_positive_layer_laws

end AllPathsLocal
