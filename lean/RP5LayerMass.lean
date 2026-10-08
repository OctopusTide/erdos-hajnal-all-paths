import RP5NegativeFringe

namespace AllPathsLocal

noncomputable def positiveLayer {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) : Finset V := by
  classical
  exact if (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∈ retainedCutChildren s a.cut
    then EHP6.nbrs G a.u a.S else ∅

noncomputable def negativeLayer {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) : Finset V := by
  classical
  exact if (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut
    then a.cut.A else ∅

noncomputable def fringeLayer {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) : Finset V := by
  classical
  exact if (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut
    then (smallCutComponents s a.cut).biUnion id else ∅

theorem fringe_layer_subset_atoms {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    fringeLayer s a ⊆ cutAtoms s a.cut := by
  classical
  unfold fringeLayer
  split
  · intro v hv
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
    have hm := Finset.mem_filter.mp hK
    exact Finset.mem_biUnion.mpr ⟨K,
      Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hm.1, hm.2⟩, hvK⟩
  · exact Finset.empty_subset _

theorem unary_stage_layer_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    (if (retainedCutChildren s a.cut).card = 1 then ((cutAtoms s a.cut).card : ℝ) else 0) =
      (positiveLayer s a).card + (negativeLayer s a).card + (fringeLayer s a).card := by
  classical
  by_cases hn : (retainedCutChildren s a.cut).card = 1
  · by_cases hA : a.cut.A ∈ retainedCutChildren s a.cut
    · have hpos := (unary_positive_layer s a.cut hn hA).1
      simp [positiveLayer, negativeLayer, fringeLayer, hn, hA, hpos]
    · have hsmall := (unary_negative_layer s a.cut hn hA).1
      have hdis : Disjoint ((smallCutComponents s a.cut).biUnion id) a.cut.A := by
        apply Finset.disjoint_left.mpr
        intro v hv hvA
        obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
        exact Finset.disjoint_left.mp (a.cut.disjointA K (Finset.mem_filter.mp hK).1) hvK hvA
      rw [if_pos hn, cut_atoms_component_decomposition, if_pos hsmall,
        Finset.card_union_of_disjoint hdis]
      simp only [positiveLayer, negativeLayer, fringeLayer, hn, hA, and_true, and_false,
        not_false_eq_true, ite_true, ite_false, Finset.card_empty, Nat.cast_zero, Nat.cast_add]
      ring
  · simp [positiveLayer, negativeLayer, fringeLayer, hn]

theorem unary_path_layer_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (P : List (RootCutStage G)) :
    unaryPathMass (P.map (RootCutStage.weight s)) =
      (P.map (fun a => ((positiveLayer s a).card : ℝ))).sum +
      (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum +
      (P.map (fun a => ((fringeLayer s a).card : ℝ))).sum := by
  induction P with
  | nil => simp [unaryPathMass]
  | cons a P ih =>
    simp only [List.map_cons, unaryPathMass, RootCutStage.weight, List.sum_cons] at ih ⊢
    rw [unary_stage_layer_mass]
    linarith

theorem fringe_union_identity {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (P : List (RootCutStage G)) :
    (P.map (fringeLayer s)).toFinset.biUnion id = (negativeFringes s P).biUnion id := by
  classical
  induction P with
  | nil => simp [negativeFringes]
  | cons a P ih =>
    by_cases h : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut
    · simp only [List.map_cons, List.toFinset_cons, Finset.biUnion_insert, id_eq, ih,
        negativeFringes, fringeLayer, if_pos h, Finset.union_biUnion]
    · simp only [List.map_cons, List.toFinset_cons, Finset.biUnion_insert, id_eq, ih,
        negativeFringes, fringeLayer, if_neg h, Finset.empty_union]

theorem actual_fringe_card_sum {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    (((negativeFringes s P).biUnion id).card : ℝ) =
      (P.map (fun a => ((fringeLayer s a).card : ℝ))).sum := by
  classical
  have hpair : (P.map (fringeLayer s)).Pairwise Disjoint := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp ?_ (List.pairwise_map.mp (actual_path_atoms_pairwise_disjoint hP))
    intro a b hab
    exact hab.mono (fringe_layer_subset_atoms s a) (fringe_layer_subset_atoms s b)
  have h := disjoint_list_card_mass (P.map (fringeLayer s)) hpair
  rw [fringe_union_identity] at h
  have hcast : (((P.map (fun a => (fringeLayer s a).card)).sum : ℕ) : ℝ) =
      (P.map (fun a => ((fringeLayer s a).card : ℝ))).sum := by
    clear hP hpair h
    induction P with
    | nil => simp
    | cons a P ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [List.map_map, Function.comp_def, hcast] using hc

#print axioms fringe_layer_subset_atoms
#print axioms unary_stage_layer_mass
#print axioms unary_path_layer_mass
#print axioms fringe_union_identity
#print axioms actual_fringe_card_sum

end AllPathsLocal
