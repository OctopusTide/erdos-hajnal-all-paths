import RP5LayerInterfaces

namespace AllPathsLocal

theorem actual_path_stage_degree_size {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) : ∀ a ∈ P, s ≤ (a.S.card : ℝ) ∧
      x * a.S.card / 4 ≤ ((EHP6.nbrs G a.u a.S).card : ℝ) := by
  induction hP with
  | terminal S u hu large degree cut below hn =>
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨large, degree⟩
  | step S u hu large degree cut below K hK path ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨large, degree⟩
    · exact ih a ha

theorem positive_layer_nonempty_classification {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G)
    (h : (positiveLayer s a).Nonempty) :
    (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∈ retainedCutChildren s a.cut := by
  classical
  obtain ⟨v, hv⟩ := h
  by_contra hn
  simpa [positiveLayer, hn] using hv

theorem actual_positive_blocks_lower {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hx : 0 ≤ x) :
    ∀ K ∈ positiveBlocks s P, x * s / 4 ≤ (K.card : ℝ) := by
  classical
  intro K hK
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hK
  have hm := List.mem_filter.mp ha
  have hn : (positiveLayer s a).Nonempty := by simpa using hm.2
  have hpos := positive_layer_nonempty_classification s a hn
  obtain ⟨hlarge, hdegree⟩ := actual_path_stage_degree_size hP a hm.1
  have hxlarge := mul_le_mul_of_nonneg_left hlarge hx
  simp only [positiveLayer, if_pos hpos]
  nlinarith

theorem actual_positive_blocks_upper {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y) (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∀ K ∈ positiveBlocks s P, (K.card : ℝ) < t * s := by
  classical
  intro K hK
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hK
  have hm := List.mem_filter.mp ha
  have hn : (positiveLayer s a).Nonempty := by simpa using hm.2
  have hpos := positive_layer_nonempty_classification s a hn
  have hsmall := (unary_positive_layer s a.cut hpos.1 hpos.2).2.1
  have hC : smallCutComponents s a.cut = a.cut.C := by
    ext L
    simp only [smallCutComponents, Finset.mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, hsmall L h⟩⟩
  have haY := (actual_path_subsets_and_roots hP a hm.1).1.trans hSY
  have hmass : (((smallCutComponents s a.cut).biUnion id).card : ℝ) < t * s := by
    rcases small_components_mass_or_complete G a.cut haY s t ht with h | h
    · exact h
    · exact False.elim (hno h)
  simpa only [positiveLayer, if_pos hpos, hC, root_cut_components_cover_neighbors] using hmass

theorem positive_blocks_mass_identity {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (P : List (RootCutStage G)) :
    ((positiveBlocks s P).map (fun K => (K.card : ℝ))).sum =
      (P.map (fun a => ((positiveLayer s a).card : ℝ))).sum := by
  classical
  induction P with
  | nil => simp [positiveBlocks]
  | cons a P ih =>
    by_cases h : (positiveLayer s a).Nonempty
    · simpa only [positiveBlocks, List.filter_cons, decide_eq_true h, ite_true,
        List.map_cons, List.map_map, Function.comp_def, List.sum_cons] using congrArg
          (fun z : ℝ => ((positiveLayer s a).card : ℝ) + z) ih
    · have he : positiveLayer s a = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simpa [positiveBlocks, he] using ih

#print axioms actual_path_stage_degree_size
#print axioms positive_layer_nonempty_classification
#print axioms actual_positive_blocks_lower
#print axioms actual_positive_blocks_upper
#print axioms positive_blocks_mass_identity

end AllPathsLocal
