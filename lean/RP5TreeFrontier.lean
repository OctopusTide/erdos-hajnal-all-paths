import RP5CutTree
import RP5Frontier

/-! Connect the constructed finite rooted-cut tree to an ordered terminal frontier,
    with exact set coverage and explicit stopping conditions. -/

namespace AllPathsLocal

theorem cut_tree_terminal_frontier {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ)
    {S : Finset V} (tree : CutTree G U x s S) :
    ∃ Z : List (Finset V), OrderedCutFrontier G U S Z ∧
      (∀ K ∈ Z, (K.card : ℝ) < s ∨ FullOrSmall G U x K) ∧
      Z.toFinset.biUnion id = S := by
  classical
  induction tree with
  | leaf S stop =>
    refine ⟨[S], OrderedCutFrontier.stop S, ?_, ?_⟩
    · intro K hK
      simpa using (List.mem_singleton.mp hK) ▸ stop
    · simp
  | split S u hu hlarge hdegree cut belowC belowA ihC ihA =>
    choose F hF hstop hcover using ihC
    obtain ⟨A, hA, hAstop, hAcover⟩ := ihA
    let Z := (orderedComponentLists cut.C F).flatten ++ A
    have hfront : OrderedCutFrontier G U S Z :=
      OrderedCutFrontier.split S u hu cut F A hF hA
    have hsource : ∀ X ∈ (orderedComponentLists cut.C F).flatten,
        ∃ K, ∃ hK : K ∈ cut.C, X ∈ F K hK := by
      intro X hX
      obtain ⟨L, hL, hXL⟩ := List.mem_flatten.mp hX
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
      exact ⟨(cut.C.equivFin.symm i).val, (cut.C.equivFin.symm i).prop, hXL⟩
    refine ⟨Z, hfront, ?_, ?_⟩
    · intro K hK
      rcases List.mem_append.mp hK with hK | hK
      · obtain ⟨L, hL, hKL⟩ := hsource K hK
        exact hstop L hL K hKL
      · exact hAstop K hK
    · apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
        exact (ordered_frontier_properties G U hfront).1 K (List.mem_toFinset.mp hK) hvK
      · intro v hvS
        rw [← cut.cover] at hvS
        rcases Finset.mem_union.mp hvS with hvC | hvA
        · obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hvC
          rw [← hcover K hK] at hvK
          obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp hvK
          have hFL : F K hK ∈ orderedComponentLists cut.C F := by
            apply List.mem_ofFn.mpr
            refine ⟨cut.C.equivFin ⟨K, hK⟩, ?_⟩
            simp
          have hLZ : L ∈ Z := List.mem_append_left A
            (List.mem_flatten.mpr ⟨F K hK, hFL, List.mem_toFinset.mp hL⟩)
          exact Finset.mem_biUnion.mpr ⟨L, List.mem_toFinset.mpr hLZ, hvL⟩
        · rw [← hAcover] at hvA
          obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hvA
          have hKZ : K ∈ Z := List.mem_append_right _ (List.mem_toFinset.mp hK)
          exact Finset.mem_biUnion.mpr ⟨K, List.mem_toFinset.mpr hKZ, hvK⟩

/-- If no large clean outcome has occurred anywhere, terminal leaves are precisely
    small atoms partitioning the original set, in a valid ordered frontier. -/
theorem small_terminal_frontier_of_no_clean {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ)
    {S : Finset V} (tree : CutTree G U x s S)
    (hno : ∀ K ⊆ S, s ≤ (K.card : ℝ) → ¬ FullOrSmall G U x K) :
    ∃ Z : List (Finset V), OrderedCutFrontier G U S Z ∧
      (∀ K ∈ Z, (K.card : ℝ) < s) ∧ Z.toFinset.biUnion id = S := by
  obtain ⟨Z, hfront, hstop, hcover⟩ := cut_tree_terminal_frontier G U x s tree
  refine ⟨Z, hfront, ?_, hcover⟩
  intro K hK
  rcases hstop K hK with hsmall | hclean
  · exact hsmall
  · by_contra! hlarge
    exact hno K ((ordered_frontier_properties G U hfront).1 K hK) hlarge hclean

#print axioms cut_tree_terminal_frontier
#print axioms small_terminal_frontier_of_no_clean

end AllPathsLocal
