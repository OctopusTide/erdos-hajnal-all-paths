import RP5RetainedTree

namespace AllPathsLocal

open scoped BigOperators

theorem root_cut_remainder_not_component {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : cut.A ∉ cut.C := by
  intro h
  obtain ⟨v, hv⟩ := cut.nonemptyA
  exact Finset.disjoint_left.mp (cut.disjointA cut.A h) hv hv

theorem component_frontier_length_sum {V : Type} [DecidableEq V]
    (C : Finset (Finset V)) (F : Finset V → List (Finset V)) :
    ((orderedComponentLists C (fun K _ => F K)).flatten).length = ∑ K ∈ C, (F K).length := by
  classical
  simp only [orderedComponentLists, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  exact sum_fin_equivFin C (fun K => (F K).length)

/-- Terminal retained nodes form an ACTUAL ordered cut frontier. Its length equals
    the weighted tree's terminal count, and every block has size at least s. -/
theorem retained_terminal_frontier {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S) :
    ∃ Z : List (Finset V), OrderedCutFrontier G U S Z ∧
      (∀ K ∈ Z, s ≤ (K.card : ℝ)) ∧ Z.length = treeLeafCount T.toWeighted := by
  classical
  induction T with
  | node S u hu large degree cut below ih =>
    let L := retainedCutChildren s cut
    by_cases hn : L.card = 0
    · refine ⟨[S], OrderedCutFrontier.stop S, ?_, ?_⟩
      · intro K hK
        simpa using (List.mem_singleton.mp hK) ▸ large
      · simp [RetainedCutTree.toWeighted, treeLeafCount, L, hn]
    choose P hP hsize hlength using ih
    let F : Finset V → List (Finset V) := fun K => if hK : K ∈ L then P K hK else []
    have hF : ∀ K ∈ cutChildren cut, OrderedCutFrontier G U K (F K) := by
      intro K _
      by_cases hK : K ∈ L
      · simpa only [F, dif_pos hK] using hP K hK
      · simpa only [F, dif_neg hK] using OrderedCutFrontier.skip (G := G) (U := U) K
    have hFsize : ∀ K, ∀ B ∈ F K, s ≤ (B.card : ℝ) := by
      intro K B hB
      by_cases hK : K ∈ L
      · exact hsize K hK B (by simpa only [F, dif_pos hK] using hB)
      · simp only [F, dif_neg hK, List.not_mem_nil] at hB
    let Z := (orderedComponentLists cut.C (fun K _ => F K)).flatten ++ F cut.A
    refine ⟨Z, OrderedCutFrontier.split S u hu cut (fun K _ => F K) (F cut.A)
      (fun K hK => hF K (Finset.mem_insert_of_mem hK))
      (hF cut.A (Finset.mem_insert_self _ _)), ?_, ?_⟩
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · obtain ⟨A, hA, hBA⟩ := List.mem_flatten.mp hB
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
        exact hFsize _ B hBA
      · exact hFsize _ B hB
    · have hsumall : (∑ K ∈ cutChildren cut, (F K).length) =
          (∑ K ∈ cut.C, (F K).length) + (F cut.A).length := by
        rw [cutChildren, Finset.sum_insert (root_cut_remainder_not_component cut)]
        omega
      have hLsub : L ⊆ cutChildren cut := Finset.filter_subset _ _
      have hsumL : (∑ K ∈ cutChildren cut, (F K).length) = ∑ K ∈ L, (F K).length := by
        symm
        apply Finset.sum_subset hLsub
        intro K _ hK
        simp only [F, dif_neg hK, List.length_nil]
      have hreindex : (∑ i : Fin L.card,
          treeLeafCount ((below (L.equivFin.symm i).val (L.equivFin.symm i).prop).toWeighted)) =
          ∑ K ∈ L, (F K).length := by
        calc
          _ = ∑ i : Fin L.card, (F (L.equivFin.symm i).val).length := by
            apply Finset.sum_congr rfl
            intro i _
            simpa only [F, dif_pos (L.equivFin.symm i).prop] using
              (hlength (L.equivFin.symm i).val (L.equivFin.symm i).prop).symm
          _ = ∑ K ∈ L, (F K).length := sum_fin_equivFin L (fun K => (F K).length)
      change Z.length = if L.card = 0 then 1 else _
      rw [if_neg hn, hreindex]
      dsimp only [Z]
      rw [List.length_append]
      rw [component_frontier_length_sum, ← hsumall, hsumL]

#print axioms root_cut_remainder_not_component
#print axioms component_frontier_length_sum
#print axioms retained_terminal_frontier

end AllPathsLocal
