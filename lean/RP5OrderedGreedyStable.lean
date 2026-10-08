import RP5OrderedCliqueWitness

namespace AllPathsLocal

noncomputable def orderedGreedyStable {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V) : Finset V :=
  if h : S.Nonempty then
    insert (S.min' h) (orderedGreedyStable H (containerNext H S (S.min' h)))
  else ∅
termination_by S.card
decreasing_by exact container_next_strict H S _ (Finset.min'_mem S _)

structure OrderedStableProperties {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (S I : Finset V) : Prop where
  subset : I ⊆ S
  stable : ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v
  nonempty : S.Nonempty → I.Nonempty
  dominates : ∀ w ∈ S, w ∉ I → ∃ v ∈ I, v < w ∧ H.Adj v w

/-- The actual ordered greedy stable set and its earlier-neighbour domination.
    The choice is the minimum available vertex, not the max-degree container
    choice used in the independent thin-layer counting proof. -/
theorem ordered_greedy_stable_properties {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V) :
    OrderedStableProperties H S (orderedGreedyStable H S) := by
  classical
  by_cases hS : S.Nonempty
  · rw [orderedGreedyStable, dif_pos hS]
    let v := S.min' hS
    let J := orderedGreedyStable H (containerNext H S v)
    change OrderedStableProperties H S (insert v J)
    have hv : v ∈ S := Finset.min'_mem S hS
    have ih := ordered_greedy_stable_properties H (containerNext H S v)
    have hJS : J ⊆ S := ih.subset.trans (container_next_subset H S v)
    have hanti : ∀ w ∈ J, ¬ H.Adj v w := by
      intro w hw
      exact (Finset.mem_filter.mp (ih.subset hw)).2.2
    constructor
    · exact Finset.insert_subset hv hJS
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact H.irrefl
        · exact hanti b hb
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact fun he => hanti a ha (H.adj_symm he)
        · exact ih.stable a ha b hb
    · intro _
      exact ⟨v, Finset.mem_insert_self _ _⟩
    · intro w hw hn
      have hwv : w ≠ v := by intro he; subst w; exact hn (Finset.mem_insert_self _ _)
      by_cases hwn : w ∈ containerNext H S v
      · have hwnJ : w ∉ J := fun hh => hn (Finset.mem_insert_of_mem hh)
        obtain ⟨a, ha, haw, hadj⟩ := ih.dominates w hwn hwnJ
        exact ⟨a, Finset.mem_insert_of_mem ha, haw, hadj⟩
      · have hadj : H.Adj v w := by
          by_contra hnot
          exact hwn (Finset.mem_filter.mpr ⟨hw, hwv, hnot⟩)
        exact ⟨v, Finset.mem_insert_self _ _,
          lt_of_le_of_ne (Finset.min'_le S w hw) hwv.symm, hadj⟩
  · have hSEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [orderedGreedyStable, dif_neg (by simp)]
    constructor <;> simp
termination_by S.card
decreasing_by exact container_next_strict H S _ (Finset.min'_mem S _)

#print axioms ordered_greedy_stable_properties
end AllPathsLocal
