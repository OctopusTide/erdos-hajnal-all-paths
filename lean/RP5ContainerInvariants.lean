import RP5ContainerAlgorithm

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- Recorded vertices really belong to the encoded set, final candidates belong
    to the input, and no recorded vertex remains in the final container. -/
theorem container_run_subsets {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (u : ℕ) :
    (containerRun G I R u).1 ⊆ I ∧
    (containerRun G I R u).1 ⊆ R ∧
    (containerRun G I R u).2 ⊆ R ∧
    Disjoint (containerRun G I R u).1 (containerRun G I R u).2 := by
  classical
  rw [containerRun]
  split
  · simp
  · rename_i hstop
    let hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let v := containerChoice G R hR
    have hv : v ∈ R := (container_choice_max_degree G R hR).1
    dsimp only
    by_cases hvI : v ∈ I
    · simp only [show containerChoice G R hR ∈ I from hvI, if_true]
      have ih := container_run_subsets G I (containerNext G R v) u
      have hn := container_next_subset G R v
      have hnot : v ∉ (containerRun G I (containerNext G R v) u).2 := by
        intro hh
        have h := (Finset.mem_filter.mp (ih.2.2.1 hh)).2.1
        exact h rfl
      exact ⟨Finset.insert_subset_iff.mpr ⟨hvI, ih.1⟩,
        Finset.insert_subset_iff.mpr ⟨hv, ih.2.1.trans hn⟩,
        ih.2.2.1.trans hn, Finset.disjoint_insert_left.mpr ⟨hnot, ih.2.2.2⟩⟩
    · simp only [show ¬ containerChoice G R hR ∈ I from hvI, if_false]
      have ih := container_run_subsets G I (R.erase v) u
      exact ⟨ih.1, ih.2.1.trans (Finset.erase_subset _ _),
        ih.2.2.1.trans (Finset.erase_subset _ _), ih.2.2.2⟩
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

#print axioms container_run_subsets
end AllPathsLocal
