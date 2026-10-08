import RP5ContainerInvariants

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- No stable-set member is lost: it is recorded or remains in the container. -/
theorem container_run_stable_cover {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (u : ℕ)
    (hstable : ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) :
    I ∩ R ⊆ (containerRun G I R u).1 ∪ (containerRun G I R u).2 := by
  classical
  rw [containerRun]
  split
  · simpa using (Finset.inter_subset_right : I ∩ R ⊆ R)
  · rename_i hstop
    let hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let v := containerChoice G R hR
    have hv : v ∈ R := (container_choice_max_degree G R hR).1
    dsimp only
    by_cases hvI : v ∈ I
    · simp only [show containerChoice G R hR ∈ I from hvI, if_true]
      intro w hw
      obtain ⟨hwI, hwR⟩ := Finset.mem_inter.mp hw
      by_cases hwv : w = v
      · subst w
        exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
      · have hwn : w ∈ containerNext G R v :=
          Finset.mem_filter.mpr ⟨hwR, hwv, hstable v hvI w hwI⟩
        have hi := container_run_stable_cover G I (containerNext G R v) u hstable
          (Finset.mem_inter.mpr ⟨hwI, hwn⟩)
        rcases Finset.mem_union.mp hi with hi | hi
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hi)
        · exact Finset.mem_union_right _ hi
    · simp only [show ¬ containerChoice G R hR ∈ I from hvI, if_false]
      intro w hw
      obtain ⟨hwI, hwR⟩ := Finset.mem_inter.mp hw
      have hwv : w ≠ v := by intro he; subst w; exact hvI hwI
      exact container_run_stable_cover G I (R.erase v) u hstable
        (Finset.mem_inter.mpr ⟨hwI, Finset.mem_erase.mpr ⟨hwv, hwR⟩⟩)
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

#print axioms container_run_stable_cover
end AllPathsLocal
