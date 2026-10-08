import RP5ContainerCover

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- Exact replay, including padding: any selector containing the recorded
    fingerprint and using only it and final candidates reproduces the run. -/
theorem container_run_replay {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I J R : Finset V) (u : ℕ)
    (hF : (containerRun G I R u).1 ⊆ J)
    (hJ : J ∩ R ⊆ (containerRun G I R u).1 ∪ (containerRun G I R u).2) :
    containerRun G J R u = containerRun G I R u := by
  classical
  by_cases hstop : R.card ≤ u
  · rw [containerRun, dif_pos hstop]
    conv_rhs => rw [containerRun, dif_pos hstop]
  · let hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let v := containerChoice G R hR
    have hv : v ∈ R := (container_choice_max_degree G R hR).1
    rw [containerRun, dif_neg hstop] at hF hJ
    dsimp only at hF hJ
    by_cases hvI : v ∈ I
    · simp only [show containerChoice G R hR ∈ I from hvI, if_true] at hF hJ
      have hvJ : v ∈ J := hF (Finset.mem_insert_self _ _)
      have hF' : (containerRun G I (containerNext G R v) u).1 ⊆ J := by
        intro w hw
        exact hF (Finset.mem_insert_of_mem hw)
      have hJ' : J ∩ containerNext G R v ⊆
          (containerRun G I (containerNext G R v) u).1 ∪
          (containerRun G I (containerNext G R v) u).2 := by
        intro w hw
        obtain ⟨hwJ, hwn⟩ := Finset.mem_inter.mp hw
        have hwR := container_next_subset G R v hwn
        have hwv := (Finset.mem_filter.mp hwn).2.1
        have hh := hJ (Finset.mem_inter.mpr ⟨hwJ, hwR⟩)
        rcases Finset.mem_union.mp hh with hh | hh
        · exact Finset.mem_union_left _ ((Finset.mem_insert.mp hh).resolve_left hwv)
        · exact Finset.mem_union_right _ hh
      have hi := container_run_replay G I J (containerNext G R v) u hF' hJ'
      rw [containerRun, dif_neg hstop]
      conv_rhs => rw [containerRun, dif_neg hstop]
      dsimp only
      simp only [show containerChoice G R hR ∈ J from hvJ,
        show containerChoice G R hR ∈ I from hvI, if_true]
      change (insert v (containerRun G J (containerNext G R v) u).1,
        (containerRun G J (containerNext G R v) u).2) =
        (insert v (containerRun G I (containerNext G R v) u).1,
          (containerRun G I (containerNext G R v) u).2)
      rw [hi]
    · simp only [show ¬ containerChoice G R hR ∈ I from hvI, if_false] at hF hJ
      have hs := container_run_subsets G I (R.erase v) u
      have hvJ : v ∉ J := by
        intro hvJ
        have hh := hJ (Finset.mem_inter.mpr ⟨hvJ, hv⟩)
        rcases Finset.mem_union.mp hh with hh | hh
        · exact Finset.notMem_erase v R (hs.2.1 hh)
        · exact Finset.notMem_erase v R (hs.2.2.1 hh)
      have hJ' : J ∩ R.erase v ⊆ (containerRun G I (R.erase v) u).1 ∪
          (containerRun G I (R.erase v) u).2 := by
        intro w hw
        obtain ⟨hwJ, hwR⟩ := Finset.mem_inter.mp hw
        exact hJ (Finset.mem_inter.mpr ⟨hwJ, (Finset.mem_erase.mp hwR).2⟩)
      have hi := container_run_replay G I J (R.erase v) u hF hJ'
      rw [containerRun, dif_neg hstop]
      conv_rhs => rw [containerRun, dif_neg hstop]
      dsimp only
      simpa only [show ¬ containerChoice G R hR ∈ J from hvJ,
        show ¬ containerChoice G R hR ∈ I from hvI, if_false] using hi
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

#print axioms container_run_replay
end AllPathsLocal
