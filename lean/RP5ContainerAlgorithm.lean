import RP5ContainerStep

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- The actual deterministic algorithm from P7 II.114-121. The first component
    records selected vertices, the second is the final candidate container. -/
noncomputable def containerRun {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (u : ℕ) : Finset V × Finset V :=
  if h : R.card ≤ u then (∅, R)
  else
    let hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let v := containerChoice G R hR
    if v ∈ I then
      let z := containerRun G I (containerNext G R v) u
      (insert v z.1, z.2)
    else containerRun G I (R.erase v) u
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

/-- Every run terminates with a genuine candidate set of at most u vertices. -/
theorem container_run_terminal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (u : ℕ) :
    (containerRun G I R u).2.card ≤ u := by
  classical
  rw [containerRun]
  split
  · assumption
  · dsimp only
    split
    · exact container_run_terminal G I (containerNext G R _) u
    · exact container_run_terminal G I (R.erase _) u
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

#print axioms container_run_terminal
end AllPathsLocal
