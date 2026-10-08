import RP5ContainerReplay

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- The actual algorithm records at most r vertices whenever r contractions
    would force the candidate size below its stopping threshold. -/
theorem container_run_record_bound {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (u r : ℕ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hdegree : ∀ W ⊆ R, u < W.card → ∃ w ∈ W,
      epsilon * ((W.card : ℝ) - 1) < (W.filter (G.Adj w)).card)
    (hbudget : (1-epsilon)^r * (R.card : ℝ) ≤ u) :
    (containerRun G I R u).1.card ≤ r := by
  classical
  by_cases hstop : R.card ≤ u
  · rw [containerRun, dif_pos hstop]
    simp
  · have ha : 0 ≤ 1-epsilon := by linarith
    let hR : R.Nonempty := Finset.card_pos.mp (by omega)
    let v := containerChoice G R hR
    have hv : v ∈ R := (container_choice_max_degree G R hR).1
    rw [containerRun, dif_neg hstop]
    dsimp only
    by_cases hvI : v ∈ I
    · simp only [show containerChoice G R hR ∈ I from hvI, if_true]
      cases r with
      | zero =>
          have hh : R.card ≤ u := by simpa using (show (R.card : ℝ) ≤ u by simpa using hbudget)
          exact False.elim (hstop hh)
      | succ r =>
          obtain ⟨w, hw, hdeg⟩ := hdegree R (Finset.Subset.refl _) (by omega)
          have hmax := (container_choice_max_degree G R hR).2 w hw
          have hvdeg : epsilon * ((R.card : ℝ) - 1) <
              (R.filter (G.Adj v)).card := hdeg.trans_le (by exact_mod_cast hmax)
          have hc := (container_step_contracts G R v hv epsilon he1 hvdeg).le
          have hmul := mul_le_mul_of_nonneg_left hc (pow_nonneg ha r)
          have hb : (1-epsilon)^r * ((containerNext G R v).card : ℝ) ≤ u := by
            rw [pow_succ] at hbudget
            nlinarith
          have hd : ∀ W ⊆ containerNext G R v, u < W.card → ∃ w ∈ W,
              epsilon * ((W.card : ℝ) - 1) < (W.filter (G.Adj w)).card := by
            intro W hW hlarge
            exact hdegree W (hW.trans (container_next_subset G R v)) hlarge
          have hi := container_run_record_bound G I (containerNext G R v) u r
            epsilon he0 he1 hd hb
          have hins := Finset.card_insert_le v (containerRun G I (containerNext G R v) u).1
          change (insert v (containerRun G I (containerNext G R v) u).1).card ≤ r+1
          omega
    · simp only [show ¬ containerChoice G R hR ∈ I from hvI, if_false]
      have hs : ((R.erase v).card : ℝ) ≤ (R.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset v R)
      have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg ha r)
      have hd : ∀ W ⊆ R.erase v, u < W.card → ∃ w ∈ W,
          epsilon * ((W.card : ℝ) - 1) < (W.filter (G.Adj w)).card := by
        intro W hW hlarge
        exact hdegree W (hW.trans (Finset.erase_subset _ _)) hlarge
      exact container_run_record_bound G I (R.erase v) u r epsilon he0 he1 hd (hm.trans hbudget)
termination_by R.card
decreasing_by
  all_goals
    have hR : R.Nonempty := Finset.card_pos.mp (by omega)
    have hv := (container_choice_max_degree G R hR).1
    first
    | exact container_next_strict G R _ hv
    | have he := Finset.card_erase_add_one hv
      omega

#print axioms container_run_record_bound
end AllPathsLocal
