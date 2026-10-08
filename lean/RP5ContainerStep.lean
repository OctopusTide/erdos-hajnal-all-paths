import RP5ManyHomogeneous
import Mathlib.Data.Finset.Max

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

noncomputable def containerNext {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (v : V) : Finset V := by
  classical
  exact R.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)

/-- The deterministic choice depends only on the current candidate set. -/
noncomputable def containerChoice {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (hR : R.Nonempty) : V := by
  classical
  exact Classical.choose (Finset.exists_max_image R
    (fun v => (R.filter (G.Adj v)).card) hR)

theorem container_choice_max_degree {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (hR : R.Nonempty) :
    containerChoice G R hR ∈ R ∧ ∀ v ∈ R,
      (R.filter (G.Adj v)).card ≤ (R.filter (G.Adj (containerChoice G R hR))).card := by
  classical
  exact Classical.choose_spec (Finset.exists_max_image R
    (fun v => (R.filter (G.Adj v)).card) hR)

theorem container_next_strict {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (v : V) (hv : v ∈ R) :
    (containerNext G R v).card < R.card := by
  classical
  have hsub : containerNext G R v ⊆ R.erase v := by
    intro w hw
    obtain ⟨hwR, hwv, _⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨hwv, hwR⟩
  have he := Finset.card_erase_add_one hv
  have hs := Finset.card_le_card hsub
  omega

theorem container_next_preserves_stable {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I R : Finset V) (v : V) (hIR : I ⊆ R)
    (hv : v ∈ I) (hstable : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) :
    I.erase v ⊆ containerNext G R v := by
  classical
  intro w hw
  obtain ⟨hwv, hwI⟩ := Finset.mem_erase.mp hw
  exact Finset.mem_filter.mpr ⟨hIR hwI, hwv, hstable v hv w hwI⟩

theorem container_next_card {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (v : V) (hv : v ∈ R) :
    (containerNext G R v).card + (R.filter (G.Adj v)).card + 1 = R.card := by
  classical
  have hn : (R.erase v).filter (G.Adj v) = R.filter (G.Adj v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · exact fun h => ⟨h.1.2, h.2⟩
    · intro h
      exact ⟨⟨fun he => by subst w; exact G.irrefl h.2, h.1⟩, h.2⟩
  have hc : containerNext G R v = (R.erase v).filter (fun w => ¬ G.Adj v w) := by
    ext w
    simp [containerNext, and_assoc, and_left_comm]
  have h := Finset.card_filter_add_card_filter_not (s := R.erase v) (G.Adj v)
  rw [hn, ← hc] at h
  have he := Finset.card_erase_add_one hv
  omega

theorem container_next_subset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (v : V) :
    containerNext G R v ⊆ R := Finset.filter_subset _ _

/-- The stronger degree convention from the actual paper gives the recorded
    step contraction, including the vertex removed with its neighbourhood. -/
theorem container_step_contracts {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (v : V) (hv : v ∈ R)
    (epsilon : ℝ) (he : epsilon ≤ 1)
    (hdegree : epsilon * ((R.card : ℝ) - 1) < (R.filter (G.Adj v)).card) :
    ((containerNext G R v).card : ℝ) < (1-epsilon) * R.card := by
  have hc : ((containerNext G R v).card : ℝ) +
      ((R.filter (G.Adj v)).card : ℝ) + 1 = (R.card : ℝ) := by
    exact_mod_cast container_next_card G R v hv
  nlinarith

#print axioms container_choice_max_degree
#print axioms container_next_strict
#print axioms container_next_preserves_stable
#print axioms container_next_card
#print axioms container_next_subset
#print axioms container_step_contracts
end AllPathsLocal
