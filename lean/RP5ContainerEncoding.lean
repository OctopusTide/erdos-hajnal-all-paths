import RP5ContainerRecordBound

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- Actual padded r-fingerprint and q-r residual, recovered using replay.
    This verifies that padding does not change the deterministic container. -/
theorem container_stable_encoding {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (I S : Finset V) (u r q : ℕ)
    (hIS : I ⊆ S) (hIcard : I.card = q) (hrq : r ≤ q)
    (hstable : ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w)
    (hrecords : (containerRun G I S u).1.card ≤ r) :
    ∃ J B : Finset V, J ⊆ S ∧ J.card = r ∧
      B ⊆ (containerRun G J S u).2 ∧ B.card = q-r ∧ I = J ∪ B := by
  classical
  have hs := container_run_subsets G I S u
  obtain ⟨J, hFJ, hJI, hJcard⟩ := Finset.exists_subsuperset_card_eq hs.1 hrecords
    (by simpa only [hIcard] using hrq)
  have hcover : I ⊆ (containerRun G I S u).1 ∪ (containerRun G I S u).2 := by
    intro w hw
    exact container_run_stable_cover G I S u hstable (Finset.mem_inter.mpr ⟨hw, hIS hw⟩)
  have hJ : J ∩ S ⊆ (containerRun G I S u).1 ∪ (containerRun G I S u).2 := by
    intro w hw
    exact hcover (hJI (Finset.mem_inter.mp hw).1)
  have hreplay := container_run_replay G I J S u hFJ hJ
  refine ⟨J, I \ J, hJI.trans hIS, hJcard, ?_, ?_, ?_⟩
  · rw [hreplay]
    intro w hw
    obtain ⟨hwI, hwJ⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp (hcover hwI) with hwF | hwC
    · exact False.elim (hwJ (hFJ hwF))
    · exact hwC
  · rw [Finset.card_sdiff_of_subset hJI, hIcard, hJcard]
  · ext w
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hw
      by_cases hwJ : w ∈ J
      · exact Or.inl hwJ
      · exact Or.inr ⟨hw, hwJ⟩
    · intro hw
      rcases hw with hw | hw
      · exact hJI hw
      · exact hw.1

#print axioms container_stable_encoding
end AllPathsLocal
