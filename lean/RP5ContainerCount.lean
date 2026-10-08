import RP5ContainerEncoding

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable
open scoped BigOperators

noncomputable def stableSubsetFamily {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (q : ℕ) : Finset (Finset V) :=
  (S.powersetCard q).filter (fun I => ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w)

/-- The actual elementary container count in P7 II.113, including the zero
    upper bound when u < q-r. Padding, replay and recovery are all proved. -/
theorem stable_subset_container_count {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u r q : ℕ) (hrq : r ≤ q)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hdegree : ∀ W ⊆ S, u < W.card → ∃ w ∈ W,
      epsilon * ((W.card : ℝ) - 1) < (W.filter (G.Adj w)).card)
    (hbudget : (1-epsilon)^r * (S.card : ℝ) ≤ u) :
    (stableSubsetFamily G S q).card ≤ S.card.choose r * u.choose (q-r) := by
  classical
  let D := (S.powersetCard r).biUnion (fun J =>
    ((containerRun G J S u).2.powersetCard (q-r)).image (fun B => J ∪ B))
  have hsub : stableSubsetFamily G S q ⊆ D := by
    intro I hI
    obtain ⟨hIpow, hstable⟩ := Finset.mem_filter.mp hI
    obtain ⟨hIS, hIcard⟩ := Finset.mem_powersetCard.mp hIpow
    have hrecords := container_run_record_bound G I S u r epsilon he0 he1 hdegree hbudget
    obtain ⟨J, B, hJS, hJcard, hB, hBcard, hrec⟩ :=
      container_stable_encoding G I S u r q hIS hIcard hrq hstable hrecords
    exact Finset.mem_biUnion.mpr ⟨J, Finset.mem_powersetCard.mpr ⟨hJS, hJcard⟩,
      Finset.mem_image.mpr ⟨B, Finset.mem_powersetCard.mpr ⟨hB, hBcard⟩, hrec.symm⟩⟩
  calc
    _ ≤ D.card := Finset.card_le_card hsub
    _ ≤ ∑ J ∈ S.powersetCard r,
        (((containerRun G J S u).2.powersetCard (q-r)).image (fun B => J ∪ B)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ J ∈ S.powersetCard r, u.choose (q-r) := by
      apply Finset.sum_le_sum
      intro J _
      calc
        _ ≤ ((containerRun G J S u).2.powersetCard (q-r)).card := Finset.card_image_le
        _ = ((containerRun G J S u).2.card).choose (q-r) := Finset.card_powersetCard _ _
        _ ≤ _ := Nat.choose_le_choose _ (container_run_terminal G J S u)
    _ = _ := by simp [Finset.card_powersetCard]

#print axioms stable_subset_container_count
end AllPathsLocal
