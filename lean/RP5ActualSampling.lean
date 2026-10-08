import RP5UniformCollisionBound

namespace AllPathsLocal

/-- Connect the exact uniform count, density estimate, and actual deletion.
    At least half the 2t-samples contain at least t vertices in distinct layers. -/
theorem actual_half_samples_have_transversal {V : Type} [DecidableEq V]
    (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card)
    (t : ℕ) (ht : 1 ≤ t) (hN : 2*t ≤ S.card)
    (hthin : 32 * (t : ℝ) * lam ≤ 1) :
    (S.powersetCard (2*t)).card ≤
      2 * ((S.powersetCard (2*t)).filter (fun U =>
        ∃ T ⊆ U, t ≤ T.card ∧ ∀ A ∈ layers, (T ∩ A).card ≤ 1)).card := by
  classical
  let pairs := layers.biUnion (fun A => A.powersetCard 2)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlam : lam ≤ 1 := by nlinarith
  have hdensity := layer_pairs_density S layers hcover hdis lam hlam hsize
  have hp : ∀ p ∈ pairs, p ⊆ S ∧ p.card = 2 := by
    intro p hp
    obtain ⟨A, hA, hpA⟩ := Finset.mem_biUnion.mp hp
    have hAS : A ⊆ S := by
      intro u hu
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨A, hA, hu⟩
    exact ⟨(Finset.mem_powersetCard.mp hpA).1.trans hAS,
      (Finset.mem_powersetCard.mp hpA).2⟩
  have hhalf := half_uniform_samples_good S pairs t ht hN hp lam hlam0 hdensity hthin
  have hsub : ((S.powersetCard (2*t)).filter
      (fun U => (pairs.filter (· ⊆ U)).card ≤ t)) ⊆
      ((S.powersetCard (2*t)).filter (fun U =>
        ∃ T ⊆ U, t ≤ T.card ∧ ∀ A ∈ layers, (T ∩ A).card ≤ 1)) := by
    intro U hU
    obtain ⟨hUS, hcoll⟩ := Finset.mem_filter.mp hU
    have hcard := (Finset.mem_powersetCard.mp hUS).2
    obtain ⟨T, hTU, hmass, htrans⟩ := sample_transversal_by_collision_deletion U layers
    change U.card ≤ T.card + (pairs.filter (· ⊆ U)).card at hmass
    exact Finset.mem_filter.mpr ⟨hUS, T, hTU, by omega, htrans⟩
  exact hhalf.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub))

#print axioms actual_half_samples_have_transversal
end AllPathsLocal
