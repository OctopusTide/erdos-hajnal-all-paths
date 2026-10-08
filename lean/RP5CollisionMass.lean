import RP5ThinSamplingScale

namespace AllPathsLocal

open scoped BigOperators

/-- Actual finite layer partition accounting: its ordered same-layer pair count
    (expressed as k(k-1)) is at most lam times the total ordered pair count. -/
theorem partition_collision_mass_bound {V : Type} [DecidableEq V]
    (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam : lam ≤ 1)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card) :
    (∑ A ∈ layers, (A.card : ℝ) * ((A.card : ℝ) - 1)) ≤
      lam * S.card * ((S.card : ℝ) - 1) := by
  classical
  have hsumNat : (∑ A ∈ layers, A.card) = S.card := by
    have h := Finset.card_biUnion (s := layers) (t := id) hdis
    simpa only [hcover, id_eq] using h.symm
  have hsum : (∑ A ∈ layers, (A.card : ℝ)) = S.card := by exact_mod_cast hsumNat
  have hstep : ∀ A ∈ layers, (A.card : ℝ) * ((A.card : ℝ) - 1) ≤
      (A.card : ℝ) * (lam * S.card - 1) := by
    intro A hA
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hsize A hA) 1) (Nat.cast_nonneg _)
  have h := Finset.sum_le_sum hstep
  rw [← Finset.sum_mul, hsum] at h
  have hlast : (S.card : ℝ) * (lam * S.card - 1) ≤ lam * S.card * ((S.card : ℝ) - 1) := by
    have hh := mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg S.card)
    nlinarith
  exact h.trans hlast

theorem partition_collision_fraction_bound {V : Type} [DecidableEq V]
    (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam : lam ≤ 1) (hN : 2 ≤ S.card)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card) :
    (∑ A ∈ layers, (A.card : ℝ) * ((A.card : ℝ) - 1)) /
      ((S.card : ℝ) * ((S.card : ℝ) - 1)) ≤ lam := by
  have hNR : (2 : ℝ) ≤ S.card := by exact_mod_cast hN
  apply (div_le_iff₀ (show 0 < (S.card : ℝ) * ((S.card : ℝ) - 1) by nlinarith)).mpr
  simpa only [mul_assoc] using partition_collision_mass_bound S layers hcover hdis lam hlam hsize

#print axioms partition_collision_mass_bound
#print axioms partition_collision_fraction_bound

end AllPathsLocal
