import RP5CollisionMass
import Mathlib.Data.Finset.Powerset

namespace AllPathsLocal
open scoped BigOperators

/-- Exact finite uniform-sample incidence count, with actual bad pairs.
    The pair family is a set of two-element subsets, so collisions are unordered. -/
theorem uniform_pair_incidence {V : Type} [DecidableEq V]
    (S : Finset V) (pairs : Finset (Finset V)) (k : ℕ)
    (hk : 2 ≤ k) (hp : ∀ p ∈ pairs, p ⊆ S ∧ p.card = 2) :
    (∑ T ∈ S.powersetCard k, (pairs.filter (· ⊆ T)).card) =
      pairs.card * (S.card - 2).choose (k - 2) := by
  classical
  calc
    _ = ∑ T ∈ S.powersetCard k, ∑ p ∈ pairs, if p ⊆ T then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ pairs, ∑ T ∈ S.powersetCard k, if p ⊆ T then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ p ∈ pairs, (S.card - 2).choose (k - 2) := by
      apply Finset.sum_congr rfl
      intro p hp'
      have h := Finset.card_filter_powersetCard_subset p S k (hp p hp').1
        (by simpa only [(hp p hp').2] using hk)
      rw [(hp p hp').2] at h
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using h
    _ = _ := by simp [Nat.mul_comm]

/-- Division-free exact expectation formula for uniform k-subsets. -/
theorem uniform_pair_expectation_identity {V : Type} [DecidableEq V]
    (S : Finset V) (pairs : Finset (Finset V)) (k : ℕ)
    (hk : 2 ≤ k) (hp : ∀ p ∈ pairs, p ⊆ S ∧ p.card = 2) :
    (∑ T ∈ S.powersetCard k, (pairs.filter (· ⊆ T)).card) * S.card.choose 2 =
      pairs.card * (S.card.choose k * k.choose 2) := by
  rw [uniform_pair_incidence S pairs k hk hp, Nat.choose_mul hk]
  ring

/-- The finite Markov step: a sufficiently small total collision mass forces
    at least half the samples to have at most b collisions. -/
theorem half_samples_collision_bound {V : Type} [DecidableEq V]
    (samples : Finset (Finset V)) (pairs : Finset (Finset V)) (b : ℕ)
    (hmass : 2 * (∑ T ∈ samples, (pairs.filter (· ⊆ T)).card) ≤
      (b + 1) * samples.card) :
    samples.card ≤ 2 * (samples.filter (fun T => (pairs.filter (· ⊆ T)).card ≤ b)).card := by
  classical
  let good := samples.filter (fun T => (pairs.filter (· ⊆ T)).card ≤ b)
  let bad := samples.filter (fun T => ¬ (pairs.filter (· ⊆ T)).card ≤ b)
  have hpartition : good.card + bad.card = samples.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hsum : (b + 1) * bad.card ≤ ∑ T ∈ samples, (pairs.filter (· ⊆ T)).card := by
    calc
      _ = ∑ T ∈ bad, (b + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ T ∈ bad, (pairs.filter (· ⊆ T)).card := by
        apply Finset.sum_le_sum
        intro T hT
        have hh := (Finset.mem_filter.mp hT).2
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
  dsimp [good] at hpartition ⊢
  nlinarith

#print axioms uniform_pair_incidence
#print axioms uniform_pair_expectation_identity
#print axioms half_samples_collision_bound
end AllPathsLocal
