import RP5CollisionDeletion
import Mathlib.Data.Nat.Choose.Cast

namespace AllPathsLocal
open scoped BigOperators

/-- Actual same-layer unordered pair family has the sum of the layer pair counts. -/
theorem layer_pairs_card {V : Type} [DecidableEq V] (layers : Finset (Finset V))
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B) :
    (layers.biUnion (fun A => A.powersetCard 2)).card =
      ∑ A ∈ layers, A.card.choose 2 := by
  classical
  rw [Finset.card_biUnion]
  · simp only [Finset.card_powersetCard]
  · intro A hA B hB hAB
    exact (hdis A hA B hB hAB).powersetCard_powersetCard_finset (by omega)

/-- Convert the already proved actual partition mass bound into an unordered
    pair-density bound; no probabilistic premise is assumed. -/
theorem layer_pairs_density {V : Type} [DecidableEq V]
    (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam : lam ≤ 1)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card) :
    ((layers.biUnion (fun A => A.powersetCard 2)).card : ℝ) ≤
      lam * (S.card.choose 2 : ℝ) := by
  classical
  rw [layer_pairs_card layers hdis, Nat.cast_sum]
  simp only [Nat.cast_choose_two]
  have h := partition_collision_mass_bound S layers hcover hdis lam hlam hsize
  rw [← Finset.sum_div]
  nlinarith

/-- Exact incidence counting implies the finite uniform-sample expectation
    bound under an actual bad-pair density bound. -/
theorem uniform_collision_sum_bound {V : Type} [DecidableEq V]
    (S : Finset V) (pairs : Finset (Finset V)) (k : ℕ)
    (hk : 2 ≤ k) (hN : 2 ≤ S.card)
    (hp : ∀ p ∈ pairs, p ⊆ S ∧ p.card = 2)
    (lam : ℝ) (hdensity : (pairs.card : ℝ) ≤ lam * (S.card.choose 2 : ℝ)) :
    (∑ T ∈ S.powersetCard k, ((pairs.filter (· ⊆ T)).card : ℝ)) ≤
      lam * (S.card.choose k : ℝ) * (k.choose 2 : ℝ) := by
  have hC : 0 < (S.card.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hN
  have hi : (∑ T ∈ S.powersetCard k, ((pairs.filter (· ⊆ T)).card : ℝ)) *
      (S.card.choose 2 : ℝ) = (pairs.card : ℝ) *
      ((S.card.choose k : ℝ) * (k.choose 2 : ℝ)) := by
    exact_mod_cast uniform_pair_expectation_identity S pairs k hk hp
  have hm := mul_le_mul_of_nonneg_right hdensity
    (show 0 ≤ (S.card.choose k : ℝ) * (k.choose 2 : ℝ) by positivity)
  nlinarith

/-- At least half of the actual uniform 2t-subsets have at most t collisions.
    This proves the sampling assertion in P7 II.96-98 from pair density. -/
theorem half_uniform_samples_good {V : Type} [DecidableEq V]
    (S : Finset V) (pairs : Finset (Finset V)) (t : ℕ)
    (ht : 1 ≤ t) (hN : 2*t ≤ S.card)
    (hp : ∀ p ∈ pairs, p ⊆ S ∧ p.card = 2)
    (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hdensity : (pairs.card : ℝ) ≤ lam * (S.card.choose 2 : ℝ))
    (hthin : 32 * (t : ℝ) * lam ≤ 1) :
    (S.powersetCard (2*t)).card ≤
      2 * ((S.powersetCard (2*t)).filter
        (fun T => (pairs.filter (· ⊆ T)).card ≤ t)).card := by
  classical
  apply half_samples_collision_bound
  have hs := uniform_collision_sum_bound S pairs (2*t) (by omega) (by omega) hp lam hdensity
  have hc : ((2*t).choose 2 : ℝ) ≤ 2 * (t : ℝ)^2 := by
    rw [Nat.cast_choose_two]
    push_cast
    nlinarith [show (0 : ℝ) ≤ (t : ℝ) from Nat.cast_nonneg t]
  have htR : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
  have hq := mul_le_mul_of_nonneg_left hthin htR
  have hfactor : lam * ((2*t).choose 2 : ℝ) ≤ (t : ℝ) / 16 := by
    have hm := mul_le_mul_of_nonneg_left hc hlam0
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hfactor
    (show 0 ≤ (S.card.choose (2*t) : ℝ) by positivity)
  have hcard : ((S.powersetCard (2*t)).card : ℝ) = (S.card.choose (2*t) : ℝ) := by
    rw [Finset.card_powersetCard]
  have hfinal : 2 * (∑ T ∈ S.powersetCard (2*t), ((pairs.filter (· ⊆ T)).card : ℝ)) ≤
      ((t : ℝ) + 1) * ((S.powersetCard (2*t)).card : ℝ) := by
    rw [hcard]
    nlinarith [show (0 : ℝ) ≤ (S.card.choose (2*t) : ℝ) from Nat.cast_nonneg _]
  exact_mod_cast hfinal

#print axioms layer_pairs_card
#print axioms layer_pairs_density
#print axioms uniform_collision_sum_bound
#print axioms half_uniform_samples_good
end AllPathsLocal
