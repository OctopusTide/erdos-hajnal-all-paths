import RP5ActualSampling

namespace AllPathsLocal
open scoped BigOperators

/-- Uniform subset/witness incidence count for arbitrary q. -/
theorem uniform_subset_incidence {V : Type} [DecidableEq V]
    (S : Finset V) (witnesses : Finset (Finset V)) (q k : ℕ)
    (hqk : q ≤ k) (hw : ∀ A ∈ witnesses, A ⊆ S ∧ A.card = q) :
    (∑ T ∈ S.powersetCard k, (witnesses.filter (· ⊆ T)).card) =
      witnesses.card * (S.card - q).choose (k - q) := by
  classical
  calc
    _ = ∑ T ∈ S.powersetCard k, ∑ A ∈ witnesses, if A ⊆ T then 1 else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ A ∈ witnesses, ∑ T ∈ S.powersetCard k, if A ⊆ T then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ A ∈ witnesses, (S.card - q).choose (k - q) := by
      apply Finset.sum_congr rfl
      intro A hA
      have h := Finset.card_filter_powersetCard_subset A S k (hw A hA).1
        (by simpa only [(hw A hA).2] using hqk)
      rw [(hw A hA).2] at h
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using h
    _ = _ := by simp

/-- Actual finite double counting: every good sample contains a witness.
    Good samples need not choose that witness consistently. -/
theorem good_samples_witness_count {V : Type} [DecidableEq V]
    (S : Finset V) (witnesses good : Finset (Finset V)) (q k : ℕ)
    (hqk : q ≤ k) (hw : ∀ A ∈ witnesses, A ⊆ S ∧ A.card = q)
    (hgood : good ⊆ S.powersetCard k)
    (hex : ∀ T ∈ good, ∃ A ∈ witnesses, A ⊆ T) :
    good.card ≤ witnesses.card * (S.card - q).choose (k - q) := by
  classical
  rw [← uniform_subset_incidence S witnesses q k hqk hw]
  calc
    good.card = ∑ T ∈ good, 1 := by simp
    _ ≤ ∑ T ∈ good, (witnesses.filter (· ⊆ T)).card := by
      apply Finset.sum_le_sum
      intro T hT
      obtain ⟨A, hA, hAT⟩ := hex T hT
      exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, hAT⟩⟩
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hgood (by intros; omega)

#print axioms uniform_subset_incidence
#print axioms good_samples_witness_count
end AllPathsLocal
