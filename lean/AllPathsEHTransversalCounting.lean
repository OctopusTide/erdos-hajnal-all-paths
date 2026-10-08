import AllPathsNegativeOrder

namespace AllPathsLocal

/-- General sampling and witness double count for arbitrary transversal order t.
    This is the counting input to the EH bridge beyond perfect transversals. -/
theorem actual_many_homogeneous_subsets_of_transversal_bound {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card)
    (q t : ℕ) (hq : 1 ≤ q) (hqt : q ≤ t) (hN : 2*t ≤ S.card)
    (hthin : 32 * ((t : ℕ) : ℝ) * lam ≤ 1)
    (hhom : ∀ T : Finset V, T ⊆ S → t ≤ T.card →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, A.card = q ∧ IsHomogeneousFinset G A) :
    S.card.choose (2*t) ≤
      2 * (homogeneousSubsetFamily G S q).card * (S.card - q).choose (2*t - q) := by
  classical
  let H := (S.powersetCard q).filter (IsHomogeneousFinset G)
  let good := (S.powersetCard (2*t)).filter (fun U =>
    ∃ T ⊆ U, t ≤ T.card ∧ ∀ A ∈ layers, (T ∩ A).card ≤ 1)
  have hhalf := actual_half_samples_have_transversal S layers hcover hdis lam hlam0 hsize
    t (by omega) hN hthin
  have hw : ∀ A ∈ H, A ⊆ S ∧ A.card = q := by
    intro A hA
    exact Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1
  have hg : good ⊆ S.powersetCard (2*t) := Finset.filter_subset _ _
  have hex : ∀ U ∈ good, ∃ A ∈ H, A ⊆ U := by
    intro U hU
    obtain ⟨hUS, T, hTU, hTcard, hTtrans⟩ := Finset.mem_filter.mp hU
    have hTS := hTU.trans (Finset.mem_powersetCard.mp hUS).1
    obtain ⟨A, hAT, hAcard, hA⟩ := hhom T hTS hTcard hTtrans
    exact ⟨A, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAT.trans hTS, hAcard⟩, hA⟩, hAT.trans hTU⟩
  have hcount := good_samples_witness_count S H good q (2*t) (by omega) hw hg hex
  rw [Finset.card_powersetCard] at hhalf
  change S.card.choose (2*t) ≤ 2 * H.card * (S.card - q).choose (2*t - q)
  exact hhalf.trans (by dsimp [good] at hcount; nlinarith)

/-- An actual EH transversal exponent supplies a q-vertex homogeneous
    witness whenever t^kappa >= q. Cardinal truncation preserves its type. -/
theorem eh_transversal_homogeneous_witness {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (layers : Finset (Finset V))
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (q t : ℕ)
    (hqt : (q : ℝ) ≤ (t : ℝ)^kappa)
    (hEH : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, IsHomogeneousFinset G A ∧ (T.card : ℝ)^kappa ≤ A.card) :
    ∀ T : Finset V, T ⊆ S → t ≤ T.card →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, A.card = q ∧ IsHomogeneousFinset G A := by
  classical
  intro T hTS htT hthin
  obtain ⟨A, hAT, hAH, hsize⟩ := hEH T hTS hthin
  have hpower := Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr htT) hkappa
  have hqA : q ≤ A.card := by exact_mod_cast (hqt.trans (hpower.trans hsize))
  obtain ⟨B, hBA, hBcard⟩ := Finset.exists_subset_card_eq hqA
  refine ⟨B, hBA.trans hAT, hBcard, ?_⟩
  rcases hAH with hclique | hstable
  · exact Or.inl (fun u hu v hv hne => hclique u (hBA hu) v (hBA hv) hne)
  · exact Or.inr (fun u hu v hv => hstable u (hBA hu) v (hBA hv))

#print axioms actual_many_homogeneous_subsets_of_transversal_bound
#print axioms eh_transversal_homogeneous_witness
end AllPathsLocal
