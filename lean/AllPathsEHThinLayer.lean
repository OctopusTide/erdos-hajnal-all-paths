import AllPathsThinCountScaled

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- Full EH-transversal sampling/container bridge at explicit integer parameters.
    The general paper's epsilon-dependent ceil and log estimates remain separate
    obligations. The graph-theoretic EH premise is displayed and not asserted. -/
theorem eh_transversal_integer_thin_layer {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam epsilon : ℝ) (hlam0 : 0 ≤ lam) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam*S.card)
    (q r u t : ℕ) (hqt : q ≤ t) (hq : 2 ≤ q) (hrq : r ≤ q) (hN : 2*t ≤ S.card)
    (hthin : 32*(t : ℝ)*lam ≤ 1)
    (D : ℝ) (hD0 : 0 < D) (hD : 128*(t : ℝ)/(q : ℝ) ≤ D)
    (hu : (u : ℝ) ≤ (S.card : ℝ)/D)
    (hbudget : (1-epsilon)^r*(S.card : ℝ) ≤ u)
    (herror : (r : ℝ)/(q : ℝ)*Real.log D < 1)
    (kappa : ℝ) (hkappa : 0 ≤ kappa) (hpower : (q : ℝ) ≤ (t : ℝ)^kappa)
    (hEH : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, IsHomogeneousFinset G A ∧ (T.card : ℝ)^kappa ≤ A.card) :
    ∃ W ⊆ S, u < W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1))) := by
  classical
  by_contra hnot
  have hdG : ∀ W ⊆ S, u < W.card → ∃ v ∈ W,
      epsilon*((W.card : ℝ)-1) < (W.filter (G.Adj v)).card := by
    intro W hWS hWlarge
    by_contra hh
    push_neg at hh
    apply hnot
    exact ⟨W, hWS, hWlarge, Or.inl hh⟩
  have hdC : ∀ W ⊆ S, u < W.card → ∃ v ∈ W,
      epsilon*((W.card : ℝ)-1) < (W.filter (Gᶜ.Adj v)).card := by
    intro W hWS hWlarge
    by_contra hh
    push_neg at hh
    apply hnot
    refine ⟨W, hWS, hWlarge, Or.inr ?_⟩
    simpa only [filter_card_classical] using hh
  have hG := stable_subset_container_count G S u r q hrq epsilon he0 he1 hdG hbudget
  have hC := stable_subset_container_count Gᶜ S u r q hrq epsilon he0 he1
    (by simpa only [filter_card_classical] using hdC) hbudget
  have hUpper : (homogeneousSubsetFamily G S q).card ≤
      2*(S.card.choose r*u.choose (q-r)) := by
    calc
      _ ≤ (stableSubsetFamily G S q).card + (stableSubsetFamily Gᶜ S q).card := by
        rw [homogeneous_family_union]
        apply Finset.card_union_le
      _ ≤ _ := by omega
  have hcount := actual_many_homogeneous_subsets_of_transversal_bound G S layers hcover hdis lam hlam0 hsize
    q t (by omega) hqt hN hthin
    (eh_transversal_homogeneous_witness G S layers kappa hkappa q t hpower hEH)
  have hLower : (S.card : ℝ)^q ≤
      2*((homogeneousSubsetFamily G S q).card : ℝ)*(2*(t : ℝ))^q := by
    have hh := homogeneous_count_power_lower S.card (2*t) q
      (homogeneousSubsetFamily G S q).card (by nlinarith) hN hcount
    simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_two] using hh
  exact thin_counts_inconsistent_scaled S.card u q r t (homogeneousSubsetFamily G S q).card
    (by nlinarith) hq hrq (by omega) D hD0 hD hu herror hLower hUpper


#print axioms eh_transversal_integer_thin_layer
end AllPathsLocal
