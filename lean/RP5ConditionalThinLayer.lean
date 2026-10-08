import RP5DecisionNormalization

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

theorem homogeneous_family_union {V : Type} (G : SimpleGraph V) [DecidableEq V]
    (S : Finset V) (q : ℕ) : homogeneousSubsetFamily G S q =
      stableSubsetFamily G S q ∪ stableSubsetFamily Gᶜ S q := by
  classical
  ext A
  simp only [homogeneousSubsetFamily, stableSubsetFamily, Finset.mem_filter,
    Finset.mem_union, IsHomogeneousFinset]
  constructor
  · rintro ⟨hp, hc | hs⟩
    · right
      refine ⟨hp, ?_⟩
      intro u hu v hv hcomp
      obtain ⟨hne, hnot⟩ := (G.compl_adj u v).mp hcomp
      exact hnot (hc u hu v hv hne)
    · exact Or.inl ⟨hp, hs⟩
  · rintro (⟨hp, hs⟩ | ⟨hp, hs⟩)
    · exact ⟨hp, Or.inr hs⟩
    · refine ⟨hp, Or.inl ?_⟩
      intro u hu v hv hne
      by_contra hnot
      exact hs u hu v hv ((G.compl_adj u v).mpr ⟨hne, hnot⟩)

/-- An actual thin-layer restricted subset, conditional ONLY on displayed
    colouring/clique certificates and the verified scalar parameter bounds.
    The graph sampling, stable containers, padding, replay, and counting are
    constructed here. Hayward certificate existence remains unproved. -/
theorem actual_thin_restricted_of_certificates {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam epsilon : ℝ) (hlam0 : 0 ≤ lam) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam*S.card)
    (q r u : ℕ) (hq : 2 ≤ q) (hrq : r ≤ q) (hN : 2*(q*q) ≤ S.card)
    (hthin : 32*((q*q : ℕ) : ℝ)*lam ≤ 1)
    (hu : (u : ℝ) ≤ (S.card : ℝ)/(128*(q : ℝ)))
    (hbudget : (1-epsilon)^r*(S.card : ℝ) ≤ u)
    (herror : (r : ℝ)/(q : ℝ)*Real.log (128*(q : ℝ)) < 1)
    (hcert : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      Nonempty (CliqueColorCertificate (G.induce (T : Set V)))) :
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
  have hcount := actual_many_homogeneous_subsets G S layers hcover hdis lam hlam0 hsize
    q (by omega) hN hthin hcert
  have hLower : (S.card : ℝ)^q ≤
      2*((homogeneousSubsetFamily G S q).card : ℝ)*(2*(q : ℝ)^2)^q := by
    have hh := homogeneous_count_power_lower S.card (2*(q*q)) q
      (homogeneousSubsetFamily G S q).card (by nlinarith) hN hcount
    simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_two] using hh
  exact thin_counts_inconsistent S.card u q r (homogeneousSubsetFamily G S q).card
    (by nlinarith) hq hrq hu herror hLower hUpper

#print axioms homogeneous_family_union
#print axioms actual_thin_restricted_of_certificates
end AllPathsLocal
