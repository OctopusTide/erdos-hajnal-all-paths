import RP5FiniteCertificate

namespace AllPathsLocal

def IsHomogeneousFinset {V : Type} (G : SimpleGraph V) (A : Finset V) : Prop :=
  (∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v) ∨
  (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)

noncomputable def homogeneousSubsetFamily {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (q : ℕ) : Finset (Finset V) := by
  classical
  exact (S.powersetCard q).filter (IsHomogeneousFinset G)

/-- P7 II.96-104, finite sampling and double counting joined on actual sets.
    The unproved Hayward construction is displayed as hcert, never as an axiom.
    No restricted-set/thin-layer conclusion is assumed. -/
theorem actual_many_homogeneous_subsets {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam : ℝ) (hlam0 : 0 ≤ lam)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam * S.card)
    (q : ℕ) (hq : 1 ≤ q) (hN : 2*(q*q) ≤ S.card)
    (hthin : 32 * ((q*q : ℕ) : ℝ) * lam ≤ 1)
    (hcert : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      Nonempty (CliqueColorCertificate (G.induce (T : Set V)))) :
    S.card.choose (2*(q*q)) ≤
      2 * (homogeneousSubsetFamily G S q).card * (S.card - q).choose (2*(q*q) - q) := by
  classical
  let H := (S.powersetCard q).filter (IsHomogeneousFinset G)
  let good := (S.powersetCard (2*(q*q))).filter (fun U =>
    ∃ T ⊆ U, q*q ≤ T.card ∧ ∀ A ∈ layers, (T ∩ A).card ≤ 1)
  have hhalf := actual_half_samples_have_transversal S layers hcover hdis lam hlam0 hsize
    (q*q) (by nlinarith) hN hthin
  have hw : ∀ A ∈ H, A ⊆ S ∧ A.card = q := by
    intro A hA
    exact Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1
  have hg : good ⊆ S.powersetCard (2*(q*q)) := Finset.filter_subset _ _
  have hex : ∀ U ∈ good, ∃ A ∈ H, A ⊆ U := by
    intro U hU
    obtain ⟨hUS, T, hTU, hTcard, hTtrans⟩ := Finset.mem_filter.mp hU
    have hTS := hTU.trans (Finset.mem_powersetCard.mp hUS).1
    obtain ⟨C⟩ := hcert T hTS hTtrans
    obtain ⟨A, hAT, hAcard, hA⟩ := finite_certificate_homogeneous G T C q hq hTcard
    exact ⟨A, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAT.trans hTS, hAcard⟩, hA⟩, hAT.trans hTU⟩
  have hcount := good_samples_witness_count S H good q (2*(q*q)) (by nlinarith) hw hg hex
  rw [Finset.card_powersetCard] at hhalf
  change S.card.choose (2*(q*q)) ≤ 2 * H.card * (S.card - q).choose (2*(q*q) - q)
  exact hhalf.trans (by dsimp [good] at hcount; nlinarith)

#print axioms actual_many_homogeneous_subsets
end AllPathsLocal
