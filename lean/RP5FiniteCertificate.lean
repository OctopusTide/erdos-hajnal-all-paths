import RP5ColorClique
import RP5SubsetDoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace AllPathsLocal

/-- Lift the certificate pigeonhole theorem from the induced finite vertex type
    to an actual subset of the ambient graph. Certificate existence is explicit. -/
theorem finite_certificate_homogeneous {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V)
    (C : CliqueColorCertificate (G.induce (T : Set V)))
    (q : ℕ) (hq : 1 ≤ q) (hN : q*q ≤ T.card) :
    ∃ A ⊆ T, A.card = q ∧
      ((∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v) ∨
       (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)) := by
  classical
  obtain ⟨B, hBcard, hB⟩ := color_clique_homogeneous_q
    (G.induce (T : Set V)) C q hq (by simpa using hN)
  refine ⟨B.image Subtype.val, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact v.property
  · rw [Finset.card_image_of_injective _ Subtype.val_injective, hBcard]
  · rcases hB with hB | hB
    · left
      intro u hu v hv huv
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
      exact hB u' hu' v' hv' (fun he => huv (congrArg Subtype.val he))
    · right
      intro u hu v hv
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
      exact hB u' hu' v' hv'

#print axioms finite_certificate_homogeneous
end AllPathsLocal
