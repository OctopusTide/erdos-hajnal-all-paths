import RP5NegativeScale
import Mathlib.Combinatorics.Pigeonhole

namespace AllPathsLocal

/-- A genuine colouring and equally large clique. This is data, not an axiom.
    Constructing this certificate from weak chordality is STILL UNPROVED here. -/
structure CliqueColorCertificate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  k : ℕ
  color : V → Fin k
  proper : ∀ u v, G.Adj u v → color u ≠ color v
  clique : Finset V
  clique_card : clique.card = k
  clique_adj : ∀ u ∈ clique, ∀ v ∈ clique, u ≠ v → G.Adj u v

/-- The finite pigeonhole step used at P7 II.99-100. The certificate's existence
    is an EXPLICIT mathematical premise; this theorem does not prove Hayward. -/
theorem color_clique_homogeneous_q {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (C : CliqueColorCertificate G)
    (q : ℕ) (hq : 1 ≤ q) (hN : q*q ≤ Fintype.card V) :
    ∃ A : Finset V, A.card = q ∧
      ((∀ u ∈ A, ∀ v ∈ A, u ≠ v → G.Adj u v) ∨
       (∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)) := by
  classical
  by_cases hk : q ≤ C.k
  · obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq (show q ≤ C.clique.card by simpa only [C.clique_card] using hk)
    exact ⟨A, hAc, Or.inl (fun u hu v hv huv => C.clique_adj u (hA hu) v (hA hv) huv)⟩
  · have hV : Nonempty V := Fintype.card_pos_iff.mp (by nlinarith)
    letI : Nonempty V := hV
    letI : Nonempty (Fin C.k) := ⟨C.color (Classical.arbitrary V)⟩
    have hmul : Fintype.card (Fin C.k) * q ≤ Fintype.card V := by
      simp only [Fintype.card_fin]
      nlinarith
    obtain ⟨j, hj⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (f := C.color) hmul
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hj
    refine ⟨A, hAc, Or.inr ?_⟩
    intro u hu v hv huv
    have hcu := (Finset.mem_filter.mp (hA hu)).2
    have hcv := (Finset.mem_filter.mp (hA hv)).2
    exact C.proper u v huv (hcu.trans hcv.symm)

#print axioms color_clique_homogeneous_q

end AllPathsLocal
