import RP5PaperReduction
import RP5NegativeConclusion

namespace AllPathsLocal

/-- The complete ambient-independent RP5 Tooth theorem at the paper's original
    x,y parameters: clean core, strongly restricted set, or directed blockade.
    No transversal-certificate or perfection premise remains. -/
theorem rp5_tooth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V) (x y : ℝ)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hx : 0 < x) (hxy : x ≤ y) (hySmall : y ≤ 1 / 2^16)
    (hN : 1 / x^600 ≤ (Y.card : ℝ)) :
    (∃ A ⊆ Y, y^26 * Y.card ≤ (A.card : ℝ) ∧ FullOrSmall G U x A) ∨
    (∃ W ⊆ Y, y^18*(Y.card : ℝ) ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1)))) ∨
    (∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x^140 ∧
      ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i)) := by
  classical
  rcases actual_rp5_paper_reduction G U Y x y hout hfree hx hxy hySmall hN with
    hclean | hblock | ⟨T, P, hP, hmass⟩
  · exact Or.inl hclean
  · exact Or.inr (Or.inr hblock)
  · have hy : 0 < y := hx.trans_le hxy
    obtain ⟨ht, htLower, htUpper, _⟩ := paper_tree_parameter_bounds x y hx hxy hySmall
    have ht0 : (0 : ℝ) < Nat.ceil (1/y^4) := by
      exact_mod_cast (show 0 < Nat.ceil (1/y^4) by omega)
    have hY : 0 < (Y.card : ℝ) := (show 0 < 1/x^600 by positivity).trans_le hN
    exact Or.inr (Or.inl (actual_negative_direction_conclusion hP hout hfree y hy hySmall
      hY (Nat.ceil (1/y^4)) ht0 htLower htUpper rfl hmass))

#print rp5_tooth
#print axioms rp5_tooth
end AllPathsLocal
