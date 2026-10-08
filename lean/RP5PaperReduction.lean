import RP5YParameters

namespace AllPathsLocal

/-- The original x/y hypotheses, original clean size y^26|Y| and original
    integer blockade bounds are all closed. The large negative-path branch is
    retained explicitly because Hayward and the thin-layer lemma are unfinished. -/
theorem actual_rp5_paper_reduction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V) (x y : ℝ)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hx : 0 < x) (hxy : x ≤ y) (hySmall : y ≤ 1 / 2^16)
    (hN : 1 / x^600 ≤ (Y.card : ℝ)) :
    (∃ A ⊆ Y, y^26 * Y.card ≤ (A.card : ℝ) ∧ FullOrSmall G U x A) ∨
    (∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x^140 ∧
      ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i)) ∨
    (∃ T : RetainedCutTree G U x ((Y.card : ℝ) / (Nat.ceil (1 / y^4) : ℝ)^6) Y,
      ∃ P, ActualRetainedPath T P ∧
        3 * (Y.card : ℝ) / (8 * (Nat.ceil (1 / y^4) : ℝ)) ≤
          (P.map (fun a => ((negativeLayer ((Y.card : ℝ) / (Nat.ceil (1 / y^4) : ℝ)^6) a).card : ℝ))).sum) := by
  have hy : 0 < y := hx.trans_le hxy
  let t := Nat.ceil (1 / y^4)
  let s := (Y.card : ℝ) / (t : ℝ)^6
  obtain ⟨ht, htLower, htUpperY, htUpperX⟩ := paper_tree_parameter_bounds x y hx hxy hySmall
  rcases actual_rp5_reduction G U Y x s hout hfree hx (hxy.trans hySmall) t ht htUpperX hN rfl with
    ⟨A, hAY, hsize, hfull⟩ | ⟨K, hlo, hup, γ, hγm, htypes⟩ | hnegative
  · left
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    exact ⟨A, hAY, (clean_node_y_size y (t : ℝ) (Y.card : ℝ) hy hySmall ht0
      (Nat.cast_nonneg _) htUpperY).trans hsize, hfull⟩
  · exact Or.inr (Or.inl ⟨K, paper_output_length_lower y (K : ℝ) hy (Nat.cast_nonneg _) (htLower.trans hlo),
      hup, γ, hγm, htypes⟩)
  · exact Or.inr (Or.inr hnegative)

#print axioms actual_rp5_paper_reduction

end AllPathsLocal
