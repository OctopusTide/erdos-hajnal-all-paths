import RP5PathGeometry

namespace AllPathsLocal

theorem few_leaves_labelled_path_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t) (hfew : treeLeafCount T.toWeighted < t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∃ Q, ActualRetainedPath T Q ∧
      (S.card : ℝ) / t - 2 * (t + 1) * s ≤
        unaryPathMass (Q.map (RootCutStage.weight s)) := by
  obtain ⟨Q, hQ, hmass⟩ := actual_labelled_path_budget T hSY hs t ht hno
  have hq0 : (0 : ℝ) < treeLeafCount T.toWeighted := by
    exact_mod_cast (show 0 < treeLeafCount T.toWeighted by
      have h := tree_leaf_count_positive T.toWeighted; omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hqt : (treeLeafCount T.toWeighted : ℝ) ≤ t := by
    exact_mod_cast hfew.le
  have hratio : (S.card : ℝ) / t ≤ (S.card : ℝ) / treeLeafCount T.toWeighted := by
    apply (div_le_div_iff₀ ht0 hq0).mpr
    exact mul_le_mul_of_nonneg_left hqt (Nat.cast_nonneg S.card)
  have hp : (S.card : ℝ) / treeLeafCount T.toWeighted ≤
      unaryPathMass (Q.map (RootCutStage.weight s)) + 2 * (t + 1) * s := by
    apply (div_le_iff₀ hq0).mpr
    nlinarith
  exact ⟨Q, hQ, by linarith⟩

/-- Build the actual tree, prune it, and obtain either a large actual frontier
    or a labelled full path with the paper's unary mass bound. The excluded
    outputs are exactly the clean-node and complete-blockade alternatives. -/
theorem actual_tree_frontier_or_path {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V) (x s : ℝ)
    (hx : 0 < x) (hs : 0 < s) (hlarge : s ≤ (Y.card : ℝ))
    (t : ℕ) (ht : 2 ≤ t)
    (hclean : ∀ K ⊆ Y, s ≤ (K.card : ℝ) → ¬ FullOrSmall G U x K)
    (hcomplete : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    (∃ Z, OrderedCutFrontier G U Y Z ∧ t ≤ Z.length ∧
      ∀ K ∈ Z, s ≤ (K.card : ℝ)) ∨
    (∃ T : RetainedCutTree G U x s Y, ∃ Q, ActualRetainedPath T Q ∧
      (Y.card : ℝ) / t - 2 * (t + 1) * s ≤
        unaryPathMass (Q.map (RootCutStage.weight s))) := by
  obtain ⟨tree⟩ := finite_root_cut_tree_exists G U x s hx hs Y
  obtain ⟨T⟩ := cut_tree_prune G U x s tree (Finset.Subset.refl Y) hlarge hclean
  by_cases hq : t ≤ treeLeafCount T.toWeighted
  · obtain ⟨Z, hZ, hsize, hlength⟩ := retained_terminal_frontier G T
    exact Or.inl ⟨Z, hZ, by simpa only [hlength] using hq, hsize⟩
  · obtain ⟨Q, hQ, hmass⟩ := few_leaves_labelled_path_mass T (Finset.Subset.refl Y)
      hs.le t ht (Nat.lt_of_not_ge hq) hcomplete
    exact Or.inr ⟨T, Q, hQ, hmass⟩

#print axioms few_leaves_labelled_path_mass
#print axioms actual_tree_frontier_or_path

end AllPathsLocal
