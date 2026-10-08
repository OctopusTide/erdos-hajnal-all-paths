import RP5CutChildren

namespace AllPathsLocal

open scoped BigOperators

/-- An actual root-cut tree pruned at size s. The retained children are precisely
    the large original children; the atom weight is the union of all small children. -/
inductive RetainedCutTree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ) : Finset V → Type
  | node (S : Finset V) (u : V) (hu : u ∈ U) (large : s ≤ (S.card : ℝ))
      (degree : x * S.card / 4 ≤ ((EHP6.nbrs G u S).card : ℝ))
      (cut : RootCut G S u)
      (below : ∀ K, K ∈ retainedCutChildren s cut → RetainedCutTree G U x s K) :
      RetainedCutTree G U x s S

/-- Pruning is constructed from the previously proved finite tree. The no-clean
    hypothesis is the negation of the RP5 Tooth clean alternative, not a new axiom. -/
theorem cut_tree_prune {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ)
    {S Y : Finset V} (tree : CutTree G U x s S)
    (hSY : S ⊆ Y) (hlarge : s ≤ (S.card : ℝ))
    (hno : ∀ K ⊆ Y, s ≤ (K.card : ℝ) → ¬ FullOrSmall G U x K) :
    Nonempty (RetainedCutTree G U x s S) := by
  classical
  revert hSY hlarge
  induction tree with
  | leaf S stop =>
    intro hSY hlarge
    rcases stop with hsmall | hclean
    · exact False.elim (not_lt_of_ge hlarge hsmall)
    · exact False.elim (hno S hSY hlarge hclean)
  | split S u hu large degree cut belowC belowA ihC ihA =>
    intro hSY _
    have hbelow : ∀ K, K ∈ retainedCutChildren s cut →
        Nonempty (RetainedCutTree G U x s K) := by
      intro K hK
      have hm := Finset.mem_filter.mp hK
      rcases Finset.mem_insert.mp hm.1 with rfl | hKC
      · exact ihA (cut.properA.subset.trans hSY) hm.2
      · exact ihC K hKC ((cut.properC K hKC).subset.trans hSY) hm.2
    exact ⟨RetainedCutTree.node S u hu large degree cut
      (fun K hK => Classical.choice (hbelow K hK))⟩

noncomputable def RetainedCutTree.toWeighted {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S) : WeightedTree :=
  match T with
  | .node _ _ _ _ _ cut below =>
    let L := retainedCutChildren s cut
    WeightedTree.node ((cutAtoms s cut).card : ℝ) L.card (fun i =>
      (below (L.equivFin.symm i).val (L.equivFin.symm i).prop).toWeighted)

theorem retained_weighted_nonnegative {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S) : treeNonnegative T.toWeighted := by
  induction T with
  | node S u hu large degree cut below ih =>
    constructor
    · positivity
    · intro i
      exact ih _ _

/-- All atom weights in the actual pruned tree sum to the ORIGINAL root size.
    This follows from integer child partitions at every actual cut. -/
theorem retained_weighted_total_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S) : treeTotalMass T.toWeighted = S.card := by
  classical
  induction T with
  | node S u hu large degree cut below ih =>
    change ((cutAtoms s cut).card : ℝ) +
      (∑ i : Fin (retainedCutChildren s cut).card,
        treeTotalMass ((below ((retainedCutChildren s cut).equivFin.symm i).val
          ((retainedCutChildren s cut).equivFin.symm i).prop).toWeighted)) = S.card
    simp only [ih]
    rw [sum_fin_equivFin (retainedCutChildren s cut) (fun K => (K.card : ℝ))]
    exact_mod_cast (cut_child_mass_partition s cut).symm

/-- The generic FULL-path bound now applies to a real pruned graph-cut tree,
    with its exact original-root mass. -/
theorem retained_full_path_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S) :
    ∃ P, FullWeightPath T.toWeighted P ∧
      (S.card : ℝ) - treeExceptionMass T.toWeighted ≤ treeLeafCount T.toWeighted * unaryPathMass P := by
  obtain ⟨P, hP, hmass⟩ := full_path_carries_unary_mass T.toWeighted (retained_weighted_nonnegative T)
  have hp := tree_mass_partition T.toWeighted
  rw [retained_weighted_total_mass T] at hp
  exact ⟨P, hP, by nlinarith⟩

/-- Existence and path extraction together: the actual finite tree is built and
    pruned here, rather than being supplied as an unproved mathematical premise. -/
theorem actual_root_cut_path_mass {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V) (x s : ℝ)
    (hx : 0 < x) (hs : 0 < s) (hlarge : s ≤ (Y.card : ℝ))
    (hno : ∀ K ⊆ Y, s ≤ (K.card : ℝ) → ¬ FullOrSmall G U x K) :
    ∃ T : RetainedCutTree G U x s Y, ∃ P, FullWeightPath T.toWeighted P ∧
      (Y.card : ℝ) - treeExceptionMass T.toWeighted ≤ treeLeafCount T.toWeighted * unaryPathMass P := by
  obtain ⟨tree⟩ := finite_root_cut_tree_exists G U x s hx hs Y
  obtain ⟨T⟩ := cut_tree_prune G U x s tree (Finset.Subset.refl Y) hlarge hno
  obtain ⟨P, hP, hmass⟩ := retained_full_path_mass T
  exact ⟨T, P, hP, hmass⟩

#print axioms cut_tree_prune
#print axioms retained_weighted_nonnegative
#print axioms retained_weighted_total_mass
#print axioms retained_full_path_mass
#print axioms actual_root_cut_path_mass

end AllPathsLocal
