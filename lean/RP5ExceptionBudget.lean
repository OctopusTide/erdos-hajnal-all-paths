import RP5AtomBudget

namespace AllPathsLocal

theorem retained_exception_budget {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    treeExceptionBound ((t + 1) * s) T.toWeighted := by
  classical
  induction T with
  | node S u hu large degree cut below ih =>
    constructor
    · intro _
      exact cut_atom_budget G cut hSY s hs t ht hno
    · intro i
      apply ih _ _
      exact (cut_children_subset cut _
        (Finset.mem_filter.mp ((retainedCutChildren s cut).equivFin.symm i).prop).1).trans hSY

theorem retained_exception_mass_leaf_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    treeExceptionMass T.toWeighted ≤ 2 * treeLeafCount T.toWeighted * ((t + 1) * s) := by
  have h := tree_exception_mass_bound ((t + 1) * s) T.toWeighted
    (retained_exception_budget T hSY hs t ht hno)
  have hcount : (treeExceptionCount T.toWeighted : ℝ) ≤ 2 * treeLeafCount T.toWeighted := by
    exact_mod_cast (show treeExceptionCount T.toWeighted ≤ 2 * treeLeafCount T.toWeighted by
      have h := tree_exception_count_bound T.toWeighted; omega)
  have ha : (0 : ℝ) ≤ (t + 1) * s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcount ha]

theorem retained_full_path_budget {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∃ P, FullWeightPath T.toWeighted P ∧
      (S.card : ℝ) - 2 * treeLeafCount T.toWeighted * ((t + 1) * s) ≤
        treeLeafCount T.toWeighted * unaryPathMass P := by
  obtain ⟨P, hP, hmass⟩ := retained_full_path_mass T
  have he := retained_exception_mass_leaf_bound T hSY hs t ht hno
  exact ⟨P, hP, by linarith⟩

#print axioms retained_exception_budget
#print axioms retained_exception_mass_leaf_bound
#print axioms retained_full_path_budget

end AllPathsLocal
