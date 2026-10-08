import RP5QuantitativeFrontier

/-! Finite tree accounting for III.5. This is a combinatorial dependency; the
    integration with the actual pruned rooted-cut tree is a subsequent obligation. -/

namespace AllPathsLocal

open scoped BigOperators

inductive WeightedTree : Type
  | node (weight : ℝ) (arity : ℕ) (children : Fin arity → WeightedTree)

def treeLeafCount : WeightedTree → ℕ
  | .node _ n child => if n = 0 then 1 else ∑ i, treeLeafCount (child i)

def treeBranchCount : WeightedTree → ℕ
  | .node _ n child => (if 2 ≤ n then 1 else 0) + ∑ i, treeBranchCount (child i)

def treeExceptionCount : WeightedTree → ℕ
  | .node _ n child => (if n = 1 then 0 else 1) + ∑ i, treeExceptionCount (child i)

def treeUnaryMass : WeightedTree → ℝ
  | .node w n child => (if n = 1 then w else 0) + ∑ i, treeUnaryMass (child i)

def treeTotalMass : WeightedTree → ℝ
  | .node w _ child => w + ∑ i, treeTotalMass (child i)

def treeExceptionMass : WeightedTree → ℝ
  | .node w n child => (if n = 1 then 0 else w) + ∑ i, treeExceptionMass (child i)

def treeExceptionBound (a : ℝ) : WeightedTree → Prop
  | .node w n child => (n ≠ 1 → w ≤ a) ∧ ∀ i, treeExceptionBound a (child i)

def treeNonnegative : WeightedTree → Prop
  | .node w _ child => 0 ≤ w ∧ ∀ i, treeNonnegative (child i)

inductive FullWeightPath : WeightedTree → List (ℕ × ℝ) → Prop
  | terminal (w : ℝ) (child : Fin 0 → WeightedTree) :
      FullWeightPath (.node w 0 child) [(0, w)]
  | step (w : ℝ) {n : ℕ} (child : Fin n → WeightedTree) (i : Fin n)
      {P : List (ℕ × ℝ)} (below : FullWeightPath (child i) P) :
      FullWeightPath (.node w n child) ((n, w) :: P)

def unaryPathMass (P : List (ℕ × ℝ)) : ℝ :=
  (P.map (fun nw => if nw.1 = 1 then nw.2 else 0)).sum

theorem tree_leaf_count_positive (T : WeightedTree) : 1 ≤ treeLeafCount T := by
  induction T with
  | node w n child ih =>
    by_cases hn : n = 0
    · simp [treeLeafCount, hn]
    · have hn0 : 0 < n := by omega
      let i : Fin n := ⟨0, hn0⟩
      have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (treeLeafCount (child j)))
        (Finset.mem_univ i)
      exact (ih i).trans (by simpa [treeLeafCount, hn] using hi)

theorem tree_branch_count_bound (T : WeightedTree) : treeBranchCount T + 1 ≤ treeLeafCount T := by
  induction T with
  | node w n child ih =>
    by_cases hn : n = 0
    · subst n
      simp [treeLeafCount, treeBranchCount]
    · have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => ih i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] at hs
      simp only [treeLeafCount, hn, if_false, treeBranchCount]
      by_cases hbranch : 2 ≤ n
      · rw [if_pos hbranch]
        omega
      · rw [if_neg hbranch]
        omega

theorem tree_exception_count_eq (T : WeightedTree) :
    treeExceptionCount T = treeLeafCount T + treeBranchCount T := by
  induction T with
  | node w n child ih =>
    have hs : (∑ i, treeExceptionCount (child i)) =
        (∑ i, treeLeafCount (child i)) + ∑ i, treeBranchCount (child i) := by
      simp only [ih, Finset.sum_add_distrib]
    by_cases hn0 : n = 0
    · subst n
      simp [treeExceptionCount, treeLeafCount, treeBranchCount]
    by_cases hn1 : n = 1
    · simp [treeExceptionCount, treeLeafCount, treeBranchCount, hn0, hn1, hs]
    · have hn2 : 2 ≤ n := by omega
      simp only [treeExceptionCount, treeLeafCount, treeBranchCount,
        if_neg hn0, if_neg hn1, if_pos hn2, hs]
      omega

/-- Count full paths with leaf multiplicity. No uninterrupted unary segment is
    assumed: branching nodes may occur, with their weights omitted. -/
theorem full_path_carries_unary_mass (T : WeightedTree) (hT : treeNonnegative T) :
    ∃ P, FullWeightPath T P ∧ treeUnaryMass T ≤ treeLeafCount T * unaryPathMass P := by
  induction T with
  | node w n child ih =>
    have hw := hT.1
    have hc := hT.2
    by_cases hn : n = 0
    · subst n
      exact ⟨[(0, w)], FullWeightPath.terminal w child, by simp [treeUnaryMass, treeLeafCount, unaryPathMass]⟩
    have hn0 : 0 < n := by omega
    have hpaths : ∀ i, ∃ P, FullWeightPath (child i) P ∧
        treeUnaryMass (child i) ≤ treeLeafCount (child i) * unaryPathMass P :=
      fun i => ih i (hc i)
    choose P hP hmass using hpaths
    let Q : ℝ := ∑ i : Fin n, (treeLeafCount (child i) : ℝ)
    let M : ℝ := ∑ i : Fin n, treeUnaryMass (child i)
    have hQeq : Q = treeLeafCount (.node w n child) := by
      simp [Q, treeLeafCount, hn, Nat.cast_sum]
    have hQ1 : 1 ≤ Q := by rw [hQeq]; exact_mod_cast tree_leaf_count_positive (.node w n child)
    have hQ0 : 0 < Q := by linarith
    have hsum : (∑ i : Fin n, (treeLeafCount (child i) : ℝ) * (M / Q)) ≤
        ∑ i : Fin n, (treeLeafCount (child i) : ℝ) * unaryPathMass (P i) := by
      have hleft : (∑ i : Fin n, (treeLeafCount (child i) : ℝ) * (M / Q)) = M := by
        rw [← Finset.sum_mul]
        change Q * (M / Q) = M
        field_simp
      rw [hleft]
      exact Finset.sum_le_sum (fun i _ => hmass i)
    have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
    obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne hsum
    have hqi0 : (0 : ℝ) < treeLeafCount (child i) := by
      have h := tree_leaf_count_positive (child i)
      exact_mod_cast (show 0 < treeLeafCount (child i) by omega)
    have hratio : M / Q ≤ unaryPathMass (P i) := by nlinarith
    have hMi : M ≤ Q * unaryPathMass (P i) := by
      simpa only [mul_comm] using (div_le_iff₀ hQ0).mp hratio
    have hroot : 0 ≤ (if n = 1 then w else 0) := by split <;> positivity
    have hrootmult : (if n = 1 then w else 0) ≤ Q * (if n = 1 then w else 0) := by
      have h := mul_le_mul_of_nonneg_right hQ1 hroot
      simpa using h
    refine ⟨(n, w) :: P i, FullWeightPath.step w child i (hP i), ?_⟩
    simp only [treeUnaryMass, unaryPathMass, List.map_cons, List.sum_cons, hQeq.symm]
    change (if n = 1 then w else 0) + M ≤ Q * ((if n = 1 then w else 0) + unaryPathMass (P i))
    nlinarith

theorem tree_mass_partition (T : WeightedTree) :
    treeTotalMass T = treeUnaryMass T + treeExceptionMass T := by
  induction T with
  | node w n child ih =>
    simp only [treeTotalMass, treeUnaryMass, treeExceptionMass, ih, Finset.sum_add_distrib]
    by_cases hn : n = 1 <;> simp only [hn, ite_true, ite_false] <;> ring

theorem tree_exception_mass_bound (a : ℝ) (T : WeightedTree)
    (hT : treeExceptionBound a T) : treeExceptionMass T ≤ a * treeExceptionCount T := by
  induction T with
  | node w n child ih =>
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i _ => ih i (hT.2 i))
    rw [← Finset.mul_sum] at hs
    by_cases hn : n = 1
    · simpa [treeExceptionMass, treeExceptionCount, hn, Nat.cast_sum] using hs
    · have hw := hT.1 hn
      simp only [treeExceptionMass, treeExceptionCount, if_neg hn, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      nlinarith

theorem tree_exception_count_bound (T : WeightedTree) :
    treeExceptionCount T + 1 ≤ 2 * treeLeafCount T := by
  rw [tree_exception_count_eq]
  have h := tree_branch_count_bound T
  omega

#print axioms tree_leaf_count_positive
#print axioms tree_branch_count_bound
#print axioms tree_exception_count_eq
#print axioms full_path_carries_unary_mass
#print axioms tree_mass_partition
#print axioms tree_exception_mass_bound
#print axioms tree_exception_count_bound

end AllPathsLocal
