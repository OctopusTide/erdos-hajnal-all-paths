import RP5ExceptionBudget

namespace AllPathsLocal

structure RootCutStage {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  S : Finset V
  u : V
  cut : RootCut G S u

noncomputable def RootCutStage.weight {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) : ℕ × ℝ :=
  ((retainedCutChildren s a.cut).card, (cutAtoms s a.cut).card)

inductive ActualRetainedPath {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ} :
    {S : Finset V} → RetainedCutTree G U x s S → List (RootCutStage G) → Prop
  | terminal (S : Finset V) (u : V) (hu : u ∈ U) (large : s ≤ (S.card : ℝ))
      (degree : x * S.card / 4 ≤ ((EHP6.nbrs G u S).card : ℝ))
      (cut : RootCut G S u)
      (below : ∀ K, K ∈ retainedCutChildren s cut → RetainedCutTree G U x s K)
      (hn : (retainedCutChildren s cut).card = 0) :
      ActualRetainedPath (.node S u hu large degree cut below) [⟨S, u, cut⟩]
  | step (S : Finset V) (u : V) (hu : u ∈ U) (large : s ≤ (S.card : ℝ))
      (degree : x * S.card / 4 ≤ ((EHP6.nbrs G u S).card : ℝ))
      (cut : RootCut G S u)
      (below : ∀ K, K ∈ retainedCutChildren s cut → RetainedCutTree G U x s K)
      (K : Finset V) (hK : K ∈ retainedCutChildren s cut)
      {P : List (RootCutStage G)} (path : ActualRetainedPath (below K hK) P) :
      ActualRetainedPath (.node S u hu large degree cut below) (⟨S, u, cut⟩ :: P)

theorem full_weight_path_node_cases (w : ℝ) (n : ℕ) (child : Fin n → WeightedTree)
    (P : List (ℕ × ℝ)) (hP : FullWeightPath (.node w n child) P) :
    (n = 0 ∧ P = [(0, w)]) ∨
      ∃ i Q, P = (n, w) :: Q ∧ FullWeightPath (child i) Q := by
  cases hP with
  | terminal => exact Or.inl ⟨rfl, rfl⟩
  | step w child i below => exact Or.inr ⟨i, _, rfl, below⟩

/-- Lift the numerical full path to actual graph cuts, retaining every original
    vertex set, root, component family and chosen child. -/
theorem retained_weight_path_lift {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} (T : RetainedCutTree G U x s S)
    {P : List (ℕ × ℝ)} (hP : FullWeightPath T.toWeighted P) :
    ∃ Q, ActualRetainedPath T Q ∧ Q.map (RootCutStage.weight s) = P := by
  classical
  induction T generalizing P with
  | node S u hu large degree cut below ih =>
    let L := retainedCutChildren s cut
    obtain h | ⟨i, R, hR, hbelow⟩ := full_weight_path_node_cases
      ((cutAtoms s cut).card : ℝ) L.card
      (fun i => (below (L.equivFin.symm i).val (L.equivFin.symm i).prop).toWeighted) P hP
    · refine ⟨[⟨S, u, cut⟩], ActualRetainedPath.terminal S u hu large degree cut below h.1, ?_⟩
      simp only [List.map_cons, List.map_nil, RootCutStage.weight]
      change [(L.card, ((cutAtoms s cut).card : ℝ))] = P
      rw [h.1, h.2]
    · obtain ⟨Q, hQ, hmap⟩ := ih (L.equivFin.symm i).val (L.equivFin.symm i).prop hbelow
      refine ⟨⟨S, u, cut⟩ :: Q,
        ActualRetainedPath.step S u hu large degree cut below _ _ hQ, ?_⟩
      simp only [List.map_cons, RootCutStage.weight, hmap]
      exact hR.symm

theorem actual_labelled_path_budget {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∃ Q, ActualRetainedPath T Q ∧
      (S.card : ℝ) - 2 * treeLeafCount T.toWeighted * ((t + 1) * s) ≤
        treeLeafCount T.toWeighted * unaryPathMass (Q.map (RootCutStage.weight s)) := by
  obtain ⟨P, hP, hmass⟩ := retained_full_path_budget T hSY hs t ht hno
  obtain ⟨Q, hQ, hmap⟩ := retained_weight_path_lift T hP
  exact ⟨Q, hQ, by simpa only [hmap] using hmass⟩

#print axioms full_weight_path_node_cases
#print axioms retained_weight_path_lift
#print axioms actual_labelled_path_budget

end AllPathsLocal
