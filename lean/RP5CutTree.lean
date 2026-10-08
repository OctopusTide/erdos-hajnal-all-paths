import RP5RootCut

/-! The finite rooted-cut tree from III.5. It is built by strict subset recursion,
    stops at small or clean sets, and remembers every split root's degree lower bound. -/

namespace AllPathsLocal

def FullOrSmall {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x : ℝ) (S : Finset V) : Prop :=
  ∀ u ∈ U, (∀ v ∈ S, G.Adj u v) ∨ ((EHP6.nbrs G u S).card : ℝ) < x * S.card / 4

theorem exists_bad_root_cut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) (x : ℝ) (hx : 0 < x) (hS : S.Nonempty)
    (hbad : ¬ FullOrSmall G U x S) :
    ∃ u ∈ U, x * S.card / 4 ≤ ((EHP6.nbrs G u S).card : ℝ) ∧
      Nonempty (RootCut G S u) := by
  classical
  unfold FullOrSmall at hbad
  push Not at hbad
  obtain ⟨u, hu, hnotfull, hlower⟩ := hbad
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hNposR : (0 : ℝ) < (EHP6.nbrs G u S).card :=
    lt_of_lt_of_le (by positivity) hlower
  have hNpos : 0 < (EHP6.nbrs G u S).card := by exact_mod_cast hNposR
  have hNne : EHP6.nbrs G u S ≠ S := by
    intro heq
    obtain ⟨v, hv, hnonadj⟩ := hnotfull
    have hvN : v ∈ EHP6.nbrs G u S := by rw [heq]; exact hv
    exact hnonadj (Finset.mem_filter.mp hvN).2
  have hproper : EHP6.nbrs G u S ⊂ S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, hNne⟩
  exact ⟨u, hu, hlower, exists_root_cut G S u hNpos (Finset.card_lt_card hproper)⟩

inductive CutTree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ) : Finset V → Type
  | leaf (S : Finset V) (stop : (S.card : ℝ) < s ∨ FullOrSmall G U x S) :
      CutTree G U x s S
  | split (S : Finset V) (u : V) (hu : u ∈ U) (large : s ≤ (S.card : ℝ))
      (degree : x * S.card / 4 ≤ ((EHP6.nbrs G u S).card : ℝ))
      (cut : RootCut G S u)
      (belowC : ∀ K, K ∈ cut.C → CutTree G U x s K)
      (belowA : CutTree G U x s cut.A) : CutTree G U x s S

/-- Strict proper-subset induction constructs the whole finite tree; its existence
    is not an axiom and does not assume any form of the RP5 Tooth conclusion. -/
theorem finite_root_cut_tree_exists {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (x s : ℝ)
    (hx : 0 < x) (hs : 0 < s) (S : Finset V) : Nonempty (CutTree G U x s S) := by
  classical
  refine Finset.strongInductionOn S ?_
  intro T ih
  by_cases hsmall : (T.card : ℝ) < s
  · exact ⟨CutTree.leaf T (Or.inl hsmall)⟩
  by_cases hclean : FullOrSmall G U x T
  · exact ⟨CutTree.leaf T (Or.inr hclean)⟩
  have hlarge : s ≤ (T.card : ℝ) := le_of_not_gt hsmall
  have hSc : (0 : ℝ) < T.card := hs.trans_le hlarge
  have hT : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSc)
  obtain ⟨u, hu, hdegree, ⟨cut⟩⟩ := exists_bad_root_cut G U T x hx hT hclean
  let belowC : ∀ K, K ∈ cut.C → CutTree G U x s K :=
    fun K hK => Classical.choice (ih K (cut.properC K hK))
  let belowA : CutTree G U x s cut.A := Classical.choice (ih cut.A cut.properA)
  exact ⟨CutTree.split T u hu hlarge hdegree cut belowC belowA⟩

#print axioms exists_bad_root_cut
#print axioms finite_root_cut_tree_exists

end AllPathsLocal
