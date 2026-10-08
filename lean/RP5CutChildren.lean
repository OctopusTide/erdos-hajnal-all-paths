import RP5TreeMass
import RP5CutTree

namespace AllPathsLocal

open scoped BigOperators

def cutChildren {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : Finset (Finset V) := insert cut.A cut.C

noncomputable def retainedCutChildren {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) : Finset (Finset V) := by
  classical
  exact (cutChildren cut).filter (fun K => s ≤ (K.card : ℝ))

noncomputable def smallCutChildren {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) : Finset (Finset V) := by
  classical
  exact (cutChildren cut).filter (fun K => (K.card : ℝ) < s)

noncomputable def cutAtoms {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) : Finset V :=
  (smallCutChildren s cut).biUnion id

theorem cut_children_cover {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : (cutChildren cut).biUnion id = S := by
  simpa only [cutChildren, Finset.biUnion_insert, id_eq, Finset.union_comm] using cut.cover

theorem cut_children_subset {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : ∀ K ∈ cutChildren cut, K ⊆ S := by
  intro K hK
  rcases Finset.mem_insert.mp hK with rfl | hK
  · exact cut.properA.subset
  · exact (cut.properC K hK).subset

theorem cut_children_disjoint {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (cut : RootCut G S u) : ∀ K ∈ cutChildren cut, ∀ L ∈ cutChildren cut,
      K ≠ L → Disjoint K L := by
  intro K hK L hL hKL
  rcases Finset.mem_insert.mp hK with rfl | hK
  · rcases Finset.mem_insert.mp hL with rfl | hL
    · exact False.elim (hKL rfl)
    · exact (cut.disjointA L hL).symm
  · rcases Finset.mem_insert.mp hL with rfl | hL
    · exact cut.disjointA K hK
    · exact cut.disjointC K hK L hL hKL

theorem cut_children_threshold_partition {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) :
    smallCutChildren s cut ∪ retainedCutChildren s cut = cutChildren cut ∧
      Disjoint (smallCutChildren s cut) (retainedCutChildren s cut) := by
  classical
  constructor
  · ext K
    simp only [smallCutChildren, retainedCutChildren, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases lt_or_ge (K.card : ℝ) s with hsmall | hlarge
      · exact Or.inl ⟨h, hsmall⟩
      · exact Or.inr ⟨h, hlarge⟩
  · apply Finset.disjoint_left.mpr
    intro K hsmall hlarge
    exact (not_lt_of_ge (Finset.mem_filter.mp hlarge).2) (Finset.mem_filter.mp hsmall).2

/-- Exact integer mass partition at each actual root cut. -/
theorem cut_child_mass_partition {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) :
    S.card = (cutAtoms s cut).card + ∑ K ∈ retainedCutChildren s cut, K.card := by
  classical
  have hall : S.card = ∑ K ∈ cutChildren cut, K.card := by
    have h := Finset.card_biUnion (s := cutChildren cut) (t := id)
      (cut_children_disjoint cut)
    rwa [cut_children_cover cut] at h
  have hatoms : (cutAtoms s cut).card = ∑ K ∈ smallCutChildren s cut, K.card := by
    apply Finset.card_biUnion
    intro K hK L hL hKL
    exact cut_children_disjoint cut K (Finset.mem_filter.mp hK).1
      L (Finset.mem_filter.mp hL).1 hKL
  obtain ⟨hunion, hdisj⟩ := cut_children_threshold_partition s cut
  calc
    S.card = ∑ K ∈ cutChildren cut, K.card := hall
    _ = (∑ K ∈ smallCutChildren s cut, K.card) + ∑ K ∈ retainedCutChildren s cut, K.card := by
      rw [← hunion]
      exact Finset.sum_union hdisj
    _ = (cutAtoms s cut).card + ∑ K ∈ retainedCutChildren s cut, K.card := by rw [hatoms]

theorem sum_fin_equivFin {α M : Type} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (∑ i : Fin s.card, f (s.equivFin.symm i).val) = ∑ a ∈ s, f a := by
  classical
  have h := Equiv.sum_comp s.equivFin.symm (fun a : s => f a.val)
  rw [Finset.sum_coe_sort] at h
  exact h

#print axioms cut_children_cover
#print axioms cut_children_subset
#print axioms cut_children_disjoint
#print axioms cut_children_threshold_partition
#print axioms cut_child_mass_partition
#print axioms sum_fin_equivFin

end AllPathsLocal
