import RP5UnaryLayers

namespace AllPathsLocal

theorem cut_atoms_disjoint_retained_child {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {u : V}
    (s : ℝ) (cut : RootCut G S u) {K : Finset V}
    (hK : K ∈ retainedCutChildren s cut) : Disjoint (cutAtoms s cut) K := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvK
  obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp hv
  have hLm := Finset.mem_filter.mp hL
  have hKm := Finset.mem_filter.mp hK
  have hLK : L ≠ K := by
    intro heq
    exact not_lt_of_ge hKm.2 (heq ▸ hLm.2)
  exact Finset.disjoint_left.mp (cut_children_disjoint cut L hLm.1 K hKm.1 hLK) hvL hvK

theorem actual_path_subsets_and_roots {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) : ∀ a ∈ P, a.S ⊆ S ∧ a.u ∈ U := by
  induction hP with
  | terminal S u hu large degree cut below hn =>
    intro a ha
    have heq := List.mem_singleton.mp ha
    subst a
    exact ⟨Finset.Subset.refl S, hu⟩
  | step S u hu large degree cut below K hK path ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨Finset.Subset.refl S, hu⟩
    · exact ⟨(ih a ha).1.trans (cut_children_subset cut K (Finset.mem_filter.mp hK).1),
        (ih a ha).2⟩

def ForwardCutLaw {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a b : RootCutStage G) : Prop :=
  b.S ⊆ a.S ∧ Disjoint (cutAtoms s a.cut) b.S ∧
    ((retainedCutChildren s a.cut).card = 1 →
      a.cut.A ∈ retainedCutChildren s a.cut → ∀ v ∈ b.S, ¬ G.Adj a.u v) ∧
    ((retainedCutChildren s a.cut).card = 1 →
      a.cut.A ∉ retainedCutChildren s a.cut → ∀ v ∈ b.S, G.Adj a.u v)

/-- Every later graph cut lies in the chosen continuation. Unary positive roots
    are anti to every later vertex; unary negative roots are full to every later
    vertex. Atoms remain disjoint even when branching nodes intervene. -/
theorem actual_path_forward_laws {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) : P.Pairwise (ForwardCutLaw s) := by
  classical
  induction hP with
  | terminal => exact List.pairwise_singleton _ _
  | step S u hu large degree cut below K hK path ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro b hb
    have hbK := (actual_path_subsets_and_roots path b hb).1
    have hKm := Finset.mem_filter.mp hK
    refine ⟨hbK.trans (cut_children_subset cut K hKm.1),
      (cut_atoms_disjoint_retained_child s cut hK).mono (Finset.Subset.refl _) hbK, ?_, ?_⟩
    · intro hn hA v hv
      have hKA := unary_retained_child_unique s cut hn hA K hK
      have hvA : v ∈ cut.A := hKA ▸ hbK hv
      rw [cut.remainder] at hvA
      obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
      intro huv
      exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)
    · intro _ hA v hv
      have hKC : K ∈ cut.C := by
        rcases Finset.mem_insert.mp hKm.1 with heq | hKC
        · exact False.elim (hA (heq ▸ hK))
        · exact hKC
      exact (Finset.mem_filter.mp ((cut.component K hKC).1 (hbK hv))).2

theorem actual_path_atoms_pairwise_disjoint {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    (P.map (fun a => cutAtoms s a.cut)).Pairwise Disjoint := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp ?_ (actual_path_forward_laws hP)
  intro a b hab
  apply hab.2.1.mono (Finset.Subset.refl _)
  intro v hv
  obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
  exact cut_children_subset b.cut K (Finset.mem_filter.mp hK).1 hvK

#print axioms cut_atoms_disjoint_retained_child
#print axioms actual_path_subsets_and_roots
#print axioms actual_path_forward_laws
#print axioms actual_path_atoms_pairwise_disjoint

end AllPathsLocal
