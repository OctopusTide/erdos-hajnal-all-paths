import RP5RootCut
import Mathlib.Data.List.OfFn

/-! Ordered frontiers of actual rooted cuts. Components are enumerated in one fixed order,
    and the nonneighbor child is appended last. Skipping a subtree or stopping at it
    describes arbitrary antichains, rather than only terminal leaves. -/

namespace AllPathsLocal

noncomputable def orderedComponentLists {V : Type} [DecidableEq V]
    (C : Finset (Finset V)) (F : ∀ K, K ∈ C → List (Finset V)) : List (List (Finset V)) :=
  List.ofFn (fun i => F (C.equivFin.symm i).val (C.equivFin.symm i).prop)

inductive OrderedCutFrontier {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    Finset V → List (Finset V) → Prop
  | skip (S : Finset V) : OrderedCutFrontier G U S []
  | stop (S : Finset V) : OrderedCutFrontier G U S [S]
  | split (S : Finset V) (u : V) (hu : u ∈ U) (cut : RootCut G S u)
      (F : ∀ K, K ∈ cut.C → List (Finset V)) (A : List (Finset V))
      (hC : ∀ K hK, OrderedCutFrontier G U K (F K hK))
      (hA : OrderedCutFrontier G U cut.A A) :
      OrderedCutFrontier G U S ((orderedComponentLists cut.C F).flatten ++ A)

def RootedSeparation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U A B : Finset V) : Prop :=
  EHP6.Complete G A B ∨ ∃ u ∈ U,
    (∀ a ∈ A, G.Adj u a) ∧ ∀ b ∈ B, ¬ G.Adj u b

/-- Every ordered frontier pair is complete or has an original root separating it in
    the needed orientation. The root may depend on both members of the pair. -/
theorem ordered_frontier_properties {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z) :
    (∀ K ∈ Z, K ⊆ S) ∧ Z.Pairwise (RootedSeparation G U) := by
  classical
  induction hfront with
  | skip S => simp
  | stop S => simp
  | split S u hu cut F A hC hA ihC ihA =>
    have hsource : ∀ X ∈ (orderedComponentLists cut.C F).flatten,
        ∃ K, ∃ hK : K ∈ cut.C, X ∈ F K hK := by
      intro X hX
      obtain ⟨L, hL, hXL⟩ := List.mem_flatten.mp hX
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
      exact ⟨(cut.C.equivFin.symm i).val, (cut.C.equivFin.symm i).prop, hXL⟩
    constructor
    · intro X hX
      rcases List.mem_append.mp hX with hX | hX
      · obtain ⟨K, hK, hXK⟩ := hsource X hX
        exact ((ihC K hK).1 X hXK).trans (cut.properC K hK).1
      · exact (ihA.1 X hX).trans cut.properA.1
    · apply List.pairwise_append.mpr
      refine ⟨?_, ihA.2, ?_⟩
      · apply List.pairwise_flatten.mpr
        constructor
        · intro L hL
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
          exact (ihC (cut.C.equivFin.symm i).val (cut.C.equivFin.symm i).prop).2
        · apply List.pairwise_ofFn.mpr
          intro i j hij X hX Y hY
          left
          have hne : (cut.C.equivFin.symm i).val ≠ (cut.C.equivFin.symm j).val := by
            intro heq
            exact (ne_of_lt hij) (cut.C.equivFin.symm.injective (Subtype.ext heq))
          intro a ha b hb
          exact cut.completeC _ (cut.C.equivFin.symm i).prop _ (cut.C.equivFin.symm j).prop hne
            a ((ihC _ (cut.C.equivFin.symm i).prop).1 X hX ha)
            b ((ihC _ (cut.C.equivFin.symm j).prop).1 Y hY hb)
      · intro X hX B hB
        obtain ⟨K, hK, hXK⟩ := hsource X hX
        right
        refine ⟨u, hu, ?_, ?_⟩
        · intro v hv
          have hvK := (ihC K hK).1 X hXK hv
          exact (Finset.mem_filter.mp ((cut.component K hK).1 hvK)).2
        · intro v hv
          have hvA := ihA.1 B hB hv
          rw [cut.remainder] at hvA
          obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
          intro huv
          exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)

theorem ordered_frontier_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z) :
    Z.Pairwise Disjoint := by
  classical
  induction hfront with
  | skip S => simp
  | stop S => simp
  | split S u hu cut F A hC hA ihC ihA =>
    apply List.pairwise_append.mpr
    refine ⟨?_, ihA, ?_⟩
    · apply List.pairwise_flatten.mpr
      constructor
      · intro L hL
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
        exact ihC (cut.C.equivFin.symm i).val (cut.C.equivFin.symm i).prop
      · apply List.pairwise_ofFn.mpr
        intro i j hij X hX Y hY
        have hne : (cut.C.equivFin.symm i).val ≠ (cut.C.equivFin.symm j).val := by
          intro heq
          exact (ne_of_lt hij) (cut.C.equivFin.symm.injective (Subtype.ext heq))
        exact (cut.disjointC _ (cut.C.equivFin.symm i).prop _ (cut.C.equivFin.symm j).prop hne).mono
          ((ordered_frontier_properties G U (hC _ (cut.C.equivFin.symm i).prop)).1 X hX)
          ((ordered_frontier_properties G U (hC _ (cut.C.equivFin.symm j).prop)).1 Y hY)
    · intro X hX B hB
      obtain ⟨L, hL, hXL⟩ := List.mem_flatten.mp hX
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
      exact (cut.disjointA _ (cut.C.equivFin.symm i).prop).mono
        ((ordered_frontier_properties G U (hC _ (cut.C.equivFin.symm i).prop)).1 X hXL)
        ((ordered_frontier_properties G U hA).1 B hB)

/-- The exact first-Tooth input of III.1 for every pair in an arbitrary ordered frontier. -/
theorem ordered_frontier_root_law {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    (hSY : S ⊆ Y) (houtside : ∀ u ∈ U, u ∉ Y)
    (hfree : ∀ u ∈ U, RootedP5Free G Y u) :
    Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v) := by
  have hprops := ordered_frontier_properties G U hfront
  have hroot : Z.Pairwise (fun A B => ∀ v ∈ B, RootedP4Free G A v) := by
    apply List.Pairwise.imp_of_mem ?_ hprops.2
    intro A B hA hB hsep v hv
    rcases hsep with hcomplete | ⟨u, hu, huA, huB⟩
    · apply complete_vertex_rootedP4Free G
      intro a ha
      exact G.adj_symm (hcomplete a ha v hv)
    · exact rp5_to_rp4 G (houtside u hu) (hSY (hprops.1 B hB hv))
        ((hprops.1 A hA).trans hSY) (hfree u hu) (huB v hv) huA
  exact (ordered_frontier_disjoint G U hfront).and hroot

#print axioms ordered_frontier_properties
#print axioms ordered_frontier_disjoint
#print axioms ordered_frontier_root_law

end AllPathsLocal
