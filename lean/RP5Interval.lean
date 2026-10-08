import RP5RootFamilies
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn

/-! The interval argument in III.3. A path is an ordered sublist whose consecutive
    pairs are noncomplete. Such a path cannot cross two distinct C-child intervals. -/

namespace AllPathsLocal

open List

theorem chain_confined_to_one_section {α : Type} (R : α → α → Prop)
    (sections : List (List α)) :
    sections.Pairwise (fun A B => ∀ a ∈ A, ∀ b ∈ B, R a b) →
    ∀ P : List α, P <+ sections.flatten → P.IsChain (fun a b => ¬ R a b) →
      P = [] ∨ ∃ A ∈ sections, P <+ A := by
  induction sections with
  | nil =>
    intro _ P hP _
    left
    simpa using hP
  | cons A sections ih =>
    intro hcross P hP hchain
    have hc := List.pairwise_cons.mp hcross
    simp only [List.flatten_cons] at hP
    obtain ⟨P₁, P₂, rfl, hP₁, hP₂⟩ := List.sublist_append_iff.mp hP
    by_cases h₁ : P₁ = []
    · subst P₁
      simp only [List.nil_append] at hchain ⊢
      rcases ih hc.2 P₂ hP₂ hchain with h | ⟨B, hB, hPB⟩
      · exact Or.inl h
      · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, hPB⟩
    by_cases h₂ : P₂ = []
    · subst P₂
      right
      exact ⟨A, List.mem_cons_self, by simpa using hP₁⟩
    have hnot := hchain.rel_getLast_head_of_append h₁ h₂
    have ha := hP₁.getLast_mem h₁
    have hb := hP₂.head_mem h₂
    obtain ⟨B, hB, hbB⟩ := List.mem_flatten.mp hb
    exact False.elim (hnot (hc.1 B hB _ ha _ hbB))

/-- Any two blocks of an increasing noncomplete path in an actual cut frontier have
    a separating ORIGINAL root. No root is assumed common to the whole path. -/
theorem ordered_frontier_path_roots {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z) :
    ∀ P : List (Finset V), P <+ Z → P.IsChain (fun A B => ¬ EHP6.Complete G A B) →
      P.Pairwise (fun A B => ∃ u ∈ U, RootSeparates G u A B) := by
  classical
  induction hfront with
  | skip S =>
    intro P hP _
    have : P = [] := by simpa using hP
    simp [this]
  | stop S =>
    intro P hP _
    exact (show [S].Pairwise (fun A B => ∃ u ∈ U, RootSeparates G u A B) by simp).sublist hP
  | split S u hu cut F A hC hA ihC ihA =>
    intro P hP hchain
    obtain ⟨P₁, P₂, rfl, hP₁, hP₂⟩ := List.sublist_append_iff.mp hP
    have hsource : ∀ X ∈ (orderedComponentLists cut.C F).flatten,
        ∃ K, ∃ hK : K ∈ cut.C, X ∈ F K hK := by
      intro X hX
      obtain ⟨L, hL, hXL⟩ := List.mem_flatten.mp hX
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
      exact ⟨(cut.C.equivFin.symm i).val, (cut.C.equivFin.symm i).prop, hXL⟩
    have hcomplete : (orderedComponentLists cut.C F).Pairwise
        (fun L M => ∀ X ∈ L, ∀ B ∈ M, EHP6.Complete G X B) := by
      apply List.pairwise_ofFn.mpr
      intro i j hij X hX B hB
      have hne : (cut.C.equivFin.symm i).val ≠ (cut.C.equivFin.symm j).val := by
        intro heq
        exact (ne_of_lt hij) (cut.C.equivFin.symm.injective (Subtype.ext heq))
      intro a ha b hb
      exact cut.completeC _ (cut.C.equivFin.symm i).prop _ (cut.C.equivFin.symm j).prop hne
        a ((ordered_frontier_properties G U (hC _ (cut.C.equivFin.symm i).prop)).1 X hX ha)
        b ((ordered_frontier_properties G U (hC _ (cut.C.equivFin.symm j).prop)).1 B hB hb)
    have hleft : P₁.Pairwise (fun X B => ∃ u ∈ U, RootSeparates G u X B) := by
      rcases chain_confined_to_one_section (EHP6.Complete G)
          (orderedComponentLists cut.C F) hcomplete P₁ hP₁ hchain.left_of_append with
        hnil | ⟨L, hL, hPL⟩
      · simp [hnil]
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
        exact ihC _ (cut.C.equivFin.symm i).prop P₁ hPL hchain.left_of_append
    apply List.pairwise_append.mpr
    refine ⟨hleft, ihA P₂ hP₂ hchain.right_of_append, ?_⟩
    intro X hX B hB
    obtain ⟨K, hK, hXK⟩ := hsource X (hP₁.subset hX)
    refine ⟨u, hu, ?_, ?_⟩
    · intro v hv
      have hvK := (ordered_frontier_properties G U (hC K hK)).1 X hXK hv
      exact (Finset.mem_filter.mp ((cut.component K hK).1 hvK)).2
    · intro v hv
      have hvA := (ordered_frontier_properties G U hA).1 B (hP₂.subset hB) hv
      rw [cut.remainder] at hvA
      obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
      intro huv
      exact hvN (Finset.mem_filter.mpr ⟨hvS, huv⟩)

/-- The interval/root theorem applies to concrete strictly increasing index sequences,
    including the sequences extracted from IncreasingQPath certificates. -/
theorem ordered_frontier_increasing_path_roots {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    {n : ℕ} (f : Fin n → Fin Z.length) (hf : StrictMono f)
    (hlinks : ∀ a b : Fin n, a.val + 1 = b.val →
      ¬ EHP6.Complete G (Z.get (f a)) (Z.get (f b))) :
    ∀ a b, a < b → ∃ u ∈ U, RootSeparates G u (Z.get (f a)) (Z.get (f b)) := by
  have hindices : (List.ofFn f).Pairwise (· < ·) := List.pairwise_ofFn.mpr hf
  have hsub : List.ofFn (fun i => Z.get (f i)) <+ Z := by
    simpa [List.map_ofFn, Function.comp_def] using List.map_getElem_sublist hindices
  have hchain : (List.ofFn (fun i => Z.get (f i))).IsChain
      (fun A B => ¬ EHP6.Complete G A B) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact hlinks ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have hpair := ordered_frontier_path_roots G U hfront _ hsub hchain
  intro a b hab
  exact List.pairwise_ofFn.mp hpair hab

#print axioms chain_confined_to_one_section
#print axioms ordered_frontier_path_roots
#print axioms ordered_frontier_increasing_path_roots

end AllPathsLocal
