import AllPathsFrontier
import RP5PositiveConclusion
import RP5Interval

/-!
# Frontier inputs of the RPq tree recurrence

The two constructions that feed the RPq frontier lemma (main paper, Appendix
"RP6 frontiers and the third offending-pair purification", first section): an
ordered cut-tree frontier, and a positive sequence. Both give a list of pairwise
disjoint blocks with a separating root for every pair on an increasing path of
non-complete pairs; recorded root families and the rooted RP(q-1) law (II) follow.
The positive-layer facts are the q-independent parts of `RP5LayerInterfaces` and
`RP5PositiveCount`.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A vertex complete in `G` to `T` has no rooted path of the complement into `T`
    on at least two vertices. -/
theorem rooted_path_free_of_complete (n : ℕ) {T : Finset V} {v : V}
    (h : ∀ a ∈ T, G.Adj v a) : RootedPathFree G (n + 2) T v := by
  rintro ⟨p, i, hi, hp, hpi, htail⟩
  have he : i = 0 := Fin.ext hi
  subst he
  have h1 : (1 : Fin (n + 2)) ≠ 0 := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  have hadj : Gᶜ.Adj (p 0) (p 1) := (hp.2 0 1).mpr (Or.inl (by simp))
  rw [hpi] at hadj
  exact ((G.compl_adj _ _).mp hadj).2 (h _ (htail 1 h1))

/-- Positive layers on an actual retained path: disjoint, and the split root of the
    earlier one separates every pair. -/
theorem gen_positive_layer_laws {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    P.Pairwise (fun a b => (positiveLayer s a).Nonempty →
      Disjoint (positiveLayer s a) (positiveLayer s b) ∧ ∃ u ∈ U,
        RootSeparates G u (positiveLayer s a) (positiveLayer s b)) := by
  apply List.Pairwise.imp_of_mem ?_ (actual_path_forward_laws hP)
  intro a b ha hb hab
  have hu := (actual_path_subsets_and_roots hP a ha).2
  have hdis := hab.2.1.mono (positive_layer_subset_atoms s a) (positive_layer_subset_source s b)
  intro hnonempty
  obtain ⟨v, hv⟩ := hnonempty
  have hpos : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∈ retainedCutChildren s a.cut := by
    by_contra h
    simpa [positiveLayer, h] using hv
  have hfull : ∀ v ∈ positiveLayer s a, G.Adj a.u v := by
    intro v hv
    have hvN : v ∈ EHP6.nbrs G a.u a.S := by simpa only [positiveLayer, if_pos hpos] using hv
    exact (Finset.mem_filter.mp hvN).2
  have hanti : ∀ v ∈ positiveLayer s b, ¬ G.Adj a.u v := by
    intro v hv
    exact hab.2.2.1 hpos.1 hpos.2 v (positive_layer_subset_source s b hv)
  exact ⟨hdis, a.u, hu, hfull, hanti⟩

theorem gen_positive_blocks_properties {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y) :
    (∀ K ∈ positiveBlocks s P, K ⊆ Y ∧ K.Nonempty) ∧
    (positiveBlocks s P).Pairwise (fun A B => Disjoint A B ∧
      ∃ u ∈ U, RootSeparates G u A B) := by
  constructor
  · intro K hK
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hK
    have hm := List.mem_filter.mp ha
    exact ⟨(positive_layer_subset_source s a).trans
      ((actual_path_subsets_and_roots hP a hm.1).1.trans hSY), by simpa using hm.2⟩
  · apply List.pairwise_map.mpr
    have h := (gen_positive_layer_laws (Y := Y) hP).sublist
      (show (P.filter (fun a => (positiveLayer s a).Nonempty)).Sublist P from List.filter_sublist)
    apply List.Pairwise.imp_of_mem ?_ h
    intro a b ha hb hab
    exact hab (by simpa using (List.mem_filter.mp ha).2)

theorem gen_positive_count_bound {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hx : 0 < x) (t : ℕ) (ht : 1 ≤ t) (hN : 0 < (S.card : ℝ))
    (hscale : s = (S.card : ℝ) / (t : ℝ) ^ 6) :
    ((positiveBlocks s P).length : ℝ) ≤ 4 * (t : ℝ) ^ 6 / x := by
  let Z := positiveBlocks s P
  have hprops := gen_positive_blocks_properties hP hSY
  have hpair : Z.Pairwise Disjoint := hprops.2.imp (fun h => h.1)
  have hsub : Z.toFinset.biUnion id ⊆ S := by
    intro v hv
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    exact (actual_path_subsets_and_roots hP a (List.mem_filter.mp ha).1).1
      (positive_layer_subset_source s a hvK)
  have hmass := list_card_mass_lower Z (x * s / 4) (actual_positive_blocks_lower hP hx.le)
  rw [← disjoint_list_card_mass Z hpair] at hmass
  have hcard : ((Z.toFinset.biUnion id).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hsub
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hbound : (Z.length : ℝ) * (x * ((S.card : ℝ) / (t : ℝ) ^ 6) / 4) ≤ S.card := by
    simpa only [hscale] using hmass.trans hcard
  have he : (Z.length : ℝ) * (x * ((S.card : ℝ) / (t : ℝ) ^ 6) / 4) =
      ((S.card : ℝ) * ((Z.length : ℝ) * x)) / (4 * (t : ℝ) ^ 6) := by ring
  rw [he] at hbound
  have hbound' := (div_le_iff₀ (show 0 < 4 * (t : ℝ) ^ 6 by positivity)).mp hbound
  have hcancel : (Z.length : ℝ) * x ≤ 4 * (t : ℝ) ^ 6 :=
    (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm] using hbound')
  exact (le_div_iff₀ hx).mpr hcancel

/-- **The RPq frontier lemma for a list of blocks** with a separating root on every
    increasing path of non-complete pairs (an ordered cut-tree frontier or a positive
    sequence). -/
theorem rpq_frontier_list (n : ℕ) {A e c k d E : ℕ} {η₀ : ℝ} (hE : 1 ≤ E) (hk : 1 ≤ k)
    (hT1 : LowerTooth G (n + 2) A e c k d E η₀) (hT2 : LowerTooth G (n + 1) A e c k d E η₀)
    (Z : List (Finset V)) {U Y : Finset V}
    (hsub : ∀ K ∈ Z, K ⊆ Y) (hdis : Z.Pairwise Disjoint)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n + 3) Y u)
    (hsep : ∀ (N : ℕ) (f : Fin N → Fin Z.length), StrictMono f →
      (∀ a b : Fin N, a.val + 1 = b.val → ¬ EHP6.Complete G (Z.get (f a)) (Z.get (f b))) →
      ∀ a b, a < b → ∃ u ∈ U, RootSeparates G u (Z.get (f a)) (Z.get (f b)))
    {τ N : ℝ} {b₀ : ℕ} (hm : 2 ^ 16 ≤ Z.length) (hmη : 1 / (Z.length : ℝ) ≤ η₀)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hN : 0 ≤ N)
    (hsizeN : ∀ K ∈ Z, N / (Z.length : ℝ) ^ b₀ ≤ (K.card : ℝ))
    (hsizeQ : ∀ K ∈ Z, ((Z.length : ℝ) / τ) ^ (E * (4 * A + 11)) ≤ (K.card : ℝ)) :
    FrontierOut G Y Z.length τ N A e c k d b₀ := by
  obtain ⟨R, hR⟩ := recorded_root_families G U (fun i : Fin Z.length => Z.get i)
  have hdisj : Pairwise (fun i j : Fin Z.length => Disjoint (Z.get i) (Z.get j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (List.pairwise_iff_get.mp hdis) i j h
    · exact ((List.pairwise_iff_get.mp hdis) j i h).symm
  have hII : ∀ i j : Fin Z.length, i < j → ∀ v ∈ Z.get j,
      RootedPathFree G (n + 2) (Z.get i) v := by
    intro i j hij v hv
    by_cases hc : EHP6.Complete G (Z.get i) (Z.get j)
    · exact rooted_path_free_of_complete n (fun a ha => (hc a ha v hv).symm)
    · let f : Fin 2 → Fin Z.length := fun a => if a.val = 0 then i else j
      have hf : StrictMono f := by
        intro a b hab
        have ha : a.val = 0 := by have := b.isLt; have : a.val < b.val := hab; omega
        have hb : b.val ≠ 0 := by have : a.val < b.val := hab; omega
        simp only [f, if_pos ha, if_neg hb]
        exact hij
      have hlinks : ∀ a b : Fin 2, a.val + 1 = b.val →
          ¬ EHP6.Complete G (Z.get (f a)) (Z.get (f b)) := by
        intro a b hab
        have ha : a.val = 0 := by have := b.isLt; omega
        have hb : b.val ≠ 0 := by omega
        simp only [f, if_pos ha, if_neg hb]
        exact hc
      obtain ⟨u, hu, hsepu⟩ := hsep 2 f hf hlinks 0 1 (by decide)
      have e0 : f 0 = i := by simp [f]
      have e1 : f 1 = j := by simp [f]
      rw [e0, e1] at hsepu
      exact rooted_path_free_prefix G (n + 1) (hout u hu) (hsub _ (List.get_mem Z j) hv)
        (hsub _ (List.get_mem Z i)) (hfree u hu) (hsepu.2 v hv) hsepu.1
  refine rpq_frontier n hE hk hT1 hT2 (fun i : Fin Z.length => Z.get i) R
    (fun i => hsub _ (List.get_mem Z i)) hdisj (fun i => (hR i).2.1)
    (fun i => (hR i).1.trans (Nat.sub_le _ _)) hout hfree (fun j => (hR j).2.2.1) hII ?_
    hm hmη hτ0 hτ1 hN (fun i => hsizeN _ (List.get_mem Z i))
    (fun i => hsizeQ _ (List.get_mem Z i))
  intro N' f hf hlinks a b hab
  exact (hR (f a)).2.2.2 (f b) (hf hab) (hsep N' f hf hlinks a b hab)

#print axioms rooted_path_free_of_complete
#print axioms gen_positive_blocks_properties
#print axioms gen_positive_count_bound
#print axioms rpq_frontier_list
end AllPathsLocal
