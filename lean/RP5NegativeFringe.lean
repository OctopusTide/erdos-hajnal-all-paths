import RP5TreeDichotomy

namespace AllPathsLocal

noncomputable def negativeFringes {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ)
    (P : List (RootCutStage G)) : Finset (Finset V) := by
  classical
  exact P.toFinset.biUnion (fun a => if (retainedCutChildren s a.cut).card = 1 ∧
    a.cut.A ∉ retainedCutChildren s a.cut then smallCutComponents s a.cut else ∅)

theorem negative_fringe_mem {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ)
    {P : List (RootCutStage G)} {L : Finset V} (hL : L ∈ negativeFringes s P) :
    ∃ a ∈ P, L ∈ smallCutComponents s a.cut := by
  classical
  obtain ⟨a, ha, hLa⟩ := Finset.mem_biUnion.mp hL
  by_cases h : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut
  · exact ⟨a, List.mem_toFinset.mp ha, by simpa only [if_pos h] using hLa⟩
  · have he : L ∈ (∅ : Finset (Finset V)) := by simpa only [if_neg h] using hLa
    exact False.elim (by simpa using he)

theorem negative_fringe_properties {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    ∀ L ∈ negativeFringes s P, L ⊆ S ∧ (L.card : ℝ) < s := by
  classical
  intro L hL
  obtain ⟨a, ha, hLa⟩ := negative_fringe_mem s hL
  have hm := Finset.mem_filter.mp hLa
  exact ⟨(a.cut.properC L hm.1).subset.trans (actual_path_subsets_and_roots hP a ha).1, hm.2⟩

/-- All individual small C siblings at negative unary steps are complete to one
    another, including siblings at different depths of the actual full path. -/
theorem negative_fringe_pairwise_complete {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {x s : ℝ}
    {S : Finset V} {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    ∀ L ∈ negativeFringes s P, ∀ R ∈ negativeFringes s P,
      L ≠ R → EHP6.Complete G L R := by
  classical
  induction hP with
  | terminal S u hu large degree cut below hn =>
    simp [negativeFringes, hn]
  | @step S u hu large degree cut below K hK P path ih =>
    have hKm := Finset.mem_filter.mp hK
    by_cases hneg : (retainedCutChildren s cut).card = 1 ∧ cut.A ∉ retainedCutChildren s cut
    · have hKC : K ∈ cut.C := by
        rcases Finset.mem_insert.mp hKm.1 with heq | hKC
        · exact False.elim (hneg.2 (heq ▸ hK))
        · exact hKC
      have hcross : ∀ L ∈ smallCutComponents s cut, ∀ R ∈ negativeFringes s P,
          EHP6.Complete G L R := by
        intro L hL R hR
        have hLm := Finset.mem_filter.mp hL
        have hLK : L ≠ K := by
          intro heq
          exact not_lt_of_ge hKm.2 (heq ▸ hLm.2)
        intro v hv w hw
        exact cut.completeC L hLm.1 K hKC hLK v hv w
          ((negative_fringe_properties path R hR).1 hw)
      change ∀ L ∈ negativeFringes s (⟨S, u, cut⟩ :: P),
        ∀ R ∈ negativeFringes s (⟨S, u, cut⟩ :: P), L ≠ R → EHP6.Complete G L R
      simp only [negativeFringes, List.toFinset_cons, Finset.biUnion_insert,
        if_pos hneg, Finset.mem_union]
      intro L hL R hR hLR
      rcases hL with hL | hL <;> rcases hR with hR | hR
      · exact cut.completeC L (Finset.mem_filter.mp hL).1 R (Finset.mem_filter.mp hR).1 hLR
      · exact hcross L hL R hR
      · intro v hv w hw
        exact G.adj_symm (hcross R hR L hL w hw v hv)
      · exact ih L hL R hR hLR
    · simpa only [negativeFringes, List.toFinset_cons, Finset.biUnion_insert,
        if_neg hneg, Finset.empty_union] using ih

theorem negative_fringe_mass_or_complete {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y) (t : ℕ) (ht : 2 ≤ t) :
    (((negativeFringes s P).biUnion id).card : ℝ) < t * s ∨
      ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G := by
  classical
  let D := (negativeFringes s P).biUnion id
  by_cases hmass : (D.card : ℝ) < t * s
  · exact Or.inl hmass
  right
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hsize : s ≤ (D.card : ℝ) / t := by
    apply (le_div_iff₀ ht0).mpr
    nlinarith [le_of_not_gt hmass]
  have hsmall : ∀ L ∈ negativeFringes s P, (L.card : ℝ) < (D.card : ℝ) / t :=
    fun L hL => (negative_fringe_properties hP L hL).2.trans_le hsize
  obtain ⟨β, hm, hβ⟩ := complete_small_atoms_grouping G D (negativeFringes s P) t ht
    rfl (negative_fringe_pairwise_complete hP) hsmall
  have hDY : D ⊆ Y := by
    intro v hv
    obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp hv
    exact hSY ((negative_fringe_properties hP L hL).1 hvL)
  have hwidth : s / (t : ℝ) ≤ (D.card : ℝ) / (t : ℝ)^2 := by
    apply (div_le_div_iff₀ ht0 (sq_pos_of_pos ht0)).mpr
    nlinarith [(le_div_iff₀ ht0).mp hsize]
  exact ⟨β.mono hDY le_rfl hwidth, hm, hβ⟩

#print axioms negative_fringe_mem
#print axioms negative_fringe_properties
#print axioms negative_fringe_pairwise_complete
#print axioms negative_fringe_mass_or_complete

end AllPathsLocal
