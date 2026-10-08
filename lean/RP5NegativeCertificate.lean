import RP5OrderedTransversalCertificate

namespace AllPathsLocal

/-- All later negative layers, with their actual path indices, satisfy the
    rooted P4 exclusion; this uses the original RP5 roots and prefix lemma. -/
theorem actual_negative_layer_future_free {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (i : Fin P.length) (v : V) (hv : v ∈ negativeLayer s (P.get i)) :
    RootedP4Free G ((Finset.univ.filter (fun j => i < j)).biUnion
      (fun j => negativeLayer s (P.get j))) v := by
  classical
  let a := P.get i
  change v ∈ negativeLayer s a at hv
  have ha : a ∈ P := List.get_mem P i
  have hu := (actual_path_subsets_and_roots hP a ha).2
  have hneg : (retainedCutChildren s a.cut).card = 1 ∧
      a.cut.A ∉ retainedCutChildren s a.cut := by
    by_contra h
    simpa [negativeLayer, h] using hv
  have hvA : v ∈ a.cut.A := by simpa only [negativeLayer, if_pos hneg] using hv
  have hanti : ¬ G.Adj a.u v := by
    rw [a.cut.remainder] at hvA
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
    intro hadj
    exact hvN (Finset.mem_filter.mpr ⟨hvS, hadj⟩)
  have hsub : ((Finset.univ.filter (fun j => i < j)).biUnion
      (fun j => negativeLayer s (P.get j))) ⊆ Y := by
    intro w hw
    obtain ⟨j, _, hwj⟩ := Finset.mem_biUnion.mp hw
    exact hSY ((actual_path_subsets_and_roots hP _ (List.get_mem P j)).1
      (negative_layer_subset_source s _ hwj))
  have hfull : ∀ w ∈ ((Finset.univ.filter (fun j => i < j)).biUnion
      (fun j => negativeLayer s (P.get j))), G.Adj a.u w := by
    intro w hw
    obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp hw
    have hij := (Finset.mem_filter.mp hj).2
    have hfwd := List.Pairwise.rel_getElem_of_lt i.isLt j.isLt
      (actual_path_forward_laws hP) hij
    exact hfwd.2.2.2 hneg.1 hneg.2 w (negative_layer_subset_source s _ hwj)
  exact rp5_to_rp4 G (hout a.u hu)
    (hSY ((actual_path_subsets_and_roots hP a ha).1 (negative_layer_subset_source s a hv)))
    hsub (hfree a.u hu) hanti hfull

/-- Certificate existence for every actual negative partial transversal is now
    proved, with no perfection hypothesis and no new literature axiom. The
    certificate is in the complement, as required by the ordered obstruction. -/
theorem actual_negative_transversal_certificate {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (A : Finset V) (hAS : A ⊆ (P.map (negativeLayer s)).toFinset.biUnion id)
    (hthin : ∀ L ∈ (P.map (negativeLayer s)).toFinset, (A ∩ L).card ≤ 1) :
    Nonempty (CliqueColorCertificate (Gᶜ.induce (A : Set V))) := by
  classical
  apply ordered_layer_transversal_certificate G (fun i : Fin P.length => negativeLayer s (P.get i)) A
  · intro v hv
    obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp (hAS hv)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i, hi⟩, by simpa only [List.get_eq_getElem, heq, id_eq] using hvL⟩
  · intro i
    exact hthin _ (List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨P.get i, List.get_mem P i, rfl⟩))
  · exact actual_negative_layer_future_free hP hSY hout hfree

#print axioms actual_negative_layer_future_free
#print axioms actual_negative_transversal_certificate
end AllPathsLocal
