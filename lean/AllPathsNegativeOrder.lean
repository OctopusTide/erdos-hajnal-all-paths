import AllPathsRootedRecurrence

namespace AllPathsLocal

/-- All later negative layers, with their actual path indices, satisfy the
    rooted P4 exclusion; this uses the original RP5 roots and prefix lemma. -/
theorem actual_negative_layer_future_rooted_free {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (n : ℕ) (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n+2) Y u)
    (i : Fin P.length) (v : V) (hv : v ∈ negativeLayer s (P.get i)) :
    RootedPathFree G (n+1) ((Finset.univ.filter (fun j => i < j)).biUnion
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
  exact rooted_path_free_prefix G n (hout a.u hu)
    (hSY ((actual_path_subsets_and_roots hP a ha).1 (negative_layer_subset_source s a hv)))
    hsub (hfree a.u hu) hanti hfull

/-- Ordered E_(n+1) condition, with n+1 vertices as in the original path
    definition. The first vertex cannot be an induced-path endpoint. -/
def OrderedFirstEndpointFree {V : Type} [LT V] (H : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ p : Fin (n+1) → V, IsInducedPath H p → ¬ ∀ j, j ≠ 0 → p 0 < p j

/-- The negative transversal belongs to E_(q-1) in the original complement
    when the roots exclude RPq. This constructs its order from actual layer
    indices, and is the graph input to the RPq EH-transversal bridge. -/
theorem actual_negative_transversal_ordered_path_free {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s Y} {P : List (RootCutStage G)}
    (n : ℕ) (hP : ActualRetainedPath T P)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n+2) Y u)
    (A : Finset V) (hAS : A ⊆ (P.map (negativeLayer s)).toFinset.biUnion id)
    (hthin : ∀ L ∈ (P.map (negativeLayer s)).toFinset, (A ∩ L).card ≤ 1) :
    ∃ ord : LinearOrder ↥(A : Set V),
      @OrderedFirstEndpointFree ↥(A : Set V) ord.toLT (Gᶜ.induce (A : Set V)) n := by
  classical
  have hchoose : ∀ v : ↥(A : Set V), ∃ i : Fin P.length, v.val ∈ negativeLayer s (P.get i) := by
    intro v
    obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp (hAS v.property)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ha
    exact ⟨⟨i, hi⟩, by simpa only [List.get_eq_getElem, heq, id_eq] using hvL⟩
  choose index hindex using hchoose
  have hinj : Function.Injective index := by
    intro u v he
    apply Subtype.ext
    have hm : negativeLayer s (P.get (index u)) ∈ (P.map (negativeLayer s)).toFinset :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨P.get (index u), List.get_mem P _, rfl⟩)
    exact Finset.card_le_one.mp (hthin _ hm) u.val
      (Finset.mem_inter.mpr ⟨u.property, hindex u⟩) v.val
      (Finset.mem_inter.mpr ⟨v.property, he ▸ hindex v⟩)
  let ord : LinearOrder ↥(A : Set V) := LinearOrder.lift' index hinj
  refine ⟨ord, ?_⟩
  letI : LinearOrder ↥(A : Set V) := ord
  intro p hp hlt
  let q : Fin (n+1) → V := fun j => (p j).val
  have hq : IsInducedPath Gᶜ q :=
    ⟨fun i j he => hp.1 (Subtype.ext he), hp.2⟩
  apply actual_negative_layer_future_rooted_free n hP (Finset.Subset.refl Y) hout hfree
    (index (p 0)) (p 0).val (hindex (p 0))
  refine ⟨q, 0, rfl, hq, rfl, ?_⟩
  intro j hj
  have hij : index (p 0) < index (p j) := hlt j hj
  exact Finset.mem_biUnion.mpr ⟨index (p j),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hindex (p j)⟩

#print axioms actual_negative_layer_future_rooted_free
#print axioms actual_negative_transversal_ordered_path_free
end AllPathsLocal
