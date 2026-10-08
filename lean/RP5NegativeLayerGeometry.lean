import RP5NegativeCertificate
import RP5ThinLayerStrong

namespace AllPathsLocal

theorem negative_layer_subset_atoms {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (a : RootCutStage G) :
    negativeLayer s a ⊆ cutAtoms s a.cut := by
  classical
  unfold negativeLayer
  split
  · rename_i hn
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨a.cut.A, Finset.mem_filter.mpr
      ⟨Finset.mem_insert_self _ _, (unary_negative_layer s a.cut hn.1 hn.2).1⟩, hv⟩
  · exact Finset.empty_subset _

theorem negative_layer_size_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (s : ℝ) (hs : 0 ≤ s) (a : RootCutStage G) :
    ((negativeLayer s a).card : ℝ) ≤ s := by
  classical
  unfold negativeLayer
  split
  · rename_i hn
    exact (unary_negative_layer s a.cut hn.1 hn.2).1.le
  · simpa using hs

/-- The actual negative layers are disjoint, lie in the original set, and
    preserve their precise integer mass when collected into a finite family. -/
theorem actual_negative_layer_geometry {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) :
    let layers := (P.map (negativeLayer s)).toFinset
    (layers.biUnion id ⊆ S) ∧
    (∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B) ∧
    (((layers.biUnion id).card : ℝ) =
      (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum) := by
  classical
  dsimp only
  have hpair : (P.map (negativeLayer s)).Pairwise Disjoint := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp ?_ (List.pairwise_map.mp (actual_path_atoms_pairwise_disjoint hP))
    intro a b hab
    exact hab.mono (negative_layer_subset_atoms s a) (negative_layer_subset_atoms s b)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    exact (actual_path_subsets_and_roots hP a ha).1 (negative_layer_subset_source s a hvL)
  · intro A hA B hB hAB
    obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hA)
    obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hB)
    rcases lt_trichotomy i j with hij | hij | hij
    · simpa only [hei, hej] using List.Pairwise.rel_getElem_of_lt hi hj hpair hij
    · subst j
      exact False.elim (hAB (hei.symm.trans hej))
    · simpa only [hei, hej] using (List.Pairwise.rel_getElem_of_lt hj hi hpair hij).symm
  · have h := disjoint_list_card_mass (P.map (negativeLayer s)) hpair
    have hcast : (((P.map (fun a => (negativeLayer s a).card)).sum : ℕ) : ℝ) =
        (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum := by
      clear hP hpair h
      induction P with
      | nil => simp
      | cons a P ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [List.map_map, Function.comp_def, hcast] using hc

#print axioms negative_layer_subset_atoms
#print axioms negative_layer_size_bound
#print axioms actual_negative_layer_geometry
end AllPathsLocal
