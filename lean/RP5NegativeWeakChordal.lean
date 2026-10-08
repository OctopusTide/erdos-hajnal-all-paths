import RP5CycleRotation

namespace AllPathsLocal

noncomputable def orderedFutureVertices {V : Type} [DecidableEq V] {l : ℕ}
    (f : Fin l → V) (i : Fin l) : Finset V := by
  classical
  exact (Finset.univ.filter (fun j => i < j)).image f

theorem ordered_endpoint_cycle_obstruction {V : Type} [DecidableEq V]
    (G : SimpleGraph V) {l n : ℕ} (f : Fin l → V) (p : Fin n → V) (hn : 5 ≤ n)
    (hmem : ∀ j, p j ∈ Finset.univ.image f)
    (hfree : ∀ i, RootedP4Free G (orderedFutureVertices f i) (f i)) :
    ¬ (IsInducedCycle G p ∨ IsInducedCycle Gᶜ p) := by
  classical
  intro hp
  letI : NeZero n := ⟨by omega⟩
  have hpinj : Function.Injective p := hp.elim (fun h => h.1) (fun h => h.1)
  have hchoose : ∀ j : Fin n, ∃ i : Fin l, f i = p j := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hmem j)
    exact ⟨i, hi⟩
  choose g hg using hchoose
  have hginj : Function.Injective g := by
    intro i j h
    apply hpinj
    rw [← hg i, ← hg j, h]
  obtain ⟨k, _, hmin⟩ := (Finset.univ : Finset (Fin n)).exists_min_image g
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hrest : ∀ i : Fin n, i.val ≠ 0 → p (i + k) ∈ orderedFutureVertices f (g k) := by
    intro i hi
    have hne : g k ≠ g (i + k) := by
      intro h
      have hrot : i + k = (0 : Fin n) + k := by simpa using (hginj h).symm
      have hz : i = 0 := add_right_cancel hrot
      exact hi (congrArg Fin.val hz)
    have hlt : g k < g (i + k) := lt_of_le_of_ne (hmin _ (Finset.mem_univ _)) hne
    apply Finset.mem_image.mpr
    exact ⟨g (i + k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hg (i + k)⟩
  have hroot : RootedP4Free G (orderedFutureVertices f (g k))
      ((fun i : Fin n => p (i + k)) ⟨0, by omega⟩) := by
    simpa only [show (⟨0, by omega⟩ : Fin n) = 0 from rfl, zero_add, ← hg k] using hfree (g k)
  rcases hp with hp | hp
  · exact rooted_p4_excludes_hole G hn (fun i => p (i + k)) _ hroot hrest
      (induced_cycle_rotate G (by omega) p hp k)
  · exact rooted_p4_excludes_complement_hole G hn (fun i => p (i + k)) _ hroot hrest
      (induced_cycle_rotate Gᶜ (by omega) p hp k)

theorem actual_negative_transversal_endpoint_free {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    {l : ℕ} (φ : Fin l → Fin P.length) (hφ : StrictMono φ) (f : Fin l → V)
    (hf : ∀ i, f i ∈ negativeLayer s (P.get (φ i))) :
    ∀ i, RootedP4Free G (orderedFutureVertices f i) (f i) := by
  classical
  intro i
  let a := P.get (φ i)
  have ha : a ∈ P := List.get_mem P (φ i)
  have hu := (actual_path_subsets_and_roots hP a ha).2
  have hneg : (retainedCutChildren s a.cut).card = 1 ∧ a.cut.A ∉ retainedCutChildren s a.cut := by
    by_contra h
    have hv : f i ∈ negativeLayer s a := hf i
    simpa [negativeLayer, h] using hv
  have hvA : f i ∈ a.cut.A := by
    have hv : f i ∈ negativeLayer s a := hf i
    simpa only [negativeLayer, if_pos hneg] using hv
  have hanti : ¬ G.Adj a.u (f i) := by
    rw [a.cut.remainder] at hvA
    obtain ⟨hvS, hvN⟩ := Finset.mem_sdiff.mp hvA
    intro hadj
    exact hvN (Finset.mem_filter.mpr ⟨hvS, hadj⟩)
  have hsub : orderedFutureVertices f i ⊆ Y := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hSY ((actual_path_subsets_and_roots hP _ (List.get_mem P (φ j))).1
      (negative_layer_subset_source s _ (hf j)))
  have hfull : ∀ v ∈ orderedFutureVertices f i, G.Adj a.u v := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hij := (Finset.mem_filter.mp hj).2
    have hforward := List.Pairwise.rel_getElem_of_lt (φ i).isLt (φ j).isLt
      (actual_path_forward_laws hP) (hφ hij)
    exact hforward.2.2.2 hneg.1 hneg.2 (f j) (negative_layer_subset_source s _ (hf j))
  exact rp5_to_rp4 G (hout a.u hu)
    (hSY ((actual_path_subsets_and_roots hP a ha).1 (negative_layer_subset_source s a (hf i))))
    hsub (hfree a.u hu) hanti hfull

/-- Actual negative transversals have no long hole in either graph or complement.
    This is weak chordality; perfection is a separate theorem, not assumed here. -/
theorem actual_negative_transversal_no_long_cycles {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    {l : ℕ} (φ : Fin l → Fin P.length) (hφ : StrictMono φ) (f : Fin l → V)
    (hf : ∀ i, f i ∈ negativeLayer s (P.get (φ i)))
    {n : ℕ} (p : Fin n → V) (hn : 5 ≤ n) (hmem : ∀ j, p j ∈ Finset.univ.image f) :
    ¬ (IsInducedCycle G p ∨ IsInducedCycle Gᶜ p) := by
  exact ordered_endpoint_cycle_obstruction G f p hn hmem
    (actual_negative_transversal_endpoint_free hP hSY hout hfree φ hφ f hf)

#print axioms ordered_endpoint_cycle_obstruction
#print axioms actual_negative_transversal_endpoint_free
#print axioms actual_negative_transversal_no_long_cycles

end AllPathsLocal
