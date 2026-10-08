import RP5RetainedFrontier

namespace AllPathsLocal

theorem disjoint_list_card_mass {V : Type} [DecidableEq V]
    (Z : List (Finset V)) (hZ : Z.Pairwise Disjoint) :
    (Z.toFinset.biUnion id).card = (Z.map Finset.card).sum := by
  classical
  induction Z with
  | nil => simp
  | cons A Z ih =>
    obtain ⟨hA, htail⟩ := List.pairwise_cons.mp hZ
    have hdis : Disjoint A (Z.toFinset.biUnion id) := by
      apply Finset.disjoint_left.mpr
      intro v hv hUnion
      obtain ⟨B, hB, hvB⟩ := Finset.mem_biUnion.mp hUnion
      exact Finset.disjoint_left.mp (hA B (List.mem_toFinset.mp hB)) hv hvB
    simp only [List.toFinset_cons, Finset.biUnion_insert, id_eq,
      Finset.card_union_of_disjoint hdis, List.map_cons, List.sum_cons]
    rw [ih htail]

theorem list_card_mass_lower {V : Type} (Z : List (Finset V)) (s : ℝ)
    (hsize : ∀ K ∈ Z, s ≤ (K.card : ℝ)) :
    (Z.length : ℝ) * s ≤ ((Z.map Finset.card).sum : ℝ) := by
  induction Z with
  | nil => simp
  | cons A Z ih =>
    have hA := hsize A (List.mem_cons_self)
    have htail := ih (fun K hK => hsize K (List.mem_cons_of_mem A hK))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add,
      Nat.cast_one]
    nlinarith

theorem ordered_frontier_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    {s : ℝ} (hsize : ∀ K ∈ Z, s ≤ (K.card : ℝ)) :
    (Z.length : ℝ) * s ≤ (S.card : ℝ) := by
  classical
  have hsub : Z.toFinset.biUnion id ⊆ S := by
    intro v hv
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
    exact (ordered_frontier_properties G U hfront).1 K (List.mem_toFinset.mp hK) hvK
  have hcard := Finset.card_le_card hsub
  have hlower := list_card_mass_lower Z s hsize
  rw [← disjoint_list_card_mass Z (ordered_frontier_disjoint G U hfront)] at hlower
  exact hlower.trans (by exact_mod_cast hcard)

#print axioms disjoint_list_card_mass
#print axioms list_card_mass_lower
#print axioms ordered_frontier_mass_bound

end AllPathsLocal
