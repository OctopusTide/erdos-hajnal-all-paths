import RP5UniformSampling

namespace AllPathsLocal

/-- Delete at most one vertex per forbidden nonempty subset.
    This is an actual finite set construction, not a transversal hypothesis. -/
theorem forbidden_subsets_deletion {V : Type} [DecidableEq V]
    (S : Finset V) (pairs : Finset (Finset V))
    (hp : ∀ p ∈ pairs, p.Nonempty) :
    ∃ T ⊆ S, S.card ≤ T.card + pairs.card ∧ ∀ p ∈ pairs, ¬ p ⊆ T := by
  classical
  revert hp
  induction pairs using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨S, Finset.Subset.refl _, by simp, by simp⟩
  | @insert p pairs hnot ih =>
      intro hp
      obtain ⟨T, hTS, hsize, hfree⟩ := ih (fun q hq => hp q (Finset.mem_insert_of_mem hq))
      by_cases hpt : p ⊆ T
      · obtain ⟨u, hu⟩ := hp p (Finset.mem_insert_self _ _)
        refine ⟨T.erase u, (Finset.erase_subset _ _).trans hTS, ?_, ?_⟩
        · have he : (T.erase u).card + 1 = T.card := Finset.card_erase_add_one (hpt hu)
          simp only [Finset.card_insert_of_notMem hnot]
          omega
        · intro q hq hqT
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact (Finset.notMem_erase u T) (hqT hu)
          · exact hfree q hq (hqT.trans (Finset.erase_subset _ _))
      · refine ⟨T, hTS, ?_, ?_⟩
        · simp only [Finset.card_insert_of_notMem hnot]
          omega
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact hpt
          · exact hfree q hq

/-- A sample contains a genuine partial transversal after deleting at most
    its number of colliding same-layer unordered pairs. -/
theorem sample_transversal_by_collision_deletion {V : Type} [DecidableEq V]
    (S : Finset V) (layers : Finset (Finset V)) :
    let pairs := (layers.biUnion (fun A => A.powersetCard 2)).filter (· ⊆ S)
    ∃ T ⊆ S, S.card ≤ T.card + pairs.card ∧
      ∀ A ∈ layers, (T ∩ A).card ≤ 1 := by
  classical
  dsimp only
  let pairs := (layers.biUnion (fun A => A.powersetCard 2)).filter (· ⊆ S)
  have hp : ∀ p ∈ pairs, p.Nonempty := by
    intro p hp
    obtain ⟨A, _, hpA⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp).1
    exact Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hpA).2]; omega)
  obtain ⟨T, hTS, hsize, hfree⟩ := forbidden_subsets_deletion S pairs hp
  refine ⟨T, hTS, hsize, ?_⟩
  intro A hA
  by_contra hc
  obtain ⟨p, hpTA, hpCard⟩ := Finset.exists_subset_card_eq (show 2 ≤ (T ∩ A).card by omega)
  have hpT := hpTA.trans Finset.inter_subset_left
  have hpA := hpTA.trans Finset.inter_subset_right
  have hpmem : p ∈ pairs := Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨A, hA, Finset.mem_powersetCard.mpr ⟨hpA, hpCard⟩⟩,
      hpT.trans hTS⟩
  exact hfree p hpmem hpT

#print axioms forbidden_subsets_deletion
#print axioms sample_transversal_by_collision_deletion
end AllPathsLocal
