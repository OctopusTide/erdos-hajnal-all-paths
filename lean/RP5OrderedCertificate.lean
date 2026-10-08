import RP5OrderedGreedyStable

namespace AllPathsLocal

/-- Certificate on an actual ambient finite set, for recursive construction. -/
structure FinsetCliqueColorCertificate {V : Type} (H : SimpleGraph V) (S : Finset V) where
  k : ℕ
  color : V → ℕ
  bound : ∀ v ∈ S, color v < k
  proper : ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → color u ≠ color v
  clique : Finset V
  subset : clique ⊆ S
  card : clique.card = k
  adjacent : ∀ u ∈ clique, ∀ v ∈ clique, u ≠ v → H.Adj u v

/-- Construct the certificate by removing the actual ordered greedy stable
    set. A remaining clique extends by a stable vertex, via the proved witness
    lemma, so the added colour has an equally large actual clique. -/
theorem ordered_finset_certificate {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (hfree : OrderedP4EndpointFree H) (S : Finset V) :
    Nonempty (FinsetCliqueColorCertificate H S) := by
  classical
  by_cases hS : S.Nonempty
  · let I := orderedGreedyStable H S
    have hs := ordered_greedy_stable_properties H S
    have hI : I.Nonempty := hs.nonempty hS
    let R := S \ I
    have hstrict : R.card < S.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro he
      obtain ⟨u, hu⟩ := hI
      have huS := hs.subset hu
      have huR : u ∈ R := by rwa [he]
      exact (Finset.mem_sdiff.mp huR).2 hu
    obtain ⟨C⟩ := ordered_finset_certificate H hfree R
    obtain ⟨u, huI, hfull⟩ : ∃ u ∈ I, ∀ a ∈ C.clique, H.Adj u a := by
      by_cases hK : C.clique.Nonempty
      · apply ordered_stable_clique_witness H hfree I C.clique hK hs.stable C.adjacent
        intro a ha
        obtain ⟨haS, haI⟩ := Finset.mem_sdiff.mp (C.subset ha)
        exact hs.dominates a haS haI
      · obtain ⟨u, hu⟩ := hI
        exact ⟨u, hu, fun a ha => False.elim (hK ⟨a, ha⟩)⟩
    have huNot : u ∉ C.clique := by
      intro hu
      exact (Finset.mem_sdiff.mp (C.subset hu)).2 huI
    refine ⟨{
      k := C.k+1
      color := fun v => if v ∈ I then 0 else C.color v+1
      bound := ?_
      proper := ?_
      clique := insert u C.clique
      subset := Finset.insert_subset (hs.subset huI) (C.subset.trans Finset.sdiff_subset)
      card := ?_
      adjacent := ?_ }⟩
    · intro v hv
      by_cases hvI : v ∈ I
      · simp [hvI]
      · simp only [if_neg hvI]
        have hh := C.bound v (Finset.mem_sdiff.mpr ⟨hv, hvI⟩)
        omega
    · intro a ha b hb hab
      by_cases haI : a ∈ I <;> by_cases hbI : b ∈ I
      · exact False.elim (hs.stable a haI b hbI hab)
      · simp [haI, hbI]
      · simp [haI, hbI]
      · simp only [if_neg haI, if_neg hbI]
        intro he
        exact C.proper a (Finset.mem_sdiff.mpr ⟨ha, haI⟩) b
          (Finset.mem_sdiff.mpr ⟨hb, hbI⟩) hab (Nat.add_right_cancel he)
    · rw [Finset.card_insert_of_notMem huNot, C.card]
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · exact False.elim (hab rfl)
        · exact hfull b hb
      · rcases Finset.mem_insert.mp hb with hbEq | hb
        · rw [hbEq]
          exact H.adj_symm (hfull a ha)
        · exact C.adjacent a ha b hb hab
  · have hSEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    exact ⟨{ k := 0
             color := fun _ => 0
             bound := by simp
             proper := by simp
             clique := ∅
             subset := by simp
             card := rfl
             adjacent := by simp }⟩
termination_by S.card
decreasing_by exact hstrict

#print axioms ordered_finset_certificate
end AllPathsLocal
