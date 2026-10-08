import RP5OrderedCertificateStructure

namespace AllPathsLocal

/-- Grow a covered part A of a clique. An earliest stable neighbour of an
    uncovered vertex enlarges A; any later stable neighbour of the remaining
    part must be complete to the enlargement, by the actual P4 obstruction. -/
theorem ordered_stable_clique_witness_aux {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (hfree : OrderedP4EndpointFree H)
    (I K A : Finset V) (hAK : A ⊆ K)
    (hstable : ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v)
    (hclique : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b)
    (hdom : ∀ a ∈ K, ∃ v ∈ I, v < a ∧ H.Adj v a)
    (hcover : ∀ v ∈ I, (∃ b ∈ K \ A, H.Adj v b) → ∀ a ∈ A, H.Adj v a)
    (hB : (K \ A).Nonempty) : ∃ v ∈ I, ∀ a ∈ K, H.Adj v a := by
  classical
  let candidates := I.filter (fun v => ∃ b ∈ K \ A, H.Adj v b)
  have hc : candidates.Nonempty := by
    obtain ⟨b, hb⟩ := hB
    obtain ⟨v, hv, _, hvb⟩ := hdom b (Finset.mem_sdiff.mp hb).1
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, b, hb, hvb⟩⟩
  let u := candidates.min' hc
  have hu := Finset.mem_filter.mp (Finset.min'_mem candidates hc)
  obtain ⟨b0, hb0, hub0⟩ := hu.2
  have hmin : ∀ v ∈ candidates, u ≤ v := fun v hv => Finset.min'_le candidates v hv
  have hafter : ∀ a ∈ K \ A, u < a := by
    intro a ha
    obtain ⟨v, hvI, hva, hvEdge⟩ := hdom a (Finset.mem_sdiff.mp ha).1
    exact (hmin v (Finset.mem_filter.mpr ⟨hvI, a, ha, hvEdge⟩)).trans_lt hva
  let A' := K.filter (H.Adj u)
  have hA'K : A' ⊆ K := Finset.filter_subset _ _
  have hAA' : A ⊆ A' := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨hAK ha, hcover u hu.1 ⟨b0, hb0, hub0⟩ a ha⟩
  have hBsub : K \ A' ⊆ K \ A := by
    intro b hb
    obtain ⟨hbK, hbA'⟩ := Finset.mem_sdiff.mp hb
    exact Finset.mem_sdiff.mpr ⟨hbK, fun hbA => hbA' (hAA' hbA)⟩
  have hstrict : (K \ A').card < (K \ A).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hBsub, ?_⟩
    intro he
    have hh : b0 ∈ K \ A' := by rwa [he]
    exact (Finset.mem_sdiff.mp hh).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb0).1, hub0⟩)
  have hcover' : ∀ v ∈ I, (∃ b ∈ K \ A', H.Adj v b) → ∀ a ∈ A', H.Adj v a := by
    intro v hvI hvB a haA'
    obtain ⟨b, hb, hvb⟩ := hvB
    have hbOld := hBsub hb
    by_cases haOld : a ∈ A
    · exact hcover v hvI ⟨b, hbOld, hvb⟩ a haOld
    · obtain ⟨haK, hua⟩ := Finset.mem_filter.mp haA'
      have haOldB := Finset.mem_sdiff.mpr ⟨haK, haOld⟩
      have huNotb : ¬ H.Adj u b := by
        intro he
        exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, he⟩)
      have huvlt : u < v := by
        have hle := hmin v (Finset.mem_filter.mpr ⟨hvI, b, hbOld, hvb⟩)
        apply lt_of_le_of_ne hle
        intro he
        subst v
        exact huNotb hvb
      have habne : a ≠ b := by intro he; subst a; exact huNotb hua
      by_contra hav
      exact ordered_p4_endpoint_obstruction H hfree (hafter a haOldB) (hafter b hbOld) huvlt
        hua (hclique a haK b (Finset.mem_sdiff.mp hb).1 habne) (H.adj_symm hvb)
        huNotb (hstable u hu.1 v hvI) (fun he => hav (H.adj_symm he))
  by_cases hB' : (K \ A').Nonempty
  · exact ordered_stable_clique_witness_aux H hfree I K A' hA'K hstable hclique hdom hcover' hB'
  · refine ⟨u, hu.1, ?_⟩
    intro a ha
    by_contra hua
    exact hB' ⟨a, Finset.mem_sdiff.mpr ⟨ha, fun hh => hua (Finset.mem_filter.mp hh).2⟩⟩
termination_by (K \ A).card
decreasing_by exact hstrict

/-- The constructive clique extension needed to build a colouring/clique
    certificate recursively from an ordered greedy stable set. -/
theorem ordered_stable_clique_witness {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (hfree : OrderedP4EndpointFree H)
    (I K : Finset V) (hK : K.Nonempty)
    (hstable : ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v)
    (hclique : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → H.Adj a b)
    (hdom : ∀ a ∈ K, ∃ v ∈ I, v < a ∧ H.Adj v a) :
    ∃ v ∈ I, ∀ a ∈ K, H.Adj v a := by
  classical
  exact ordered_stable_clique_witness_aux H hfree I K ∅ (Finset.empty_subset _) hstable hclique hdom
    (by simp) (by simpa using hK)

#print axioms ordered_stable_clique_witness_aux
#print axioms ordered_stable_clique_witness
end AllPathsLocal
