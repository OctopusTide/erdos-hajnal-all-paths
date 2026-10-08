import RP5SortedSelection

namespace AllPathsLocal

/-- Sort only to find the size threshold, then select blocks in their ORIGINAL
    order. The output has exact length m, retaining every original root law. -/
theorem ordered_size_selection {V : Type} (Z : List (Finset V)) (t : ℕ) (N : ℝ)
    (ht : 16 ≤ t) (hN : 0 < N)
    (hsmall : ∀ K ∈ Z, (K.card : ℝ) ≤ N / (t : ℝ)^5)
    (hmass : 3 * N / (8 * t) ≤ (Z.map (fun K => (K.card : ℝ))).sum) :
    ∃ (m : ℕ) (Q : List (Finset V)), t ≤ m ∧ m ≤ Z.length ∧ Q.Sublist Z ∧ Q.length = m ∧
      ∀ K ∈ Q, N / (m : ℝ)^3 ≤ (K.card : ℝ) := by
  classical
  let r : Finset V → Finset V → Prop := fun A B => B.card ≤ A.card
  letI : Std.Total r := ⟨fun A B => le_total B.card A.card⟩
  letI : IsTrans (Finset V) r := ⟨fun A B C hAB hBC => hBC.trans hAB⟩
  let S := Z.mergeSort (fun A B => decide (r A B))
  have hperm : S.Perm Z := List.mergeSort_perm Z _
  have hpair : S.Pairwise r := List.pairwise_mergeSort' r Z
  have hmon : ∀ i j : Fin S.length, i ≤ j → (S.get j).card ≤ (S.get i).card := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hpair hij
    · exact le_rfl
  have hsmallS : ∀ K ∈ S, (K.card : ℝ) ≤ N / (t : ℝ)^5 :=
    fun K hK => hsmall K (hperm.mem_iff.mp hK)
  have hmassS : 3 * N / (8 * t) ≤ (S.map (fun K => (K.card : ℝ))).sum := by
    rw [(hperm.map (fun K => (K.card : ℝ))).sum_eq]
    exact hmass
  obtain ⟨m, htm, hmS, hwidth⟩ := sorted_size_selection S t N ht hN hsmallS hmassS hmon
  let p : Finset V → Bool := fun K => decide (N / (m : ℝ)^3 ≤ (K.card : ℝ))
  have hfiltertake : (S.take m).filter p = S.take m := by
    apply List.filter_eq_self.mpr
    intro K hK
    simpa only [p, decide_eq_true_eq] using hwidth K hK
  have hcountS : m ≤ (S.filter p).length := by
    have h := ((List.take_sublist m S).filter p).length_le
    simpa only [hfiltertake, List.length_take, Nat.min_eq_left hmS] using h
  have hfilterperm := hperm.filter p
  have hcountZ : m ≤ (Z.filter p).length := by simpa only [hfilterperm.length_eq] using hcountS
  let Q := (Z.filter p).take m
  refine ⟨m, Q, htm, by simpa only [hperm.length_eq] using hmS,
    (List.take_sublist m (Z.filter p)).trans List.filter_sublist, ?_, ?_⟩
  · simp only [Q, List.length_take, Nat.min_eq_left hcountZ]
  · intro K hK
    have hmem := (List.take_sublist m (Z.filter p)).subset hK
    have hp := (List.mem_filter.mp hmem).2
    simpa only [p, decide_eq_true_eq] using hp

#print axioms ordered_size_selection

end AllPathsLocal
