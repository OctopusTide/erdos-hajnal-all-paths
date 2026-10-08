import RP5RankSelection

namespace AllPathsLocal

open scoped BigOperators

theorem list_card_range_sum {V : Type} (Z : List (Finset V)) :
    (∑ i ∈ Finset.range Z.length, (((Z[i]?.getD ∅).card : ℕ) : ℝ)) =
      (Z.map (fun K => (K.card : ℝ))).sum := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hget : ∀ i : Fin Z.length, (((Z[i.val]?.getD ∅).card : ℕ) : ℝ) = (Z.get i).card := by
    intro i
    simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some, List.get_eq_getElem]
  simp only [hget]
  rw [← List.sum_ofFn]
  conv_rhs => rw [← List.ofFn_get Z, List.map_ofFn]
  rfl

theorem sorted_size_selection {V : Type} (Z : List (Finset V)) (t : ℕ) (N : ℝ)
    (ht : 16 ≤ t) (hN : 0 < N)
    (hsmall : ∀ K ∈ Z, (K.card : ℝ) ≤ N / (t : ℝ)^5)
    (hmass : 3 * N / (8 * t) ≤ (Z.map (fun K => (K.card : ℝ))).sum)
    (hmon : ∀ i j : Fin Z.length, i ≤ j → (Z.get j).card ≤ (Z.get i).card) :
    ∃ m, t ≤ m ∧ m ≤ Z.length ∧ ∀ K ∈ Z.take m, N / (m : ℝ)^3 ≤ (K.card : ℝ) := by
  let f : ℕ → ℝ := fun i => (Z[i]?.getD ∅).card
  have hf : ∀ i (hi : i < Z.length), f i = ((Z[i]'hi).card : ℝ) := by
    intro i hi
    simp only [f, List.getElem?_eq_getElem hi, Option.getD_some]
  have hfs : ∀ i < Z.length, f i ≤ N / (t : ℝ)^5 := by
    intro i hi
    rw [hf i hi]
    exact hsmall _ (List.getElem_mem hi)
  have hfm : 3 * N / (8 * t) ≤ ∑ i ∈ Finset.range Z.length, f i := by
    rw [show (∑ i ∈ Finset.range Z.length, f i) = (Z.map (fun K => (K.card : ℝ))).sum
      from list_card_range_sum Z]
    exact hmass
  obtain ⟨m, htm, hmL, hlast⟩ := rank_size_selection f Z.length t N ht hN hfs hfm
  have hm0 : 0 < m := by omega
  have hlastL : m - 1 < Z.length := by omega
  rw [hf (m - 1) hlastL] at hlast
  refine ⟨m, htm, hmL, ?_⟩
  intro K hK
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hK
  have him : i < m := by simpa only [List.length_take, Nat.min_eq_left hmL] using hi
  have hiL : i < Z.length := him.trans_le hmL
  have heq' : Z[i] = K := by simpa only [List.getElem_take] using heq
  have hmono : (Z[m - 1]).card ≤ (Z[i]).card :=
    hmon ⟨i, hiL⟩ ⟨m - 1, hlastL⟩ (by show i ≤ m - 1; omega)
  rw [← heq']
  exact hlast.trans (by exact_mod_cast hmono)

#print axioms list_card_range_sum
#print axioms sorted_size_selection

end AllPathsLocal
