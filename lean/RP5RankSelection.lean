import RP5SizeTail

namespace AllPathsLocal

open scoped BigOperators

/-- The rank-size step in III.6. No integral or infinite-series assumption is
    required: the finite reciprocal-cube tail is bounded by telescoping. -/
theorem rank_size_selection (f : ℕ → ℝ) (L t : ℕ) (N : ℝ)
    (ht : 16 ≤ t) (hN : 0 < N)
    (hsmall : ∀ i < L, f i ≤ N / (t : ℝ)^5)
    (hmass : 3 * N / (8 * t) ≤ ∑ i ∈ Finset.range L, f i) :
    ∃ m, t ≤ m ∧ m ≤ L ∧ N / (m : ℝ)^3 ≤ f (m - 1) := by
  by_contra! hnone
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht1 : 1 ≤ t := by omega
  have hnt : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub ht1, Nat.cast_one]
  let a := min L (t - 1)
  have haL : a ≤ L := Nat.min_le_left _ _
  have hat : a ≤ t := (Nat.min_le_right _ _).trans (by omega)
  have hprefix : (∑ i ∈ Finset.range a, f i) ≤ N / (t : ℝ)^4 := by
    have h := Finset.sum_le_sum (s := Finset.range a)
      (fun i hi => hsmall i ((Finset.mem_range.mp hi).trans_le haL))
    have haR : (a : ℝ) ≤ t := by exact_mod_cast hat
    have hcoef : (a : ℝ) * (N / (t : ℝ)^5) ≤ (t : ℝ) * (N / (t : ℝ)^5) :=
      mul_le_mul_of_nonneg_right haR (by positivity)
    have heq : (t : ℝ) * (N / (t : ℝ)^5) = N / (t : ℝ)^4 := by field_simp
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    exact h.trans (hcoef.trans heq.le)
  have htail : (∑ i ∈ Finset.range (L - a), f (a + i)) ≤ N / ((t : ℝ) - 1)^2 := by
    by_cases hLa : L ≤ t - 1
    · have haeq : a = L := Nat.min_eq_left hLa
      simp only [haeq, Nat.sub_self, Finset.range_zero, Finset.sum_empty]
      positivity
    · have haeq : a = t - 1 := Nat.min_eq_right (by omega)
      have ha1 : 1 ≤ a := by omega
      have hstep : ∀ i ∈ Finset.range (L - a), f (a + i) ≤ N / ((a : ℝ) + i + 1)^3 := by
        intro i hi
        have hiL : a + i + 1 ≤ L := by have hi' := Finset.mem_range.mp hi; omega
        have hti : t ≤ a + i + 1 := by omega
        have h := hnone (a + i + 1) hti hiL
        simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← add_assoc] using h.le
      have hsum := Finset.sum_le_sum hstep
      have hrewrite : (∑ i ∈ Finset.range (L - a), N / ((a : ℝ) + i + 1)^3) =
          N * (∑ i ∈ Finset.range (L - a), 1 / ((a : ℝ) + i + 1)^3) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hrewrite] at hsum
      have htail := inverse_cube_tail_range a ha1 (L - a)
      have htail' : (∑ i ∈ Finset.range (L - a), 1 / ((a : ℝ) + i + 1)^3) ≤ 1 / (a : ℝ)^2 := by
        exact htail.trans (sub_le_self _ (by positivity))
      have h := hsum.trans (mul_le_mul_of_nonneg_left htail' hN.le)
      simpa only [haeq, hnt, mul_one_div] using h
  have hpartition : (∑ i ∈ Finset.range L, f i) =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range (L - a), f (a + i) := by
    have h := Finset.sum_range_add f a (L - a)
    simpa only [Nat.add_sub_of_le haL] using h
  have hnum := mul_lt_mul_of_pos_left (size_tail_numeric t ht) hN
  have hnum' : N / (t : ℝ)^4 + N / ((t : ℝ) - 1)^2 < 3 * N / (8 * t) := by
    convert hnum using 1 <;> ring
  rw [hpartition] at hmass
  linarith

#print axioms rank_size_selection

end AllPathsLocal
