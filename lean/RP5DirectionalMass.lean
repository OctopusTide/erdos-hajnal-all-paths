import RP5LayerMass

namespace AllPathsLocal

theorem actual_positive_negative_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y) (hs : 0 ≤ s)
    (t : ℕ) (ht : 2 ≤ t) (hfew : treeLeafCount T.toWeighted < t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∃ Q, ActualRetainedPath T Q ∧
      (S.card : ℝ) / t - (3 * t + 2) * s ≤
        (Q.map (fun a => ((positiveLayer s a).card : ℝ))).sum +
        (Q.map (fun a => ((negativeLayer s a).card : ℝ))).sum := by
  obtain ⟨Q, hQ, hmass⟩ := few_leaves_labelled_path_mass T hSY hs t ht hfew hno
  have hfringe : (((negativeFringes s Q).biUnion id).card : ℝ) < t * s := by
    rcases negative_fringe_mass_or_complete hQ hSY t ht with h | h
    · exact h
    · exact False.elim (hno h)
  rw [actual_fringe_card_sum hQ] at hfringe
  rw [unary_path_layer_mass] at hmass
  exact ⟨Q, hQ, by nlinarith⟩

theorem paper_layer_mass_numeric (N : ℝ) (hN : 0 ≤ N) (t : ℕ) (ht : 4 ≤ t) :
    3 * N / (4 * t) ≤ N / t - (3 * t + 2) * (N / (t : ℝ)^6) := by
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hp : 4 * (3 * (t : ℝ) + 2) ≤ (t : ℝ)^5 := by
    have ht2 : (16 : ℝ) ≤ (t : ℝ)^2 := by nlinarith
    have ht4 : (256 : ℝ) ≤ (t : ℝ)^4 := by nlinarith [sq_nonneg ((t : ℝ)^2 - 16)]
    nlinarith [mul_le_mul_of_nonneg_left ht4 ht0.le]
  apply (le_sub_iff_add_le).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * (t : ℝ)^6 by positivity)).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hp hN]

/-- The real path and actual layers, with s = |S|/t^6, produce a direction
    carrying at least 3|S|/(8t). No layer-existence premise is assumed. -/
theorem actual_direction_carries_mass {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    (T : RetainedCutTree G U x s S) (hSY : S ⊆ Y)
    (t : ℕ) (ht : 4 ≤ t) (hscale : s = (S.card : ℝ) / (t : ℝ)^6)
    (hfew : treeLeafCount T.toWeighted < t)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G) :
    ∃ Q, ActualRetainedPath T Q ∧
      (3 * (S.card : ℝ) / (8 * t) ≤ (Q.map (fun a => ((positiveLayer s a).card : ℝ))).sum ∨
       3 * (S.card : ℝ) / (8 * t) ≤ (Q.map (fun a => ((negativeLayer s a).card : ℝ))).sum) := by
  have hs : 0 ≤ s := by rw [hscale]; positivity
  obtain ⟨Q, hQ, hmass⟩ := actual_positive_negative_mass_bound T hSY hs t (by omega) hfew hno
  have hnum := paper_layer_mass_numeric (S.card : ℝ) (Nat.cast_nonneg _) t ht
  rw [← hscale] at hnum
  have hhalves : 2 * (3 * (S.card : ℝ) / (8 * t)) = 3 * (S.card : ℝ) / (4 * t) := by ring
  refine ⟨Q, hQ, ?_⟩
  by_cases h : 3 * (S.card : ℝ) / (8 * t) ≤ (Q.map (fun a => ((positiveLayer s a).card : ℝ))).sum
  · exact Or.inl h
  · exact Or.inr (by linarith [lt_of_not_ge h])

#print axioms actual_positive_negative_mass_bound
#print axioms paper_layer_mass_numeric
#print axioms actual_direction_carries_mass

end AllPathsLocal
