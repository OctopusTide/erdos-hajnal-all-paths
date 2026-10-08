import RP5LargeFrontierConclusion
import RP5NegativeWeakChordal

namespace AllPathsLocal

def RP5DirectedOutput {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (x : ℝ) (t : ℕ) : Prop :=
  ∃ K : ℕ, (t : ℝ) ≤ (K : ℝ)^4 ∧ (K : ℝ) ≤ 1 / x^140 ∧
    ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i)

theorem complete_early_rp5_output {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (x s : ℝ)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16) (t : ℕ) (ht : 2^16 ≤ t)
    (htupper : (t : ℝ) ≤ 2 / x^4) (hscale : s = (Y.card : ℝ) / (t : ℝ)^6)
    (β : EHP6.Blockade Y t (s / t)) (hβm : β.m = t) (hβ : β.IsComplete G) :
    RP5DirectedOutput G Y x t := by
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ) < t := by linarith
  have hpow : (t : ℝ)^7 ≤ (t : ℝ)^64 := pow_le_pow_right₀ ht1 (by decide)
  have hwidth : (Y.card : ℝ) / (t : ℝ)^64 ≤ s / t := by
    have h := div_le_div_of_nonneg_left (Nat.cast_nonneg Y.card)
      (show 0 < (t : ℝ)^7 by positivity) hpow
    have he : (Y.card : ℝ) / (t : ℝ)^7 = s / t := by rw [hscale]; ring
    exact h.trans he.le
  let γ := β.mono (Finset.Subset.refl Y) le_rfl hwidth
  have ht4 : (t : ℝ) ≤ (t : ℝ)^4 := by simpa using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 4)
  have ht6 : (t : ℝ) ≤ (t : ℝ)^6 := by simpa using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 6)
  have htglobal := ht6.trans (frontier_count_paper_upper x (t : ℝ) hx hxsmall ht0.le htupper)
  have hx1 : x ≤ 1 := hxsmall.trans (by norm_num)
  have htlower : (t : ℝ) ≤ (t : ℝ)^2 := by simpa using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 2)
  have hrecip := (paper_parameter_reciprocal_bounds (t : ℝ) x ht1 hx hx1).2
  have htupper' := global_output_length_upper x (t : ℝ) (t : ℝ) hx hxsmall ht0.le htglobal (htlower.trans hrecip)
  exact ⟨t, ht4, htupper', γ, hβm, fun i j hij => Or.inl (hβ i j (ne_of_lt hij))⟩

/-- All graph constructions through the positive direction are assembled here.
    The sole remaining graph branch is an ACTUAL negative path of large mass.
    This is deliberately not named the complete RP5 Tooth theorem. -/
theorem actual_rp5_reduction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V) (x s : ℝ)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16) (t : ℕ) (ht : 2^16 ≤ t)
    (htupper : (t : ℝ) ≤ 2 / x^4) (hN : 1 / x^600 ≤ (Y.card : ℝ))
    (hscale : s = (Y.card : ℝ) / (t : ℝ)^6) :
    (∃ A ⊆ Y, s ≤ (A.card : ℝ) ∧ FullOrSmall G U x A) ∨
    RP5DirectedOutput G Y x t ∨
    (∃ T : RetainedCutTree G U x s Y, ∃ P, ActualRetainedPath T P ∧
      3 * (Y.card : ℝ) / (8 * t) ≤ (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum) := by
  classical
  by_cases hclean : ∃ A ⊆ Y, s ≤ (A.card : ℝ) ∧ FullOrSmall G U x A
  · exact Or.inl hclean
  right
  by_cases hcomplete : ∃ β : EHP6.Blockade Y t (s / t), β.m = t ∧ β.IsComplete G
  · obtain ⟨β, hβm, hβ⟩ := hcomplete
    exact Or.inl (complete_early_rp5_output G Y x s hx hxsmall t ht htupper hscale β hβm hβ)
  have hN0 : 0 < (Y.card : ℝ) := (show 0 < 1 / x^600 by positivity).trans_le hN
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hs : 0 < s := by rw [hscale]; positivity
  have hslarge : s ≤ (Y.card : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have htpow : (1 : ℝ) ≤ (t : ℝ)^6 := one_le_pow₀ ht1
    rw [hscale]
    exact div_le_self hN0.le htpow
  have hno : ∀ A ⊆ Y, s ≤ (A.card : ℝ) → ¬ FullOrSmall G U x A := by
    intro A hAY hsize hfull
    exact hclean ⟨A, hAY, hsize, hfull⟩
  obtain ⟨tree⟩ := finite_root_cut_tree_exists G U x s hx hs Y
  obtain ⟨T⟩ := cut_tree_prune G U x s tree (Finset.Subset.refl Y) hslarge hno
  by_cases hq : t ≤ treeLeafCount T.toWeighted
  · obtain ⟨Z, hZ, hsize, hlength⟩ := retained_terminal_frontier G T
    have hm : t ≤ Z.length := by simpa only [hlength] using hq
    have hsize' : ∀ K ∈ Z, (Y.card : ℝ) / (t : ℝ)^6 ≤ (K.card : ℝ) := by simpa only [hscale] using hsize
    exact Or.inl (actual_large_frontier_conclusion hZ (Finset.Subset.refl Y) hout hfree
      x hx hxsmall t ht htupper hN hm hsize')
  · obtain ⟨P, hP, hmass⟩ := actual_direction_carries_mass T (Finset.Subset.refl Y) t (by omega)
      hscale (Nat.lt_of_not_ge hq) hcomplete
    rcases hmass with hpos | hneg
    · exact Or.inl (actual_positive_direction_conclusion hP (Finset.Subset.refl Y) hout hfree
        hx hxsmall t ht htupper hN hscale hcomplete hpos)
    · exact Or.inr ⟨T, P, hP, hneg⟩

#print axioms complete_early_rp5_output
#print axioms actual_rp5_reduction

end AllPathsLocal
