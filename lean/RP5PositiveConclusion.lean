import RP5PositiveCount
import RP5GlobalOrder

namespace AllPathsLocal

/-- The complete positive-direction graph argument, including actual layer
    construction, original-order size selection, both Tooth calls, all early
    outputs, and global length/width/order conversion. -/
theorem actual_positive_direction_conclusion {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16) (t : ℕ) (ht : 2^16 ≤ t)
    (htupper : (t : ℝ) ≤ 2 / x^4) (hN : 1 / x^600 ≤ (S.card : ℝ))
    (hscale : s = (S.card : ℝ) / (t : ℝ)^6)
    (hno : ¬ ∃ γ : EHP6.Blockade Y t (s / t), γ.m = t ∧ γ.IsComplete G)
    (hmass : 3 * (S.card : ℝ) / (8 * t) ≤
      (P.map (fun a => ((positiveLayer s a).card : ℝ))).sum) :
    ∃ K : ℕ, (t : ℝ) ≤ (K : ℝ)^4 ∧ (K : ℝ) ≤ 1 / x^140 ∧
      ∃ γ : EHP6.Blockade Y K ((S.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i) := by
  have hN0 : 0 < (S.card : ℝ) := (show 0 < 1 / x^600 by positivity).trans_le hN
  obtain ⟨m, Z, htm, hmL, hZsub, hZlen, hwidth⟩ :=
    actual_positive_size_selection hP hSY t (by omega) hN0 hscale hno hmass
  have hLbound := actual_positive_count_bound hP hSY hout hfree hx t (by omega) hN0 hscale
  have hmupper : (m : ℝ) ≤ 1 / x^27 :=
    (show (m : ℝ) ≤ (positiveBlocks s P).length by exact_mod_cast hmL).trans
      (hLbound.trans (positive_count_paper_bound x (t : ℝ) hx hxsmall (Nat.cast_nonneg _) htupper))
  have hm : 2^16 ≤ Z.length := by omega
  have hm1 : (1 : ℝ) ≤ Z.length := by exact_mod_cast (show 1 ≤ Z.length by omega)
  have hZupper : (Z.length : ℝ) ≤ 1 / x^27 := by simpa only [hZlen] using hmupper
  have horder := global_order_suffices x (Z.length : ℝ) (S.card : ℝ) hx hxsmall hm1 hZupper hN
  have hx1 : x ≤ 1 := hxsmall.trans (by norm_num)
  obtain ⟨K, hlo, hup, γ, hγm, htypes⟩ := selected_positive_quantitative hP hSY hout hfree
    hZsub hm hx hx1 horder (by simpa only [hZlen] using hwidth)
  have hlo' : (t : ℝ) ≤ (K : ℝ)^4 :=
    (show (t : ℝ) ≤ Z.length by exact_mod_cast (show t ≤ Z.length by omega)).trans hlo
  have hup' := global_output_length_upper x (Z.length : ℝ) (K : ℝ) hx hxsmall
    (Nat.cast_nonneg _) hZupper hup
  exact ⟨K, hlo', hup', γ, hγm, htypes⟩

#print axioms actual_positive_direction_conclusion

end AllPathsLocal
