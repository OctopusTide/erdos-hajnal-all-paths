import RP5PositiveConclusion

namespace AllPathsLocal

theorem ordered_frontier_count_from_scale {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U S : Finset V} {Z : List (Finset V)}
    (hfront : OrderedCutFrontier G U S Z) (t : ℕ) (ht : 1 ≤ t)
    (hN : 0 < (S.card : ℝ))
    (hsize : ∀ K ∈ Z, (S.card : ℝ) / (t : ℝ)^6 ≤ (K.card : ℝ)) :
    (Z.length : ℝ) ≤ (t : ℝ)^6 := by
  have hm := ordered_frontier_mass_bound G U hfront hsize
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have he : (Z.length : ℝ) * ((S.card : ℝ) / (t : ℝ)^6) =
      ((Z.length : ℝ) * S.card) / (t : ℝ)^6 := by ring
  rw [he] at hm
  have hh := (div_le_iff₀ (show 0 < (t : ℝ)^6 by positivity)).mp hm
  exact (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm] using hh)

theorem frontier_count_paper_upper (x t : ℝ) (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16)
    (ht0 : 0 ≤ t) (ht : t ≤ 2 / x^4) : t^6 ≤ 1 / x^27 := by
  have h6 := pow_le_pow_left₀ ht0 ht 6
  have he : (2 / x^4)^6 = 64 / x^24 := by field_simp <;> ring
  rw [he] at h6
  have hxquarter : x ≤ 1 / 4 := hxsmall.trans (by norm_num)
  have hx3 := pow_le_pow_left₀ hx.le hxquarter 3
  have hc : 64 * x^3 ≤ 1 := by norm_num at hx3; nlinarith
  have hratio : 64 / x^24 ≤ 1 / x^27 := by
    apply (div_le_div_iff₀ (by positivity : 0 < x^24) (by positivity : 0 < x^27)).mpr
    have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ x^24 by positivity)
    nlinarith [show x^24 * x^3 = x^27 by ring]
  exact h6.trans hratio

theorem actual_large_frontier_conclusion {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {Z : List (Finset V)}
    (hfront : OrderedCutFrontier G U S Z) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (x : ℝ) (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16)
    (t : ℕ) (ht : 2^16 ≤ t) (htupper : (t : ℝ) ≤ 2 / x^4)
    (hN : 1 / x^600 ≤ (S.card : ℝ)) (hm : t ≤ Z.length)
    (hsize : ∀ K ∈ Z, (S.card : ℝ) / (t : ℝ)^6 ≤ (K.card : ℝ)) :
    ∃ K : ℕ, (t : ℝ) ≤ (K : ℝ)^4 ∧ (K : ℝ) ≤ 1 / x^140 ∧
      ∃ γ : EHP6.Blockade Y K ((S.card : ℝ) / (K : ℝ)^64), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i) := by
  have hN0 : 0 < (S.card : ℝ) := (show 0 < 1 / x^600 by positivity).trans_le hN
  have hmupper := (ordered_frontier_count_from_scale hfront t (by omega) hN0 hsize).trans
    (frontier_count_paper_upper x (t : ℝ) hx hxsmall (Nat.cast_nonneg _) htupper)
  have hmlarge : 2^16 ≤ Z.length := by omega
  have hm1 : (1 : ℝ) ≤ Z.length := by exact_mod_cast (show 1 ≤ Z.length by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htm : (t : ℝ) ≤ Z.length := by exact_mod_cast hm
  have hpow := pow_le_pow_left₀ ht0.le htm 6
  have hwidth : ∀ i : Fin Z.length, (S.card : ℝ) / (Z.length : ℝ)^6 ≤ ((Z.get i).card : ℝ) := by
    intro i
    exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity : 0 < (t : ℝ)^6) hpow).trans
      (hsize _ (List.get_mem Z i))
  have horder := global_order_suffices x (Z.length : ℝ) (S.card : ℝ) hx hxsmall hm1 hmupper hN
  obtain ⟨K, hlo, hup, γ, hγm, htypes⟩ := quantitative_frontier G U Y hfront hSY hout hfree hmlarge
    hx (hxsmall.trans (by norm_num)) (Nat.cast_nonneg _) horder hwidth
  exact ⟨K, htm.trans hlo,
    global_output_length_upper x (Z.length : ℝ) (K : ℝ) hx hxsmall (Nat.cast_nonneg _) hmupper hup,
    γ, hγm, htypes⟩

#print axioms ordered_frontier_count_from_scale
#print axioms frontier_count_paper_upper
#print axioms actual_large_frontier_conclusion

end AllPathsLocal
