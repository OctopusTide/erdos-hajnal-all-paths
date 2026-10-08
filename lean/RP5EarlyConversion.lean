import RP5LengthBounds
import RP5WidthBounds

namespace AllPathsLocal

theorem fourth_root_length_nontrivial (m K : ℕ) (hm : 2 ≤ m)
    (hroot : (m : ℝ) ≤ (K : ℝ) ^ 4) : 2 ≤ K := by
  by_contra h
  have hK : K ≤ 1 := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hKR : (K : ℝ) ≤ 1 := by exact_mod_cast hK
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg K) hKR 4
  norm_num at hp
  linarith

/-- Every genuine RP4 early output gives an EXACT actual length K, including the
    floor alternatives, with common width N/K^64. p<=7 covers first and second
    Tooth calls when the original frontier width is N/m^6. -/
theorem rp4_early_convert {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {A Y : Finset V}
    (hAY : A ⊆ Y) {m : ℕ} {x N : ℝ} {p : ℕ}
    (hm : 2 ^ 16 ≤ m) (hx : 0 < x) (hxsmall : x ≤ 1 / (m : ℝ) ^ 2)
    (hp : p ≤ 7) (hN : N ≤ (m : ℝ) ^ p * A.card)
    (hearly : RP4Early G A x m) :
    ∃ K : ℕ, (m : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ 1 / x ∧
      ∃ γ : EHP6.Blockade Y K (N / (K : ℝ) ^ 64), γ.m = K ∧ γ.IsPure G := by
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hA0 : (0 : ℝ) ≤ A.card := by positivity
  obtain ⟨hfloor3, hfloor4, hfloor3up, hfloor4up⟩ :=
    tooth_floor_length_bounds m x (by omega) hx hxsmall
  have hmUp : (m : ℝ) ≤ 1 / x :=
    (show (m : ℝ) ≤ (⌊1 / x⌋₊ : ℝ) by exact_mod_cast hfloor3).trans hfloor3up
  rcases hearly with ⟨K, hlo, hup, β, hpure⟩ | ⟨K, hlo, hup, β, hpure⟩ |
    ⟨β, hkind⟩ | ⟨β, hcomp⟩
  · have hK2 : 2 ≤ K := fourth_root_length_nontrivial m K (by omega) hlo
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have hw := polynomial_width_convert (m : ℝ) (K : ℝ) N (A.card : ℝ) p 4 64
      (by positivity) hK1 hA0 hN hlo (by omega)
    exact ⟨K, hlo, hup, (exactLengthBlockade β).mono hAY le_rfl hw, rfl,
      exactLengthBlockade_pure G β hpure⟩
  · obtain ⟨hsq, hK2, hKm⟩ := tl2_length_bounds (m : ℝ) (K : ℝ) hmR (by positivity) hlo hup
    have hK1 : (1 : ℝ) ≤ K := by linarith
    have hk4 : (m : ℝ) ≤ (K : ℝ) ^ 4 :=
      hsq.trans (pow_le_pow_right₀ hK1 (by decide))
    have hw' := scaled_width_convert (m : ℝ) (K : ℝ) N (A.card : ℝ) 1
      2 p 0 1 0 1 64 hm1 hK2 hA0 (by norm_num) hN hsq
      (by simp; linarith) (by omega)
    have hw : N / (K : ℝ) ^ 64 ≤ (A.card : ℝ) / (2 * m) := by simpa using hw'
    exact ⟨K, hk4, hKm.trans hmUp, (exactLengthBlockade β).mono hAY le_rfl hw, rfl,
      exactLengthBlockade_pure G β hpure⟩
  · let K := ⌊1 / x⌋₊
    have hmK : (m : ℝ) ≤ K := by exact_mod_cast hfloor3
    have hK2 : (2 : ℝ) ≤ K := by linarith
    have hK1 : (1 : ℝ) ≤ K := by linarith
    have hK4 : (m : ℝ) ≤ (K : ℝ) ^ 4 :=
      hmK.trans (by simpa using pow_le_pow_right₀ hK1 (by decide : 1 ≤ 4))
    have hfloor : 1 / x / 2 ≤ (K : ℝ) := reciprocal_floor_lower (1 / x) (by linarith)
    have hrecip : 1 ≤ (2 * (m : ℝ) ^ 0 * K) * x := by
      have hh := mul_le_mul_of_nonneg_right (show 1 / x ≤ 2 * (K : ℝ) by linarith) hx.le
      have heq : (1 / x) * x = 1 := by field_simp
      rw [heq] at hh
      simpa using hh
    have hw' := scaled_width_convert (m : ℝ) (K : ℝ) N (A.card : ℝ) x
      1 p 0 1 2 0 64 hm1 hK2 hA0 hx.le hN (by simpa using hmK) hrecip (by omega)
    have hw : N / (K : ℝ) ^ 64 ≤ x ^ 2 * A.card / m := by simpa using hw'
    have hpure : β.IsPure G := by
      rcases hkind with h | h
      · exact fun i j hij => Or.inl (h i j hij)
      · exact fun i j hij => Or.inr (h i j hij)
    exact ⟨K, hK4, hfloor3up, (exactLengthBlockade β).mono hAY le_rfl hw, rfl,
      exactLengthBlockade_pure G β hpure⟩
  · let K := ⌊1 / (x * m)⌋₊
    have hmK : (m : ℝ) ≤ K := by exact_mod_cast hfloor4
    have hK2 : (2 : ℝ) ≤ K := by linarith
    have hK1 : (1 : ℝ) ≤ K := by linarith
    have hK4 : (m : ℝ) ≤ (K : ℝ) ^ 4 :=
      hmK.trans (by simpa using pow_le_pow_right₀ hK1 (by decide : 1 ≤ 4))
    have ha2 : (2 : ℝ) ≤ 1 / (x * m) := by
      exact hK2.trans (Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / (x * m)))
    have hfloor : 1 / (x * m) / 2 ≤ (K : ℝ) := reciprocal_floor_lower _ ha2
    have hrecip : 1 ≤ (2 * (m : ℝ) ^ 1 * K) * x := by
      have hh := mul_le_mul_of_nonneg_right
        (show 1 / (x * m) ≤ 2 * (K : ℝ) by linarith) (show 0 ≤ x * (m : ℝ) by positivity)
      have heq : (1 / (x * m)) * (x * m) = 1 := by field_simp
      rw [heq] at hh
      convert hh using 1 <;> ring
    have hw' := scaled_width_convert (m : ℝ) (K : ℝ) N (A.card : ℝ) x
      1 p 1 0 3 2 64 hm1 hK2 hA0 hx.le hN (by simpa using hmK) hrecip (by omega)
    have hw : N / (K : ℝ) ^ 64 ≤ x ^ 3 * A.card / 4 := by norm_num at hw' ⊢; exact hw'
    have hpure : β.IsPure G := fun i j hij => Or.inl (hcomp i j hij)
    exact ⟨K, hK4, hfloor4up, (exactLengthBlockade β).mono hAY le_rfl hw, rfl,
      exactLengthBlockade_pure G β hpure⟩

#print axioms fourth_root_length_nontrivial
#print axioms rp4_early_convert

end AllPathsLocal
