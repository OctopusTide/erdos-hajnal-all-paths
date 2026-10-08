import RP5Tooth
import AllPathsRootedRecurrence
import AllPathsBootstrap

/-!
# The quantified rooted Tooth contract

`LowerTooth G r A e c k d E η` is the Tooth contract `T_r` of the main paper
(Section "One ambient class and a quantified rooted contract") for one host graph
`G`: roots `U` outside `Y` with no rooted induced `r`-vertex path of the complement
into `Y`. The restricted outcome keeps its actual scale `z ∈ [x^c, y]`. The RP5 Tooth
supplies the contract at `r = 5` for every host.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A root with no rooted `q`-vertex path has no rooted `(q+1)`-vertex path. -/
theorem rooted_path_free_succ (q : ℕ) (hq : 1 ≤ q) {Y : Finset V} {r : V}
    (h : RootedPathFree G q Y r) : RootedPathFree G (q + 1) Y r := by
  rintro ⟨p, i, hi, hp, hpi, htail⟩
  apply h
  refine ⟨fun j : Fin q => p (Fin.castLE (Nat.le_succ q) j), ⟨0, hq⟩, rfl,
    inducedPath_castLE Gᶜ (Nat.le_succ q) p hp, ?_, ?_⟩
  · have e : Fin.castLE (Nat.le_succ q) ⟨0, hq⟩ = i := Fin.ext (by
      rw [Fin.val_castLE]; exact hi.symm)
    show p (Fin.castLE (Nat.le_succ q) ⟨0, hq⟩) = r
    rw [e]
    exact hpi
  · intro j hj
    show p (Fin.castLE (Nat.le_succ q) j) ∈ Y
    apply htail
    intro hc
    apply hj
    apply Fin.ext
    have h1 := congrArg Fin.val hc
    rw [Fin.val_castLE] at h1
    show j.val = 0
    omega

/-- The Tooth contract `T_r` for the host `G`. -/
def LowerTooth (G : SimpleGraph V) [DecidableRel G.Adj] (r A e c k d E : ℕ) (η : ℝ) : Prop :=
  ∀ (U Y : Finset V) (x y : ℝ), (∀ u ∈ U, u ∉ Y) → (∀ u ∈ U, RootedPathFree G r Y u) →
    0 < x → x ≤ y → y ≤ η → 1 / x ^ E ≤ (Y.card : ℝ) →
    (∃ S ⊆ Y, y ^ A * Y.card ≤ (S.card : ℝ) ∧ FullOrSmall G U x S) ∨
    (∃ z : ℝ, x ^ c ≤ z ∧ z ≤ y ∧ ∃ W ⊆ Y, z ^ e * Y.card ≤ (W.card : ℝ) ∧
      EHP6.Restricted G (z ^ 4) W) ∨
    (∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x ^ k ∧
      ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ) ^ d), γ.m = K ∧
        ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i))

/-- The verified RP5 Tooth is the contract `T_5` for every host. -/
theorem lowerTooth_five (G : SimpleGraph V) [DecidableRel G.Adj] :
    LowerTooth G 5 26 18 1 140 64 600 (1 / 2 ^ 16) := by
  intro U Y x y hout hfree hx hxy hy hN
  rcases rp5_tooth G U Y x y hout (fun u hu => (rooted_path_free_five G Y u).mp (hfree u hu))
    hx hxy hy hN with h | ⟨W, hWY, hWsize, hWdeg⟩ | h
  · exact Or.inl h
  · right; left
    have hy0 : 0 < y := hx.trans_le hxy
    refine ⟨y, by rw [pow_one]; exact hxy, le_rfl, W, hWY, hWsize, ?_⟩
    have he0 : (0 : ℝ) ≤ y ^ 4 := by positivity
    rcases hWdeg with hdeg | hdeg
    · left
      intro v hv
      have h1 := hdeg v hv
      have h2 : y ^ 4 * ((W.card : ℝ) - 1) ≤ y ^ 4 * W.card :=
        mul_le_mul_of_nonneg_left (by linarith) he0
      unfold EHP6.nbrs
      rw [filter_card_classical]
      rw [filter_card_classical] at h1
      linarith
    · right
      intro v hv
      have h1 := hdeg v hv
      have h2 : y ^ 4 * ((W.card : ℝ) - 1) ≤ y ^ 4 * W.card :=
        mul_le_mul_of_nonneg_left (by linarith) he0
      unfold EHP6.nbrs
      rw [filter_card_classical]
      rw [filter_card_classical] at h1
      linarith
  · exact Or.inr (Or.inr h)

/-- A contract for RP(r+1) roots applies to RP(r) roots. -/
theorem lowerTooth_pred {r A e c k d E : ℕ} {η : ℝ} (hr : 1 ≤ r)
    (h : LowerTooth G (r + 1) A e c k d E η) : LowerTooth G r A e c k d E η :=
  fun U Y x y hout hfree hx hxy hy hN =>
    h U Y x y hout (fun u hu => rooted_path_free_succ r hr (hfree u hu)) hx hxy hy hN

/-- Enlarging the constants of a contract. -/
theorem lowerTooth_mono {r A e c k d E A' e' c' k' d' E' : ℕ} {η η' : ℝ}
    (h : LowerTooth G r A e c k d E η) (hη : η' ≤ η) (hη1 : η ≤ 1)
    (hA : A ≤ A') (he : e ≤ e') (hc : c ≤ c') (hk : k ≤ k') (hd : d ≤ d') (hE : E ≤ E') :
    LowerTooth G r A' e' c' k' d' E' η' := by
  intro U Y x y hout hfree hx hxy hy hN
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := (hy.trans hη).trans hη1
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
  have hN' : 1 / x ^ E ≤ (Y.card : ℝ) := by
    refine le_trans ?_ hN
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
      (pow_le_pow_of_le_one hx.le hx1 hE)
  rcases h U Y x y hout hfree hx hxy (hy.trans hη) hN' with ⟨S, hS, hsize, hfull⟩ |
      ⟨z, hz1, hz2, W, hW, hsize, hres⟩ | ⟨K, hK1, hK2, γ, hm, hγ⟩
  · left
    refine ⟨S, hS, le_trans ?_ hsize, hfull⟩
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hy0.le hy1 hA) hY0
  · right; left
    have hz0 : 0 < z := lt_of_lt_of_le (pow_pos hx _) hz1
    refine ⟨z, le_trans (pow_le_pow_of_le_one hx.le hx1 hc) hz1, hz2, W, hW,
      le_trans ?_ hsize, hres⟩
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hz0.le (hz2.trans hy1) he) hY0
  · right; right
    have hK1' : (1 : ℝ) ≤ K := by
      have : 1 ≤ 1 / y := by rw [le_div_iff₀ hy0]; linarith
      linarith
    have hK0 : (0 : ℝ) < K := by linarith
    refine ⟨K, hK1, hK2.trans ?_, γ.mono subset_rfl le_rfl ?_, hm, hγ⟩
    · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
        (pow_le_pow_of_le_one hx.le hx1 hk)
    · exact div_le_div_of_nonneg_left hY0 (pow_pos hK0 _) (pow_le_pow_right₀ hK1' hd)

#print axioms rooted_path_free_succ
#print axioms lowerTooth_five
#print axioms lowerTooth_mono
end AllPathsLocal
