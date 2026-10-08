import AllPathsP7Round1
import EHP6.Nice

/-!
Lemma 4.3 and niceness for complement-P7-free graphs (the P7 analogues of
`EHP6.round1_blockade` and `EHP6.nice_P6`). The cited inputs are displayed as the
propositions `RodlCoP7`, `NssPath7` and `EHP6.NssComb`. Nothing here asserts EH(P7).
-/

namespace AllPathsLocal

open Finset Classical

theorem p7_r3_F {x δ s f : ℝ} {L : ℕ} (hx : 0 < x) (hxL : x ≤ 1 / 2 ^ (L + 20310))
    (hδ0 : 0 < δ) (hδL : 1 ≤ δ * 2 ^ L) (hs : 1 / x ^ (L + 20310) ≤ s) (hf : δ * s ≤ f) :
    1 / x ^ 1359 ≤ f := by
  have hx1 : x ≤ 1 := hxL.trans (by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num))
  have hxL' : x * 2 ^ L ≤ 1 := by
    have h1 : x * 2 ^ (L + 20310) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hxL (show (0 : ℝ) ≤ 2 ^ (L + 20310) by positivity)
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    have h2 : x * 2 ^ L ≤ x * 2 ^ (L + 20310) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hx.le
    linarith
  have hδx : x ≤ δ := by
    have h1 : x * 2 ^ L ≤ δ * 2 ^ L := hxL'.trans hδL
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have h1 : 1 ≤ s * x ^ (L + 20310) := (div_le_iff₀ (by positivity)).mp hs
  rw [div_le_iff₀ (by positivity)]
  have h2 : x ^ (L + 20310) ≤ x ^ 1360 := pow_le_pow_of_le_one hx.le hx1 (by omega)
  have h3 : s * x ^ (L + 20310) ≤ s * x ^ 1360 := mul_le_mul_of_nonneg_left h2 hs0.le
  have h4 : s * x ^ 1360 = (x * s) * x ^ 1359 := by ring
  have h5 : (x * s) * x ^ 1359 ≤ (δ * s) * x ^ 1359 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδx hs0.le) (by positivity)
  have h6 : (δ * s) * x ^ 1359 ≤ f * x ^ 1359 :=
    mul_le_mul_of_nonneg_right hf (by positivity)
  linarith

theorem p7_r3_w {s f δ k : ℝ} {L : ℕ} (hk : 2 ≤ k) (hδL : 1 ≤ δ * 2 ^ L) (hδ0 : 0 < δ)
    (hf : δ * s ≤ f) (hs : 0 ≤ s) : s / k ^ (L + 20310) ≤ f / k ^ 20310 := by
  have hk0 : 0 < k := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : f * k ^ (L + 20310) = (f * k ^ L) * k ^ 20310 := by rw [pow_add]; ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hkL : (2 : ℝ) ^ L ≤ k ^ L := pow_le_pow_left₀ (by norm_num) hk L
  have h1 : δ * s * 2 ^ L ≤ f * k ^ L :=
    mul_le_mul hf hkL (by positivity) (le_trans (by positivity) hf)
  have h2 : s * 1 ≤ s * (δ * 2 ^ L) := mul_le_mul_of_nonneg_left hδL hs
  linarith [show s * (δ * 2 ^ L) = δ * s * 2 ^ L by ring]

theorem p7_r3_c_core (s f A P : ℝ) (hA : 0 < A) (hP : (2 : ℝ) ^ 20 ≤ P)
    (hfs : s ≤ f * A) (hsA : P * A ≤ s) :
    s / (A * P) ≤ (⌊(1 / 420) ^ 2 * f⌋₊ : ℝ) := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hfP : P ≤ f := le_of_mul_le_mul_right (hsA.trans hfs) hA
  have hcP : 2 ≤ (1 / 420 : ℝ) ^ 2 * P := by
    have h0 : (2 : ℝ) ≤ (1 / 420) ^ 2 * 2 ^ 20 := by norm_num
    have h1 : (1 / 420 : ℝ) ^ 2 * 2 ^ 20 ≤ (1 / 420) ^ 2 * P :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    linarith
  have hcf : (1 / 420 : ℝ) ^ 2 * P ≤ (1 / 420) ^ 2 * f :=
    mul_le_mul_of_nonneg_left hfP (by positivity)
  have h1 : 1 ≤ (1 / 420 : ℝ) ^ 2 * f := by linarith
  have h2 := EHP6.floor_half h1
  have hfA : 0 ≤ f * A := mul_nonneg (le_trans hP0.le hfP) hA.le
  have h4 : s / (A * P) ≤ (1 / 420) ^ 2 * f / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : (f * A) * 2 ≤ (f * A) * ((1 / 420) ^ 2 * P) := mul_le_mul_of_nonneg_left hcP hfA
    have e : (1 / 420 : ℝ) ^ 2 * f / 2 * (A * P) = (f * A) * ((1 / 420) ^ 2 * P) / 2 := by ring
    rw [e]
    linarith
  linarith

theorem p7_r3_c {s f δ : ℝ} {L : ℕ} (hδL : 1 ≤ δ * 2 ^ L) (hδ0 : 0 < δ)
    (hsA : (2 : ℝ) ^ (L + 20310) ≤ s) (hf : δ * s ≤ f) :
    s / 2 ^ (L + 20310) ≤ (⌊(1 / 420) ^ 2 * f⌋₊ : ℝ) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hsA
  have hfs : s ≤ f * 2 ^ L := by
    have h1 : s * 1 ≤ s * (δ * 2 ^ L) := mul_le_mul_of_nonneg_left hδL hs0
    have h2 : δ * s * 2 ^ L ≤ f * 2 ^ L := mul_le_mul_of_nonneg_right hf (by positivity)
    linarith [show s * (δ * 2 ^ L) = δ * s * 2 ^ L by ring]
  have hbig : (2 : ℝ) ^ 20 ≤ 2 ^ 20310 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  rw [pow_add] at hsA ⊢
  exact p7_r3_c_core s f (2 ^ L) (2 ^ 20310) (by positivity) hbig hfs
    (by rw [mul_comm]; exact hsA)

/-- Lemma 4.3 for P7: there is `d ≥ 200` such that for every `x ∈ (0, 2^-d)` and
    every complement-P7-free `G[S]` with `|S| ≥ x^-d` there is, for some real
    `k ∈ [2, 1/x]`, an `x`-semisparse `(k, |S|/k^d)`-blockade. -/
theorem round1_blockade_p7 (hR : RodlCoP7) (hP : NssPath7) (hcomb : EHP6.NssComb) :
    ∃ d : ℕ, 200 ≤ d ∧ ∀ x : ℝ, 0 < x → x < 1 / 2 ^ d →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      EHP6.Free H P7ᶜ → ∀ S : Finset W, 1 / x ^ d ≤ (S.card : ℝ) →
        ∃ k : ℝ, 2 ≤ k ∧ k * x ≤ 1 ∧
          ∃ β : EHP6.Blockade S k (S.card / k ^ d), β.IsSemisparse H x := by
  obtain ⟨δ, hδ0, hR⟩ := hR (1 / 2 ^ 200) (by norm_num) (by norm_num)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have hδL : 1 ≤ δ * 2 ^ L := by rw [div_lt_iff₀ hδ0] at hL; linarith
  refine ⟨L + 20310, by omega, fun x hx hxd W _ _ H _ hfree S hS => ?_⟩
  obtain ⟨F, hFS, hFc, hFr⟩ := hR W H hfree S
  obtain ⟨hA, hxA⟩ := EHP6.r3_x (d := L + 20310) (by omega) hx hxd
  have hsA : (2 : ℝ) ^ (L + 20310) ≤ S.card := hA.trans (hxA.trans hS)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx2 : 2 * x ≤ 1 := by
    have : (2 : ℝ) ≤ 2 ^ (L + 20310) := le_self_pow₀ (by norm_num) (by omega)
    have h := (le_div_iff₀ hx).1 (this.trans hA)
    linarith
  rcases hFr with hsp | hspc
  · have hsp' : EHP6.Sparse H ((1 / 2 ^ 64) ^ 3 / 2 ^ 8) F := by
      rw [show ((1 : ℝ) / 2 ^ 64) ^ 3 / 2 ^ 8 = 1 / 2 ^ 200 by norm_num]; exact hsp
    have hx64 : x ≤ 1 / 2 ^ 64 := by
      refine hxd.le.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hFbig := p7_r3_F hx hxd.le hδ0 hδL hS hFc
    obtain ⟨k, hk2, hkx, β, hβ⟩ := round1_p7 hcomb hP hfree hx hx64 F hsp' hFbig
    exact ⟨k, hk2, hkx, β.mono hFS le_rfl (p7_r3_w hk2 hδL hδ0 hFc hS0),
      fun i j hij => hβ i j hij⟩
  · have hnot := compl_not_contains_p7 hfree F
    have hspc' : EHP6.Sparse Hᶜ ((1 / 420) ^ 2) F :=
      EHP6.sparse_sub hspc subset_rfl
        (mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _))
    obtain ⟨β, hβ⟩ := hP (1 / 420) (by norm_num) le_rfl W Hᶜ F hspc' hnot
    have hw := p7_r3_c hδL hδ0 hsA hFc
    refine ⟨2, le_rfl, hx2, β.mono hFS (by norm_num) hw, fun i j hij => Or.inl ?_⟩
    intro a ha b hb
    have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    by_contra hn
    exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj H a b).2 ⟨hab, hn⟩)

/-- Niceness of P7 (NSS VII Theorem 6.2 for P7): for every `ε ∈ (0, 1/2)` and every
    complement-P7-free `G[S]` with `|S| ≥ ε^(-10d^2)` there is an
    `(ε^-1, ε^(10d^2)|S|)`-blockade in which every two blocks are complete or
    weakly `ε^d`-sparse. -/
theorem nice_P7 (hR : RodlCoP7) (hP : NssPath7) (hcomb : EHP6.NssComb) :
    ∃ d : ℕ, 200 ≤ d ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      EHP6.Free H P7ᶜ → ∀ S : Finset W, 1 / ε ^ (10 * d ^ 2) ≤ (S.card : ℝ) →
        ∃ β : EHP6.Blockade S (1 / ε) (ε ^ (10 * d ^ 2) * S.card),
          β.IsSemisparse H (ε ^ d) := by
  obtain ⟨d, hd, h43⟩ := round1_blockade_p7 hR hP hcomb
  refine ⟨d, hd, fun ε hε0 hε1 W _ _ H _ hfree S hS => ?_⟩
  have hε1' : ε < 1 := by linarith
  have hx : ε ^ (5 * d) < 1 / 2 ^ d := by
    have h1 : ε ^ (5 * d) ≤ ε ^ d := pow_le_pow_of_le_one hε0.le hε1'.le (by omega)
    have h2 : ε ^ d < (1 / 2) ^ d := pow_lt_pow_left₀ hε1 hε0.le (by omega)
    rw [one_div_pow] at h2
    linarith
  obtain ⟨β, hβ⟩ := EHP6.layout_theorem (G := H) hε0 hε1' (by omega) S (fun F hF hFc =>
    h43 (ε ^ (5 * d)) (by positivity) hx W H hfree F (EHP6.nice_size hε0 hε1'.le hS hFc))
  have e : (ε ^ (5 * d)) ^ (2 * d) = ε ^ (10 * d ^ 2) := by rw [← pow_mul]; congr 1; ring
  exact ⟨β.mono subset_rfl le_rfl (by rw [e]), fun i j hij => hβ i j hij⟩

#print axioms round1_blockade_p7
#print axioms nice_P7
end AllPathsLocal
