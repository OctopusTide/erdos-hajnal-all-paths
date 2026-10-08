import AllPathsFinalGen
import AllPathsP7Round1
import EHP6.Nice

/-!
# Variable-scale local oracles and the sparsification potential

The bootstrap of the main paper (Appendix "Variable-scale local oracles and the
sparsification potential") for arbitrary oracle constants. A local oracle with
constants `a, c, d, e, L` gives, for a class of complement-`P_s`-free graphs, the
round-one blockade and then generalized niceness through the layout theorem of the
P6 project. The restricted outcome keeps its ACTUAL scale `z ∈ [x^c, y]`; the
potential drops to `z^(7/6)` in the sparse orientation, and the sparse-path theorem
`EHP6.nss_path` is used at precision `z^2` in the other orientation. This file is the
general form of `AllPathsP7Round1.lean` and `AllPathsP7Nice.lean`.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The variable-scale local oracle with constants `a, c, d, e, L` below the cutoff
    `y₀`: a `y^3`-sparse set of order at least `x^(-L)` is `2y^4`-sparse, or has a
    directed `x`-sparse pair, or a semisparse blockade of actual length in
    `[1/y, x^(-c)]`, or a restricted set at its actual scale `z ∈ [x^c, y]`. -/
def LocalOracle (G : SimpleGraph V) [DecidableRel G.Adj] (y₀ : ℝ) (a c d e L : ℕ) : Prop :=
  ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ y₀ → ∀ S : Finset V, EHP6.Sparse G (y ^ 3) S →
    1 / x ^ L ≤ (S.card : ℝ) →
    EHP6.Sparse G (2 * y ^ 4) S ∨
    (∃ X ⊆ S, ∃ Y ⊆ S, Disjoint X Y ∧ y ^ a * S.card ≤ X.card ∧
      (1 - 4 * y) * S.card ≤ Y.card ∧ EHP6.SparseTo G x Y X) ∨
    OracleBlockade G S x y c d ∨ OracleRestricted G S x y c e

theorem localOracle_mono {y₀ y₁ : ℝ} {a c d e L : ℕ} (h : LocalOracle G y₀ a c d e L)
    (hy : y₁ ≤ y₀) : LocalOracle G y₁ a c d e L :=
  fun x y hx hxy hy1 S hsp hS => h x y hx hxy (hy1.trans hy) S hsp hS

theorem gen_r1_width {s b K : ℝ} (d : ℕ) (hK : 16 ≤ K) (hb : s / 2 ^ 8 ≤ b) (hs : 0 ≤ s) :
    s / K ^ (d + 2) ≤ b / K ^ d := by
  have hK0 : 0 < K := by linarith
  rw [div_le_div_iff₀ (pow_pos hK0 _) (pow_pos hK0 _)]
  have hK2 : 256 ≤ K ^ 2 := by nlinarith
  have e : b * K ^ (d + 2) = (b * K ^ 2) * K ^ d := by rw [pow_add]; ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK0.le _)
  have hb0 : s ≤ 2 ^ 8 * b := by linarith [show s / 2 ^ 8 * 2 ^ 8 = s by ring]
  have hbs : 0 ≤ b := by linarith
  nlinarith

/-- One step of round one. -/
theorem round1_step_gen {y₀ : ℝ} {a c d e L : ℕ} (hy₀ : y₀ ≤ 1 / 2 ^ 64)
    (horacle : LocalOracle G y₀ a c d e L) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyy : y ≤ y₀) (S : Finset V)
    (hsp : EHP6.Sparse G (y ^ 3 / 2 ^ 8) S)
    (hS : 2 ^ 8 / x ^ L ≤ (S.card : ℝ)) :
    (∃ T ⊆ S, (S.card : ℝ) / 2 ^ 8 ≤ T.card ∧ EHP6.Sparse G (2 * y ^ 4) T) ∨
    OracleBlockade G S x y c (d + 2) ∨
    (∃ β : EHP6.Blockade S (1 / y) (y ^ (a + 2) * S.card), β.IsSparse G x) ∨
    (∃ z : ℝ, x ^ c ≤ z ∧ z ≤ y ∧ ∃ T ⊆ S, z ^ e * ((S.card : ℝ) / 2 ^ 8) ≤ T.card ∧
      EHP6.Restricted G (z ^ 4) T) := by
  have hy : y ≤ 1 / 2 ^ 64 := hyy.trans hy₀
  have hy0 : 0 < y := hx.trans_le hxy
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS
  have hw : 0 < y ^ (a + 2) * S.card := by positivity
  have hy5 : 4 * y ≤ 1 / 5 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 20 by norm_num]
  have hq : 0 ≤ 1 - 4 * y := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest
      (EHP6.SChain G S x (y ^ (a + 2) * S.card) (1 - 4 * y)) S.card := ⟨_, rfl⟩
  have hPn : EHP6.SChain G S x (y ^ (a + 2) * S.card) (1 - 4 * y) n := by
    rw [hn]; exact Nat.findGreatest_spec (Nat.zero_le _) (EHP6.schain_zero S _ _ _)
  have hmax : ¬ EHP6.SChain G S x (y ^ (a + 2) * S.card) (1 - 4 * y) (n + 1) := fun h => by
    have hb := EHP6.schain_bound hw h
    rw [hn] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨B, hsub, hdisj, hspB, hwid, hlast⟩ := hPn
  by_cases hn1 : 1 / y ≤ n
  · right; right; left
    refine ⟨⟨n, fun i => B i, hn1, fun i => hsub i i.2.le, fun i => hwid i i.2,
      fun i j hij => hdisj i i.2.le j j.2.le (fun h => hij (Fin.ext h))⟩, fun i j hij => ?_⟩
    exact hspB i j hij j.2.le
  push Not at hn1
  have hny : (n : ℝ) * (4 * y) ≤ 4 := by
    have := (lt_div_iff₀ hy0).1 hn1
    nlinarith
  have hBn : (S.card : ℝ) / 2 ^ 8 ≤ (B n).card := by
    have := EHP6.pow_one_sub_ge (by linarith) hy5 hny
    have h2 := mul_le_mul_of_nonneg_right this hSpos.le
    linarith [show (S.card : ℝ) / 2 ^ 8 = 1 / 256 * S.card by ring]
  have hBnS := hsub n le_rfl
  have hsp' : EHP6.Sparse G (y ^ 3) (B n) := EHP6.sparse_sub hsp hBnS (by
    have := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ 3)
    linarith [show y ^ 3 / 2 ^ 8 * S.card = y ^ 3 * (S.card / 2 ^ 8) by ring])
  have hBbig : 1 / x ^ L ≤ ((B n).card : ℝ) := by
    have e : (1 : ℝ) / x ^ L = 2 ^ 8 / x ^ L / 2 ^ 8 := by ring
    rw [e]
    have := div_le_div_of_nonneg_right hS (by norm_num : (0 : ℝ) ≤ 2 ^ 8)
    linarith
  rcases horacle x y hx hxy hyy (B n) hsp' hBbig with h |
      ⟨X, hX, Y, hY, hXY, hXs, hYs, hYX⟩ | ⟨K, hK1, hK2, β, hβ⟩ | ⟨z, hz1, hz2, T, hT, hTs, hTr⟩
  · exact Or.inl ⟨B n, hBnS, hBn, h⟩
  · exfalso
    refine hmax (EHP6.schain_extend hq hsub hdisj hspB hwid hlast hX hY hXY ?_ hYs hYX)
    have hy2 : y ^ 2 ≤ 1 / 2 ^ 8 := by
      have : y ^ 2 ≤ (1 / 2 ^ 64) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
      linarith [show ((1 : ℝ) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 8 by norm_num]
    have h1 := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ a)
    have h2 : y ^ (a + 2) * S.card ≤ y ^ a * ((S.card : ℝ) / 2 ^ 8) := by
      have := mul_le_mul_of_nonneg_left hy2 (by positivity : (0 : ℝ) ≤ y ^ a * S.card)
      linarith [show y ^ a * S.card * y ^ 2 = y ^ (a + 2) * S.card by ring,
        show y ^ a * S.card * (1 / 2 ^ 8) = y ^ a * ((S.card : ℝ) / 2 ^ 8) by ring]
    linarith
  · have hK16 : (16 : ℝ) ≤ K := by
      have h1 : (2 : ℝ) ^ 64 ≤ K := EHP6.cl_ell64 hy0 hy hK1
      linarith [show (16 : ℝ) ≤ 2 ^ 64 by norm_num]
    right; left
    exact ⟨K, hK1, hK2, β.mono hBnS le_rfl (gen_r1_width d hK16 hBn hSpos.le),
      fun i j hij => hβ i j hij⟩
  · right; right; right
    refine ⟨z, hz1, hz2, T, hT.trans hBnS, le_trans ?_ hTs, hTr⟩
    have hz0 : 0 ≤ z := le_trans (by positivity) hz1
    exact mul_le_mul_of_nonneg_left hBn (by positivity)

/-- Admissible pair of the scale potential. -/
def GAdm (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (B : ℕ) (y : ℝ)
    (F : Finset V) : Prop :=
  F ⊆ S ∧ EHP6.Sparse G (y ^ 3 / 2 ^ 8) F ∧ y ^ B * (S.card : ℝ) ≤ F.card

/-- The target of round one: an `x`-semisparse blockade of real length
    `k ∈ [2, 1/x]` and width `|S|/k^D`. -/
def GGoal (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (D : ℕ) (x : ℝ) : Prop :=
  ∃ k : ℝ, 2 ≤ k ∧ k * x ≤ 1 ∧
    ∃ β : EHP6.Blockade S k (S.card / k ^ D), β.IsSemisparse G x

theorem gen_order_F {x y s f : ℝ} {B L Q : ℕ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hxy : x ≤ y) (hQ : L + B + 1 ≤ Q) (hs : 1 / x ^ Q ≤ s) (hf : y ^ B * s ≤ f) :
    2 ^ 8 / x ^ L ≤ f := by
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have h1 : 1 ≤ s * x ^ Q := (div_le_iff₀ (by positivity)).mp hs
  have h2 : x ^ B * s ≤ f :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le hxy B) hs0.le).trans hf
  rw [div_le_iff₀ (by positivity)]
  have h3 : (2 : ℝ) ^ 8 * x ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hx64 (show (0 : ℝ) ≤ 2 ^ 8 by positivity)
    norm_num at this ⊢
    linarith
  have hpow : x ^ Q ≤ x ^ (B + L + 1) := pow_le_pow_of_le_one hx.le hx1 (by omega)
  have h4 : s * x ^ Q ≤ f * x ^ L * x := by
    have a1 : s * x ^ Q ≤ s * x ^ (B + L + 1) := mul_le_mul_of_nonneg_left hpow hs0.le
    have a2 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ x ^ (L + 1) by positivity)
    have e1 : x ^ B * s * x ^ (L + 1) = s * x ^ (B + L + 1) := by ring
    have e2 : f * x ^ (L + 1) = f * x ^ L * x := by ring
    linarith
  have h5 : (2 : ℝ) ^ 8 * x ≤ f * x ^ L * x := by linarith
  exact le_of_mul_le_mul_right h5 hx

theorem gen_width_block {x y s f K k : ℝ} {B c d D : ℕ} (hx : 0 < x) (hxy : x ≤ y)
    (hy1 : y ≤ 1) (hc : 1 ≤ c) (hD : B + c * (d + 2) ≤ D)
    (hK1 : 1 / y ≤ K) (hK2 : K ≤ 1 / x ^ c) (hk : k = min K (1 / x))
    (hf : y ^ B * s ≤ f) (hs : 0 ≤ s) : s / k ^ D ≤ f / K ^ (d + 2) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK1
  have hyx : 1 / y ≤ 1 / x := div_le_div_of_nonneg_left (by norm_num) hx hxy
  have hyk : 1 / y ≤ k := by rw [hk]; exact le_min hK1 hyx
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hyk
  have hyk1 : 1 ≤ y * k := by
    rw [div_le_iff₀ hy0] at hyk
    linarith
  have hk1 : 1 ≤ k := by
    have h1 : 1 ≤ 1 / y := by
      rw [le_div_iff₀ hy0]
      linarith
    linarith
  have hKk : K ≤ k ^ c := by
    rcases le_total K (1 / x) with h | h
    · have e : k = K := by rw [hk]; exact min_eq_left h
      rw [e]
      have hK1' : 1 ≤ K := by rw [← e]; exact hk1
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ c := pow_le_pow_right₀ hK1' hc
    · have e : k = 1 / x := by rw [hk]; exact min_eq_right h
      rw [e, one_div_pow]
      exact hK2
  have hf0 : 0 ≤ f := le_trans (mul_nonneg (pow_nonneg hy0.le _) hs) hf
  rw [div_le_div_iff₀ (pow_pos hk0 _) (pow_pos hK0 _)]
  have h1 : s * K ^ (d + 2) ≤ s * (k ^ c) ^ (d + 2) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0.le hKk _) hs
  have e2 : s * (k ^ c) ^ (d + 2) = s * k ^ (c * (d + 2)) := by rw [← pow_mul]
  have h2 : (y * k) ^ B * (s * k ^ (c * (d + 2))) ≤ f * k ^ (B + c * (d + 2)) := by
    have := mul_le_mul_of_nonneg_right hf (pow_nonneg hk0.le (B + c * (d + 2)))
    have e : y ^ B * s * k ^ (B + c * (d + 2)) = (y * k) ^ B * (s * k ^ (c * (d + 2))) := by
      rw [pow_add, mul_pow]; ring
    linarith
  have h3 : 1 * (s * k ^ (c * (d + 2))) ≤ (y * k) ^ B * (s * k ^ (c * (d + 2))) :=
    mul_le_mul_of_nonneg_right (one_le_pow₀ hyk1) (mul_nonneg hs (pow_nonneg hk0.le _))
  have h4 : f * k ^ (B + c * (d + 2)) ≤ f * k ^ D :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk1 hD) hf0
  linarith

theorem gen_width_chain {y s f : ℝ} {a B D : ℕ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hs : 0 ≤ s)
    (hD : a + 2 + B ≤ D) (hf : y ^ B * s ≤ f) : s / (1 / y) ^ D ≤ y ^ (a + 2) * f := by
  have e : s / (1 / y) ^ D = y ^ D * s := by
    rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
  rw [e]
  have h1 : y ^ D ≤ y ^ (a + 2 + B) := pow_le_pow_of_le_one hy0.le hy1 hD
  have h2 : y ^ D * s ≤ y ^ (a + 2 + B) * s := mul_le_mul_of_nonneg_right h1 hs
  have h3 : y ^ (a + 2) * (y ^ B * s) ≤ y ^ (a + 2) * f :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have e2 : y ^ (a + 2) * (y ^ B * s) = y ^ (a + 2 + B) * s := by ring
  linarith

theorem gen_width_terminal {x y s f : ℝ} {B c Q D : ℕ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hy3 : x ^ (2 * c) ≤ y) (hQ : 2 * c * B + 2 ≤ Q) (hD : 2 * c * B + 2 ≤ D)
    (hs : 1 / x ^ Q ≤ s) (hf : y ^ B * s ≤ f) :
    4 / x ≤ f ∧ s / (1 / x) ^ D ≤ x * f / 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hx4 : 4 * x ≤ 1 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 4 by norm_num]
  have h1 : 1 ≤ s * x ^ Q := (div_le_iff₀ (by positivity)).mp hs
  have h2 : x ^ (2 * c * B) * s ≤ f := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x ^ (2 * c)) hy3 B
    have e : (x ^ (2 * c)) ^ B = x ^ (2 * c * B) := by rw [← pow_mul]
    rw [e] at h
    exact (mul_le_mul_of_nonneg_right h hs0.le).trans hf
  have hf0 : 0 ≤ f := le_trans (by positivity) h2
  have key : ∀ N : ℕ, 2 * c * B + 2 ≤ N → x ^ N * s ≤ f * x * x := by
    intro N hN
    have a1 : x ^ N ≤ x ^ (2 * c * B + 2) := pow_le_pow_of_le_one hx.le hx1 hN
    have a2 : x ^ N * s ≤ x ^ (2 * c * B + 2) * s := mul_le_mul_of_nonneg_right a1 hs0.le
    have a3 := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ x * x by positivity)
    have e1 : x ^ (2 * c * B) * s * (x * x) = x ^ (2 * c * B + 2) * s := by ring
    have e2 : f * (x * x) = f * x * x := by ring
    linarith
  constructor
  · rw [div_le_iff₀ hx]
    have h3 := key Q hQ
    by_contra hcon
    push Not at hcon
    have h6 : f * x * x < 4 * x := mul_lt_mul_of_pos_right hcon hx
    linarith [mul_comm s (x ^ Q)]
  · have e : s / (1 / x) ^ D = x ^ D * s := by
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [e]
    have h3 := key D hD
    have h4 : f * x * x ≤ f * x * (1 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hf0 hx.le)
    linarith

theorem gen_sparse_scale {x y z w s f t : ℝ} {B c e : ℕ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hB : 6 * (e + 1) ≤ B)
    (hw0 : 0 < w) (hw6 : w ^ 6 = z) (hw8 : w ≤ 1 / 2 ^ 8)
    (hz1 : x ^ c ≤ z) (hz2 : z ≤ y) (hz64 : z ≤ 1 / 2 ^ 64) (hs : 0 ≤ s)
    (hf : y ^ B * s ≤ f) (ht : z ^ e * (f / 2 ^ 8) ≤ t) :
    x ^ (2 * c) ≤ w ^ 7 ∧ w ^ 7 ≤ y / 2 ^ 8 ∧ z ^ 4 ≤ (w ^ 7) ^ 3 / 2 ^ 8 ∧
      (w ^ 7) ^ B * s ≤ t := by
  have hz0 : 0 < z := by rw [← hw6]; positivity
  have hw1 : w ≤ 1 := hw8.trans (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h (by positivity) (show (6 : ℕ) ≠ 0 by norm_num)
    have e1 : (w ^ 7) ^ 6 = z ^ 7 := by rw [← hw6]; ring
    have e2 : (x ^ (2 * c)) ^ 6 = x ^ (2 * c * 6) := (pow_mul x (2 * c) 6).symm
    rw [e1, e2] at h1
    have h2 : (x ^ c) ^ 7 ≤ z ^ 7 := pow_le_pow_left₀ (by positivity) hz1 7
    have e3 : (x ^ c) ^ 7 = x ^ (c * 7) := (pow_mul x c 7).symm
    rw [e3] at h2
    have h3 : x ^ (2 * c * 6) ≤ x ^ (c * 7) := pow_le_pow_of_le_one hx.le hx1 (by omega)
    linarith
  · have e : w ^ 7 = z * w := by rw [← hw6]; ring
    rw [e]
    have h1 : z * w ≤ y * (1 / 2 ^ 8) := mul_le_mul hz2 hw8 hw0.le (hz0.le.trans hz2)
    linarith [show y * (1 / 2 ^ 8) = y / 2 ^ 8 by ring]
  · have h3 : w ^ 3 ≤ (1 / 2 ^ 8) ^ 3 := pow_le_pow_left₀ hw0.le hw8 3
    have h3' : w ^ 3 ≤ 1 / 2 ^ 8 := h3.trans (by norm_num)
    have e1 : z ^ 4 = w ^ 21 * w ^ 3 := by rw [← hw6]; ring
    have e2 : (w ^ 7) ^ 3 / 2 ^ 8 = w ^ 21 * (1 / 2 ^ 8) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h3' (by positivity)
  · have hz8 : z ≤ 1 / 2 ^ 8 := hz64.trans (by norm_num)
    have h1 : z ^ B * s ≤ y ^ B * s :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hz2 B) hs
    have h2 : z ^ e * (z ^ B * s / 2 ^ 8) ≤ z ^ e * (f / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right (h1.trans hf) (by positivity)
    have e1 : (w ^ 7) ^ B = w ^ (7 * B) := (pow_mul w 7 B).symm
    have e2 : z ^ e * (z ^ B * s / 2 ^ 8) = z ^ (e + B) * s * (1 / 2 ^ 8) := by ring
    have h3 : z ^ (e + B) * s * z ≤ z ^ (e + B) * s * (1 / 2 ^ 8) :=
      mul_le_mul_of_nonneg_left hz8 (mul_nonneg (pow_nonneg hz0.le _) hs)
    have e3 : z ^ (e + B) * s * z = w ^ (6 * (e + B + 1)) * s := by
      rw [← hw6, ← pow_mul]; ring
    have h4 : w ^ (7 * B) ≤ w ^ (6 * (e + B + 1)) :=
      pow_le_pow_of_le_one hw0.le hw1 (by omega)
    have h5 : w ^ (7 * B) * s ≤ w ^ (6 * (e + B + 1)) * s := mul_le_mul_of_nonneg_right h4 hs
    rw [e1]
    linarith

theorem gen_width_compl {x y z s f t k : ℝ} {B c e Q D : ℕ} (hx : 0 < x)
    (hx64 : x ≤ 1 / 2 ^ 64) (hc : 1 ≤ c)
    (hQ : c * (B + e + 4) + 1 ≤ Q) (hD : c * (B + e + 4) + 1 ≤ D)
    (hz1 : x ^ c ≤ z) (hz2 : z ≤ y) (hz64 : z ≤ 1 / 2 ^ 64)
    (hk : k = min (1 / z ^ 2) (1 / x)) (hs : 1 / x ^ Q ≤ s)
    (hf : y ^ B * s ≤ f) (ht : z ^ e * (f / 2 ^ 8) ≤ t) :
    2 ≤ k ∧ k * x ≤ 1 ∧ s / k ^ D ≤ (⌊(z ^ 2) ^ 2 * t⌋₊ : ℝ) := by
  obtain ⟨E', hE'⟩ : ∃ E' : ℕ, E' = B + e + 4 := ⟨_, rfl⟩
  rw [← hE'] at hQ hD
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hz1' : z ≤ 1 := hz64.trans (by norm_num)
  have hxinv := p7_inv_big hx hx64
  have hzinv : (2 : ℝ) ^ 64 ≤ 1 / z ^ 2 := by
    have h1 := p7_inv_big hz0 hz64
    have h2 : 1 / z ≤ 1 / z ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      calc z ^ 2 ≤ z ^ 1 := pow_le_pow_of_le_one hz0.le hz1' (by norm_num)
        _ = z := pow_one z
    linarith
  have hk64 : (2 : ℝ) ^ 64 ≤ k := by rw [hk]; exact le_min hzinv hxinv
  have hk0 : 0 < k := lt_of_lt_of_le (by positivity) hk64
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk64
  have hkx : k * x ≤ 1 := by
    have h1 : k ≤ 1 / x := by rw [hk]; exact min_le_right _ _
    have := mul_le_mul_of_nonneg_right h1 hx.le
    rwa [one_div, inv_mul_cancel₀ hx.ne'] at this
  have hzk : 1 ≤ z * k ^ c := by
    rcases le_total (1 / z ^ 2) (1 / x) with h | h
    · have e1 : k = 1 / z ^ 2 := by rw [hk]; exact min_eq_left h
      rw [e1, one_div_pow, ← pow_mul, mul_one_div, le_div_iff₀ (pow_pos hz0 _), one_mul]
      calc z ^ (2 * c) ≤ z ^ 1 := pow_le_pow_of_le_one hz0.le hz1' (by omega)
        _ = z := pow_one z
    · have e1 : k = 1 / x := by rw [hk]; exact min_eq_right h
      rw [e1, one_div_pow, mul_one_div, le_div_iff₀ (pow_pos hx _), one_mul]
      exact hz1
  have h1 : z ^ B * s ≤ f :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hz2 B) hs0.le).trans hf
  have h2 : z ^ E' * s / 2 ^ 8 ≤ (z ^ 2) ^ 2 * t := by
    have a1 : z ^ e * (z ^ B * s / 2 ^ 8) ≤ z ^ e * (f / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have a2 := mul_le_mul_of_nonneg_left (a1.trans ht) (show (0 : ℝ) ≤ (z ^ 2) ^ 2 by positivity)
    have e2 : (z ^ 2) ^ 2 * (z ^ e * (z ^ B * s / 2 ^ 8)) = z ^ E' * s / 2 ^ 8 := by
      rw [hE']; ring
    linarith
  have hkey : s * 2 ^ 9 ≤ z ^ E' * s * k ^ D := by
    have b0 : 1 ≤ (z * k ^ c) ^ E' := one_le_pow₀ hzk
    have b1 : (z * k ^ c) ^ E' = z ^ E' * k ^ (c * E') := by rw [mul_pow, ← pow_mul]
    rw [b1] at b0
    have b2 : (2 : ℝ) ^ 9 ≤ k := le_trans (by norm_num) hk64
    have b3 : k ^ (c * E' + 1) ≤ k ^ D := pow_le_pow_right₀ hk1 hD
    have b4 : (2 : ℝ) ^ 9 * 1 ≤ k * (z ^ E' * k ^ (c * E')) :=
      mul_le_mul b2 b0 (by norm_num) hk0.le
    have b5 : k * (z ^ E' * k ^ (c * E')) = z ^ E' * k ^ (c * E' + 1) := by ring
    have b6 : z ^ E' * k ^ (c * E' + 1) ≤ z ^ E' * k ^ D :=
      mul_le_mul_of_nonneg_left b3 (pow_nonneg hz0.le _)
    have b7 : (2 : ℝ) ^ 9 ≤ z ^ E' * k ^ D := by linarith
    have := mul_le_mul_of_nonneg_left b7 hs0.le
    linarith [show z ^ E' * s * k ^ D = s * (z ^ E' * k ^ D) by ring]
  have hlow : s / k ^ D ≤ z ^ E' * s / 2 ^ 9 := by
    rw [div_le_div_iff₀ (pow_pos hk0 _) (by positivity)]
    linarith
  have hone : 1 ≤ (z ^ 2) ^ 2 * t := by
    refine le_trans ?_ h2
    have c1 : (x ^ c) ^ E' ≤ z ^ E' := pow_le_pow_left₀ (by positivity) hz1 E'
    have e3 : (x ^ c) ^ E' = x ^ (c * E') := (pow_mul x c E').symm
    rw [e3] at c1
    have c2 : 1 ≤ s * x ^ Q := (div_le_iff₀ (by positivity)).mp hs
    have c3 : x ^ Q ≤ x ^ (c * E' + 1) := pow_le_pow_of_le_one hx.le hx1 hQ
    have c4 : x ≤ 1 / 2 ^ 8 := hx64.trans (by norm_num)
    have c5 : s * x ^ (c * E' + 1) ≤ x ^ (c * E') * s * (1 / 2 ^ 8) := by
      have := mul_le_mul_of_nonneg_left c4 (show (0 : ℝ) ≤ x ^ (c * E') * s by positivity)
      have e4 : x ^ (c * E') * s * x = s * x ^ (c * E' + 1) := by ring
      linarith
    have c6 : x ^ (c * E') * s * (1 / 2 ^ 8) ≤ z ^ E' * s * (1 / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right c1 hs0.le
    have c7 : s * x ^ Q ≤ s * x ^ (c * E' + 1) := mul_le_mul_of_nonneg_left c3 hs0.le
    linarith [show z ^ E' * s * (1 / 2 ^ 8) = z ^ E' * s / 2 ^ 8 by ring]
  have hfl := EHP6.floor_half hone
  refine ⟨le_trans (by norm_num) hk64, hkx, ?_⟩
  have : z ^ E' * s / 2 ^ 9 ≤ (z ^ 2) ^ 2 * t / 2 := by
    have := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 2 by norm_num)
    linarith [show z ^ E' * s / 2 ^ 8 / 2 = z ^ E' * s / 2 ^ 9 by ring]
  linarith

/-- The terminal case: the admissible scale has dropped below `x`. -/
theorem gen_round1_terminal {x y : ℝ} {B c Q D : ℕ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hQ : 2 * c * B + 2 ≤ Q) (hD : 2 * c * B + 2 ≤ D)
    (hy0 : 0 < y) (hy3 : x ^ (2 * c) ≤ y) (hyx : y < x) {S F : Finset V}
    (hS : 1 / x ^ Q ≤ (S.card : ℝ)) (hadm : GAdm G S B y F) : GGoal G S D x := by
  obtain ⟨hFS, hFsp, hFc⟩ := hadm
  obtain ⟨hF4, hwid⟩ := gen_width_terminal (D := D) hx hx64 hy3 hQ hD hS hFc
  have hx14 : x ≤ 1 / 4 := hx64.trans (by norm_num)
  have hFsp' : EHP6.Sparse G (x ^ 3) F := EHP6.sparse_sub hFsp subset_rfl
    (mul_le_mul_of_nonneg_right (by
      have := pow_le_pow_left₀ hy0.le hyx.le 3
      have : 0 ≤ y ^ 3 := by positivity
      linarith) (Nat.cast_nonneg _))
  obtain ⟨β, hβ⟩ := equal_parts_sparse_blockade hx hx14 hFS hFsp' hF4
  have h64 := p7_inv_big hx hx64
  refine ⟨1 / x, by linarith [show (2 : ℝ) ≤ 2 ^ 64 by norm_num], ?_,
    β.mono subset_rfl le_rfl hwid, fun i j hij => EHP6.semisparse_of_sparse β hβ i j hij⟩
  rw [one_div, inv_mul_cancel₀ hx.ne']

/-- One improvement step of the scale potential. -/
theorem gen_round1_improve (s : ℕ) (hs : 1 ≤ s) (hfree : EHP6.Free G (EHP6.pathGraph' s)ᶜ)
    {y₀ : ℝ} {a c d e L B Q D : ℕ} (hy₀ : y₀ ≤ 1 / 2 ^ 64) (hy₀s : y₀ ≤ 1 / (60 * (s : ℝ)))
    (horacle : LocalOracle G y₀ a c d e L) (hc : 1 ≤ c) (hB : 6 * (e + 1) ≤ B)
    (hQ1 : L + B + 1 ≤ Q) (hQ2 : c * (B + e + 4) + 1 ≤ Q)
    (hD1 : B + c * (d + 2) ≤ D) (hD2 : a + 2 + B ≤ D) (hD3 : c * (B + e + 4) + 1 ≤ D)
    {x y : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) (hxy : x ≤ y) (hyy : y ≤ y₀)
    {S F : Finset V} (hS : 1 / x ^ Q ≤ (S.card : ℝ)) (hadm : GAdm G S B y F) :
    GGoal G S D x ∨ ∃ y' : ℝ, ∃ F' : Finset V, x ^ (2 * c) ≤ y' ∧ y' ≤ y / 2 ^ 8 ∧
      GAdm G S B y' F' := by
  obtain ⟨hFS, hFsp, hFc⟩ := hadm
  have hy : y ≤ 1 / 2 ^ 64 := hyy.trans hy₀
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hFbig := gen_order_F hx hx64 hxy hQ1 hS hFc
  have hB1 : 1 ≤ B := by omega
  rcases round1_step_gen hy₀ horacle hx hxy hyy F hFsp hFbig with ⟨T, hTF, hTc, hTsp⟩ |
      ⟨K, hK1, hK2, β, hβ⟩ | ⟨β, hβ⟩ | ⟨z, hz1, hz2, T, hTF, hTs, hTr⟩
  · -- sparser subset: scale y / 2^8
    right
    refine ⟨y / 2 ^ 8, T, ?_, le_rfl, hTF.trans hFS, ?_, ?_⟩
    · have h0 : x ^ (2 * c) ≤ x ^ 2 := pow_le_pow_of_le_one hx.le hx1 (by omega)
      have h1 : x ^ 2 ≤ x * (1 / 2 ^ 8) := by
        have h2 : x ≤ 1 / 2 ^ 8 := hx64.trans (by norm_num)
        have := mul_le_mul_of_nonneg_left h2 hx.le
        linarith [show x * x = x ^ 2 by ring]
      have h3 : x * (1 / 2 ^ 8) ≤ y * (1 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right hxy (by positivity)
      linarith [show y * (1 / 2 ^ 8) = y / 2 ^ 8 by ring]
    · refine EHP6.sparse_sub hTsp subset_rfl (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
      rw [show (y / 2 ^ 8) ^ 3 / 2 ^ 8 = y ^ 3 * (1 / 2 ^ 32) by ring,
        show 2 * y ^ 4 = y ^ 3 * (2 * y) by ring]
      exact mul_le_mul_of_nonneg_left
        (by linarith [show (2 : ℝ) * (1 / 2 ^ 64) ≤ 1 / 2 ^ 32 by norm_num]) (by positivity)
    · have e1 : (y / 2 ^ 8) ^ B * (S.card : ℝ) = y ^ B * S.card * (1 / 2 ^ 8) ^ B := by
        rw [div_pow, one_div_pow]; ring
      rw [e1]
      have h1 : y ^ B * (S.card : ℝ) * (1 / 2 ^ 8) ^ B ≤ y ^ B * S.card * (1 / 2 ^ 8) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hy0.le _) hS0)
        calc ((1 : ℝ) / 2 ^ 8) ^ B ≤ (1 / 2 ^ 8) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) hB1
          _ = 1 / 2 ^ 8 := pow_one _
      have h2 : y ^ B * (S.card : ℝ) * (1 / 2 ^ 8) ≤ F.card * (1 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right hFc (by positivity)
      linarith [show (F.card : ℝ) * (1 / 2 ^ 8) = F.card / 2 ^ 8 by ring]
  · -- blockade from the oracle
    left
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = min (K : ℝ) (1 / x) := ⟨_, rfl⟩
    have hK64 : (2 : ℝ) ^ 64 ≤ K := EHP6.cl_ell64 hy0 hy hK1
    have hk64 : (2 : ℝ) ^ 64 ≤ k := by rw [hk]; exact le_min hK64 (p7_inv_big hx hx64)
    refine ⟨k, le_trans (by norm_num) hk64, ?_, β.mono hFS (by rw [hk]; exact min_le_left _ _)
      (gen_width_block hx hxy hy1 hc hD1 hK1 hK2 hk hFc hS0), fun i j hij => hβ i j hij⟩
    have h1 : k ≤ 1 / x := by rw [hk]; exact min_le_right _ _
    have := mul_le_mul_of_nonneg_right h1 hx.le
    rwa [one_div, inv_mul_cancel₀ hx.ne'] at this
  · -- sparse chain
    left
    have h64 := p7_inv_big hy0 hy
    refine ⟨1 / y, le_trans (by norm_num) h64, ?_, β.mono hFS le_rfl
      (gen_width_chain hy0 hy1 hS0 hD2 hFc), fun i j hij => EHP6.semisparse_of_sparse β hβ i j hij⟩
    rw [one_div, inv_mul_le_iff₀ hy0]
    linarith
  · -- restricted set at its actual scale z
    have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
    have hz64 : z ≤ 1 / 2 ^ 64 := hz2.trans hy
    rcases hTr with hsp | hspc
    · right
      obtain ⟨w, hw0, hw6, hw8⟩ := p7_sixth_root hz0 hz64
      obtain ⟨c1, c2, c3, c4⟩ := gen_sparse_scale hx hx1 hB hw0 hw6 hw8 hz1 hz2 hz64 hS0 hFc hTs
      exact ⟨w ^ 7, T, c1, c2, hTF.trans hFS,
        EHP6.sparse_sub hsp subset_rfl (mul_le_mul_of_nonneg_right c3 (Nat.cast_nonneg _)), c4⟩
    · left
      obtain ⟨k, hk⟩ : ∃ k : ℝ, k = min (1 / z ^ 2) (1 / x) := ⟨_, rfl⟩
      obtain ⟨hk2, hkx, hwid⟩ := gen_width_compl hx hx64 hc hQ2 hD3 hz1 hz2 hz64 hk hS hFc hTs
      have hnot := compl_not_contains_path s hfree T
      have hzs : z ^ 2 ≤ 1 / (60 * (s : ℝ)) := by
        have h1 : z ^ 2 ≤ z ^ 1 :=
          pow_le_pow_of_le_one hz0.le (hz64.trans (by norm_num)) (by norm_num)
        rw [pow_one] at h1
        exact h1.trans (hz2.trans (hyy.trans hy₀s))
      have hspc' : EHP6.Sparse Gᶜ ((z ^ 2) ^ 2) T := by
        rw [show (z ^ 2) ^ 2 = z ^ 4 by ring]
        exact hspc
      obtain ⟨β, hβ⟩ := EHP6.nss_path s hs (z ^ 2) (by positivity) hzs Gᶜ T hspc' hnot
      refine ⟨k, hk2, hkx, β.mono (hTF.trans hFS) (by rw [hk]; exact min_le_left _ _) hwid,
        fun i j hij => Or.inl ?_⟩
      intro a ha b hb
      have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
      by_contra hn
      exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj G a b).2 ⟨hab, hn⟩)

/-- Round one: a `y₀^3/2^8`-sparse set of order at least `x^(-Q)` has an
    `x`-semisparse blockade of real length `k ∈ [2, 1/x]` and width `|S|/k^D`. -/
theorem round1_gen (s : ℕ) (hs : 1 ≤ s) (hfree : EHP6.Free G (EHP6.pathGraph' s)ᶜ)
    {y₀ : ℝ} {a c d e L B Q D : ℕ} (hy₀ : y₀ ≤ 1 / 2 ^ 64) (hy₀s : y₀ ≤ 1 / (60 * (s : ℝ)))
    (horacle : LocalOracle G y₀ a c d e L) (hc : 1 ≤ c) (hB : 6 * (e + 1) ≤ B)
    (hQ1 : L + B + 1 ≤ Q) (hQ2 : c * (B + e + 4) + 1 ≤ Q) (hQ3 : 2 * c * B + 2 ≤ Q)
    (hD1 : B + c * (d + 2) ≤ D) (hD2 : a + 2 + B ≤ D) (hD3 : c * (B + e + 4) + 1 ≤ D)
    (hD4 : 2 * c * B + 2 ≤ D)
    {x : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) (hxy₀ : x ≤ y₀) (S : Finset V)
    (hsp : EHP6.Sparse G (y₀ ^ 3 / 2 ^ 8) S)
    (hS : 1 / x ^ Q ≤ (S.card : ℝ)) : GGoal G S D x := by
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hxc : 0 < x ^ (2 * c) := by positivity
  have key : ∀ n : ℕ, ∀ (y : ℝ) (F : Finset V), x ^ (2 * c) ≤ y → y ≤ y₀ →
      y ≤ x * (2 ^ 8) ^ n → GAdm G S B y F → GGoal G S D x := by
    intro n
    induction n with
    | zero =>
      intro y F h3 hy hyn hadm
      have hy0 : 0 < y := hxc.trans_le h3
      by_cases hyx : y < x
      · exact gen_round1_terminal hx hx64 hQ3 hD4 hy0 h3 hyx hS hadm
      · push Not at hyx
        rcases gen_round1_improve s hs hfree hy₀ hy₀s horacle hc hB hQ1 hQ2 hD1 hD2 hD3
          hx hx64 hyx hy hS hadm with h | ⟨y', F', h3', hy', hadm'⟩
        · exact h
        · have hy'0 : 0 < y' := hxc.trans_le h3'
          have hy'x : y' < x := by
            have : y ≤ x := by simpa using hyn
            have h2 : y / 2 ^ 8 ≤ x / 2 ^ 8 := div_le_div_of_nonneg_right this (by positivity)
            have h4 : x / 2 ^ 8 < x := by
              rw [div_lt_iff₀ (by positivity)]
              nlinarith
            linarith
          exact gen_round1_terminal hx hx64 hQ3 hD4 hy'0 h3' hy'x hS hadm'
    | succ n ih =>
      intro y F h3 hy hyn hadm
      have hy0 : 0 < y := hxc.trans_le h3
      by_cases hyx : y < x
      · exact gen_round1_terminal hx hx64 hQ3 hD4 hy0 h3 hyx hS hadm
      · push Not at hyx
        rcases gen_round1_improve s hs hfree hy₀ hy₀s horacle hc hB hQ1 hQ2 hD1 hD2 hD3
          hx hx64 hyx hy hS hadm with h | ⟨y', F', h3', hy', hadm'⟩
        · exact h
        · have hy'le : y' ≤ y := by
            have : y / 2 ^ 8 ≤ y := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith
            linarith
          refine ih y' F' h3' (hy'le.trans hy) ?_ hadm'
          have h2 : y / 2 ^ 8 ≤ x * (2 ^ 8) ^ (n + 1) / 2 ^ 8 :=
            div_le_div_of_nonneg_right hyn (by positivity)
          have e : x * (2 ^ 8) ^ (n + 1) / 2 ^ 8 = x * (2 ^ 8) ^ n := by
            rw [pow_succ]
            field_simp
          rw [e] at h2
          exact hy'.trans h2
  have hy₀pos : 0 < y₀ := hx.trans_le hxy₀
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (y₀ / x) (by norm_num : (1 : ℝ) < 2 ^ 8)
  have hN' : y₀ ≤ x * (2 ^ 8) ^ N := by
    have := (div_lt_iff₀ hx).mp hN
    linarith
  refine key N y₀ S ?_ le_rfl hN' ⟨subset_rfl, hsp, ?_⟩
  · have : x ^ (2 * c) ≤ x ^ 1 := pow_le_pow_of_le_one hx.le hx1 (by omega)
    rw [pow_one] at this
    linarith
  · exact mul_le_of_le_one_left (Nat.cast_nonneg _)
      (pow_le_one₀ hy₀pos.le (hy₀.trans (by norm_num)))

theorem gen_r3_F {x δ s f : ℝ} {Lδ Q d' : ℕ} (hx : 0 < x) (hxL : x ≤ 1 / 2 ^ d')
    (hLd : Lδ ≤ d') (hQd : Q + 1 ≤ d')
    (hδ0 : 0 < δ) (hδL : 1 ≤ δ * 2 ^ Lδ) (hs : 1 / x ^ d' ≤ s) (hf : δ * s ≤ f) :
    1 / x ^ Q ≤ f := by
  have hx1 : x ≤ 1 := hxL.trans (by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num))
  have hxL' : x * 2 ^ Lδ ≤ 1 := by
    have h1 : x * 2 ^ d' ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hxL (show (0 : ℝ) ≤ 2 ^ d' by positivity)
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    have h2 : x * 2 ^ Lδ ≤ x * 2 ^ d' :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hLd) hx.le
    linarith
  have hδx : x ≤ δ := by
    have h1 : x * 2 ^ Lδ ≤ δ * 2 ^ Lδ := hxL'.trans hδL
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have h1 : 1 ≤ s * x ^ d' := (div_le_iff₀ (by positivity)).mp hs
  rw [div_le_iff₀ (by positivity)]
  have h2 : x ^ d' ≤ x ^ (Q + 1) := pow_le_pow_of_le_one hx.le hx1 hQd
  have h3 : s * x ^ d' ≤ s * x ^ (Q + 1) := mul_le_mul_of_nonneg_left h2 hs0.le
  have h4 : s * x ^ (Q + 1) = (x * s) * x ^ Q := by ring
  have h5 : (x * s) * x ^ Q ≤ (δ * s) * x ^ Q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδx hs0.le) (by positivity)
  have h6 : (δ * s) * x ^ Q ≤ f * x ^ Q :=
    mul_le_mul_of_nonneg_right hf (by positivity)
  linarith

theorem gen_r3_w {s f δ k : ℝ} {Lδ D d' : ℕ} (hk : 2 ≤ k) (hLD : Lδ + D ≤ d')
    (hδL : 1 ≤ δ * 2 ^ Lδ) (hδ0 : 0 < δ)
    (hf : δ * s ≤ f) (hs : 0 ≤ s) : s / k ^ d' ≤ f / k ^ D := by
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hf0 : 0 ≤ f := le_trans (mul_nonneg hδ0.le hs) hf
  rw [div_le_div_iff₀ (pow_pos hk0 _) (pow_pos hk0 _)]
  have h0 : f * k ^ (Lδ + D) ≤ f * k ^ d' :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk1 hLD) hf0
  have e : f * k ^ (Lδ + D) = (f * k ^ Lδ) * k ^ D := by rw [pow_add]; ring
  have hkL : (2 : ℝ) ^ Lδ ≤ k ^ Lδ := pow_le_pow_left₀ (by norm_num) hk Lδ
  have h1 : δ * s * 2 ^ Lδ ≤ f * k ^ Lδ :=
    mul_le_mul hf hkL (by positivity) hf0
  have h2 : s * 1 ≤ s * (δ * 2 ^ Lδ) := mul_le_mul_of_nonneg_left hδL hs
  have h3 : s * k ^ D ≤ (f * k ^ Lδ) * k ^ D := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hk0.le _)
    linarith [show s * (δ * 2 ^ Lδ) = δ * s * 2 ^ Lδ by ring]
  linarith

theorem gen_r3_c {s f δ η : ℝ} {Lδ n₁ d' : ℕ} (hη : 0 < η) (hηn : 2 ≤ η ^ 2 * 2 ^ n₁)
    (hLn : Lδ + n₁ ≤ d') (hδL : 1 ≤ δ * 2 ^ Lδ) (hδ0 : 0 < δ)
    (hsA : (2 : ℝ) ^ d' ≤ s) (hf : δ * s ≤ f) :
    s / 2 ^ d' ≤ (⌊η ^ 2 * f⌋₊ : ℝ) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hsA
  have hfs : s ≤ f * 2 ^ Lδ := by
    have h1 : s * 1 ≤ s * (δ * 2 ^ Lδ) := mul_le_mul_of_nonneg_left hδL hs0
    have h2 : δ * s * 2 ^ Lδ ≤ f * 2 ^ Lδ := mul_le_mul_of_nonneg_right hf (by positivity)
    linarith [show s * (δ * 2 ^ Lδ) = δ * s * 2 ^ Lδ by ring]
  have hpow : (2 : ℝ) ^ (Lδ + n₁) ≤ 2 ^ d' := pow_le_pow_right₀ (by norm_num) hLn
  have hf0 : 0 ≤ f := le_trans (mul_nonneg hδ0.le hs0) hf
  -- 2^(Lδ+n₁) ≤ s ≤ f * 2^Lδ, so 2^n₁ ≤ f
  have hfn : (2 : ℝ) ^ n₁ ≤ f := by
    have h1 : (2 : ℝ) ^ n₁ * 2 ^ Lδ ≤ f * 2 ^ Lδ := by
      have e : (2 : ℝ) ^ n₁ * 2 ^ Lδ = 2 ^ (Lδ + n₁) := by rw [pow_add]; ring
      linarith
    exact le_of_mul_le_mul_right h1 (by positivity)
  have h1 : 1 ≤ η ^ 2 * f := by
    have : η ^ 2 * 2 ^ n₁ ≤ η ^ 2 * f := mul_le_mul_of_nonneg_left hfn (by positivity)
    linarith
  have h2 := EHP6.floor_half h1
  have h4 : s / 2 ^ d' ≤ η ^ 2 * f / 2 := by
    rw [div_le_iff₀ (by positivity)]
    -- s ≤ f 2^Lδ ; 2 f 2^Lδ ≤ η² f 2^(Lδ+n₁) ≤ η² f 2^d'
    have a1 : f * 2 ^ Lδ * 2 ≤ f * 2 ^ Lδ * (η ^ 2 * 2 ^ n₁) :=
      mul_le_mul_of_nonneg_left hηn (by positivity)
    have a2 : η ^ 2 * f * 2 ^ (Lδ + n₁) ≤ η ^ 2 * f * 2 ^ d' :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have e : f * 2 ^ Lδ * (η ^ 2 * 2 ^ n₁) = η ^ 2 * f * 2 ^ (Lδ + n₁) := by
      rw [pow_add]; ring
    nlinarith
  linarith

/-- Round-one blockade for a class (Lemma 4.3 of the P6 project), from a local
    oracle and a fixed Rödl start. -/
theorem round1_blockade_cls (s : ℕ) (hs : 1 ≤ s) (Cls : ∀ (W : Type), SimpleGraph W → Prop)
    (hCls : ∀ (W : Type) (H : SimpleGraph W), Cls W H → CoPathFree s H)
    (hR : RodlCo s) {y₁ : ℝ} (hy₁ : 0 < y₁) {a c d e L : ℕ} (hc : 1 ≤ c)
    (horacle : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], Cls W H → LocalOracle H y₁ a c d e L) :
    ∃ d' : ℕ, 200 ≤ d' ∧ ∀ x : ℝ, 0 < x → x < 1 / 2 ^ d' →
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Cls W H → ∀ S : Finset W, 1 / x ^ d' ≤ (S.card : ℝ) →
        ∃ k : ℝ, 2 ≤ k ∧ k * x ≤ 1 ∧
          ∃ β : EHP6.Blockade S k (S.card / k ^ d'), β.IsSemisparse H x := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / (60 * (s : ℝ)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hη60 : η ≤ 1 / 60 := by
    rw [hηdef]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have h2η : (2 : ℝ) ≤ 1 / η := by
    rw [le_div_iff₀ hηpos]; linarith
  obtain ⟨y₀, hy₀def⟩ : ∃ y₀ : ℝ, y₀ = min y₁ (min (1 / 2 ^ 64) η) := ⟨_, rfl⟩
  have hy₀pos : 0 < y₀ := by
    rw [hy₀def]; exact lt_min hy₁ (lt_min (by norm_num) hηpos)
  have hy₀1 : y₀ ≤ y₁ := by rw [hy₀def]; exact min_le_left _ _
  have hy₀64 : y₀ ≤ 1 / 2 ^ 64 := by
    rw [hy₀def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hy₀η : y₀ ≤ 1 / (60 * (s : ℝ)) := by
    rw [hy₀def, ← hηdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (y₀ ^ 3 / 2 ^ 8) (η ^ 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min (by positivity) (by positivity)
  have hε₁a : ε₁ ≤ y₀ ^ 3 / 2 ^ 8 := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : ε₁ ≤ η ^ 2 := by rw [hε₁def]; exact min_le_right _ _
  have hε₁half : ε₁ < 1 / 2 := by
    have : η ^ 2 ≤ (1 / 60) ^ 2 := pow_le_pow_left₀ hηpos.le hη60 2
    linarith [show ((1 : ℝ) / 60) ^ 2 < 1 / 2 by norm_num]
  obtain ⟨δ, hδ0, hRδ⟩ := hR ε₁ hε₁pos hε₁half
  obtain ⟨Lδ, hLδ⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have hδL : 1 ≤ δ * 2 ^ Lδ := by rw [div_lt_iff₀ hδ0] at hLδ; linarith
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt (2 / η ^ 2) (by norm_num : (1 : ℝ) < 2)
  have hηn : 2 ≤ η ^ 2 * 2 ^ n₁ := by
    rw [div_lt_iff₀ (by positivity)] at hn₁; linarith
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hy₀pos (by norm_num : (1 : ℝ) / 2 < 1)
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 6 * (e + 1) := ⟨_, rfl⟩
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℕ, P₁ = c * (B + e + 4) := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P₂ : ℕ, P₂ = 2 * c * B := ⟨_, rfl⟩
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : ℕ, P₃ = c * (d + 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = L + B + P₁ + P₂ + 2 := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = B + P₃ + a + P₁ + P₂ + 2 := ⟨_, rfl⟩
  obtain ⟨d', hd'def⟩ : ∃ d' : ℕ, d' = Lδ + n₁ + n₀ + Q + D + 200 := ⟨_, rfl⟩
  refine ⟨d', by omega, fun x hx hxd W _ _ H _ hcls S hS => ?_⟩
  have hfree : EHP6.Free H (EHP6.pathGraph' s)ᶜ := free_of_coPathFree s H (hCls W H hcls)
  obtain ⟨F, hFS, hFc, hFr⟩ := hRδ W H hfree S
  obtain ⟨hA, hxA⟩ := EHP6.r3_x (d := d') (by omega) hx hxd
  have hsA : (2 : ℝ) ^ d' ≤ S.card := hA.trans (hxA.trans hS)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx2 : 2 * x ≤ 1 := by
    have : (2 : ℝ) ≤ 2 ^ d' := le_self_pow₀ (by norm_num) (by omega)
    have h := (le_div_iff₀ hx).1 (this.trans hA)
    linarith
  rcases hFr with hsp | hspc
  · have hsp' : EHP6.Sparse H (y₀ ^ 3 / 2 ^ 8) F :=
      EHP6.sparse_sub hsp subset_rfl (mul_le_mul_of_nonneg_right hε₁a (Nat.cast_nonneg _))
    have hx64 : x ≤ 1 / 2 ^ 64 := by
      refine hxd.le.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hxy₀ : x ≤ y₀ := by
      have h1 : x ≤ 1 / 2 ^ n₀ := by
        refine hxd.le.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [← one_div_pow] at h1
      linarith
    have hFbig := gen_r3_F (Q := Q) hx hxd.le (by omega) (by omega) hδ0 hδL hS hFc
    obtain ⟨k, hk2, hkx, β, hβ⟩ := round1_gen s hs hfree (B := B) (Q := Q) (D := D) hy₀64 hy₀η
      (localOracle_mono (horacle W H hcls) hy₀1) hc (by omega)
      (by omega) (by rw [← hP₁]; omega) (by rw [← hP₂]; omega)
      (by rw [← hP₃]; omega) (by omega) (by rw [← hP₁]; omega) (by rw [← hP₂]; omega)
      hx hx64 hxy₀ F hsp' hFbig
    exact ⟨k, hk2, hkx, β.mono hFS le_rfl (gen_r3_w hk2 (by omega) hδL hδ0 hFc hS0),
      fun i j hij => hβ i j hij⟩
  · have hnot := compl_not_contains_path s hfree F
    have hspc' : EHP6.Sparse Hᶜ (η ^ 2) F :=
      EHP6.sparse_sub hspc subset_rfl
        (mul_le_mul_of_nonneg_right hε₁b (Nat.cast_nonneg _))
    obtain ⟨β, hβ⟩ := EHP6.nss_path s hs η hηpos (le_of_eq hηdef) Hᶜ F hspc' hnot
    have hw := gen_r3_c hηpos hηn (show Lδ + n₁ ≤ d' by omega) hδL hδ0 hsA hFc
    refine ⟨2, le_rfl, hx2, β.mono hFS h2η hw, fun i j hij => Or.inl ?_⟩
    intro a ha b hb
    have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    by_contra hn
    exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj H a b).2 ⟨hab, hn⟩)

/-- **Generalized niceness from a local oracle.** -/
theorem nice_of_oracle (s : ℕ) (hs : 1 ≤ s) (Cls : ∀ (W : Type), SimpleGraph W → Prop)
    (hCls : ∀ (W : Type) (H : SimpleGraph W), Cls W H → CoPathFree s H)
    (hR : RodlCo s) {y₁ : ℝ} (hy₁ : 0 < y₁) {a c d e L : ℕ} (hc : 1 ≤ c)
    (horacle : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], Cls W H → LocalOracle H y₁ a c d e L) :
    ∃ d' : ℕ, 200 ≤ d' ∧ NiceCls Cls d' := by
  obtain ⟨d', hd, h43⟩ := round1_blockade_cls s hs Cls hCls hR hy₁ hc horacle
  refine ⟨d', hd, fun ε hε0 hε1 W _ _ H _ hcls S hS => ?_⟩
  have hε1' : ε < 1 := by linarith
  have hx : ε ^ (5 * d') < 1 / 2 ^ d' := by
    have h1 : ε ^ (5 * d') ≤ ε ^ d' := pow_le_pow_of_le_one hε0.le hε1'.le (by omega)
    have h2 : ε ^ d' < (1 / 2) ^ d' := pow_lt_pow_left₀ hε1 hε0.le (by omega)
    rw [one_div_pow] at h2
    linarith
  obtain ⟨β, hβ⟩ := EHP6.layout_theorem (G := H) hε0 hε1' (by omega) S (fun F hF hFc =>
    h43 (ε ^ (5 * d')) (by positivity) hx W H hcls F (EHP6.nice_size hε0 hε1'.le hS hFc))
  have e : (ε ^ (5 * d')) ^ (2 * d') = ε ^ (10 * d' ^ 2) := by rw [← pow_mul]; congr 1; ring
  exact ⟨β.mono subset_rfl le_rfl (by rw [e]), fun i j hij => hβ i j hij⟩

#print axioms round1_step_gen
#print axioms round1_gen
#print axioms round1_blockade_cls
#print axioms nice_of_oracle
end AllPathsLocal
