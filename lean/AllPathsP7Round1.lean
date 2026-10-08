import AllPathsP7Comb

/-!
Round one for complement-P7-free graphs (the P7 analogue of `EHP6/Round1.lean`,
i.e. the variable-scale bootstrap of the main paper at `s = 7`). The restricted
outcome of the RP5 Tooth has a floating scale `z`; the scale potential below keeps
that actual `z`. Nothing here asserts EH(P7).
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem p7_r1_width {s b K : ℝ} (hK : 16 ≤ K) (hb : s / 2 ^ 8 ≤ b) (hs : 0 ≤ s) :
    s / K ^ 72 ≤ b / K ^ 70 := by
  have hK0 : 0 < K := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hK2 : 256 ≤ K ^ 2 := by nlinarith
  have e : b * K ^ 72 = (b * K ^ 2) * K ^ 70 := by ring
  rw [e]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hb0 : s ≤ 2 ^ 8 * b := by linarith [show s / 2 ^ 8 * 2 ^ 8 = s by ring]
  have hbs : 0 ≤ b := by linarith
  nlinarith

/-- One step of round one for P7. Besides the three outcomes of the P6 step there is
    the restricted outcome with its ACTUAL scale `z ∈ [x^2, y]`. -/
theorem round1_step_p7 (hcomb : EHP6.NssComb) (hfree : EHP6.Free G P7ᶜ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (S : Finset V)
    (hsp : EHP6.Sparse G (y ^ 3 / 2 ^ 8) S)
    (hS : 2 ^ 8 / x ^ 1208 ≤ (S.card : ℝ)) :
    (∃ T ⊆ S, (S.card : ℝ) / 2 ^ 8 ≤ T.card ∧ EHP6.Sparse G (2 * y ^ 4) T) ∨
    OracleBlockade G S x y 280 72 ∨
    (∃ β : EHP6.Blockade S (1 / y) (y ^ 6 * S.card), β.IsSparse G x) ∨
    (∃ z : ℝ, x ^ 2 ≤ z ∧ z ≤ y ∧ ∃ T ⊆ S, z ^ 24 * ((S.card : ℝ) / 2 ^ 8) ≤ T.card ∧
      EHP6.Restricted G (z ^ 4) T) := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS
  have hw : 0 < y ^ 6 * S.card := by positivity
  have hy5 : 4 * y ≤ 1 / 5 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 20 by norm_num]
  have hq : 0 ≤ 1 - 4 * y := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest
      (EHP6.SChain G S x (y ^ 6 * S.card) (1 - 4 * y)) S.card := ⟨_, rfl⟩
  have hPn : EHP6.SChain G S x (y ^ 6 * S.card) (1 - 4 * y) n := by
    rw [hn]; exact Nat.findGreatest_spec (Nat.zero_le _) (EHP6.schain_zero S _ _ _)
  have hmax : ¬ EHP6.SChain G S x (y ^ 6 * S.card) (1 - 4 * y) (n + 1) := fun h => by
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
  have hBbig : 1 / x ^ 1208 ≤ ((B n).card : ℝ) := by
    have e : (1 : ℝ) / x ^ 1208 = 2 ^ 8 / x ^ 1208 / 2 ^ 8 := by ring
    rw [e]
    have := div_le_div_of_nonneg_right hS (by norm_num : (0 : ℝ) ≤ 2 ^ 8)
    linarith
  rcases comb_oracle_p7 hcomb hfree hx hxy hy (B n) hsp' hBbig with h |
      ⟨X, hX, Y, hY, hXY, hXs, hYs, hYX⟩ | ⟨K, hK1, hK2, β, hβ⟩ | ⟨z, hz1, hz2, T, hT, hTs, hTr⟩
  · exact Or.inl ⟨B n, hBnS, hBn, h⟩
  · exfalso
    refine hmax (EHP6.schain_extend hq hsub hdisj hspB hwid hlast hX hY hXY ?_ hYs hYX)
    have hy2 : y ^ 2 ≤ 1 / 2 ^ 8 := by
      have : y ^ 2 ≤ (1 / 2 ^ 64) ^ 2 := pow_le_pow_left₀ hy0.le hy 2
      linarith [show ((1 : ℝ) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 8 by norm_num]
    have h1 := mul_le_mul_of_nonneg_left hBn (by positivity : (0 : ℝ) ≤ y ^ 4)
    have h2 : y ^ 6 * S.card ≤ y ^ 4 * ((S.card : ℝ) / 2 ^ 8) := by
      have := mul_le_mul_of_nonneg_left hy2 (by positivity : (0 : ℝ) ≤ y ^ 4 * S.card)
      linarith [show y ^ 4 * S.card * y ^ 2 = y ^ 6 * S.card by ring,
        show y ^ 4 * S.card * (1 / 2 ^ 8) = y ^ 4 * ((S.card : ℝ) / 2 ^ 8) by ring]
    linarith
  · have hK16 : (16 : ℝ) ≤ K := by
      have h1 : (2 : ℝ) ^ 64 ≤ K := EHP6.cl_ell64 hy0 hy hK1
      linarith [show (16 : ℝ) ≤ 2 ^ 64 by norm_num]
    right; left
    exact ⟨K, hK1, hK2, β.mono hBnS le_rfl (p7_r1_width hK16 hBn hSpos.le),
      fun i j hij => hβ i j hij⟩
  · right; right; right
    refine ⟨z, hz1, hz2, T, hT.trans hBnS, le_trans ?_ hTs, hTr⟩
    have hz0 : 0 ≤ z := le_trans (by positivity) hz1
    exact mul_le_mul_of_nonneg_left hBn (by positivity)

/-- NSS V, statement 3.1, for the seven-vertex path (`k = 7`, so `y ≤ 1/(60*7)`).
    A cited statement, displayed as a proposition exactly like `EHP6.NssPath6`. -/
def NssPath7 : Prop := ∀ y : ℝ, 0 < y → y ≤ 1 / 420 →
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V), EHP6.Sparse G (y ^ 2) S → ¬ EHP6.ContainsInduced G P7 S →
      ∃ β : EHP6.Blockade S (1 / y) (⌊y ^ 2 * S.card⌋₊ : ℝ), β.IsAnticomplete G

/-- Rödl's theorem for the complement of P7, displayed as a proposition exactly
    like `EHP6.RodlCoP6`. -/
def RodlCoP7 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ δ : ℝ, 0 < δ ∧
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    EHP6.Free G P7ᶜ → ∀ S : Finset V, ∃ F ⊆ S, δ * S.card ≤ F.card ∧ EHP6.Restricted G ε F

/-- an induced P7 in the complement is an induced complement-P7 in `G` -/
theorem compl_not_contains_p7 (hfree : EHP6.Free G P7ᶜ) (F : Finset V) :
    ¬ EHP6.ContainsInduced Gᶜ P7 F := by
  rintro ⟨f, hinj, -, hadj⟩
  apply hfree
  refine ⟨f, hinj, fun i => mem_univ _, fun i j => ?_⟩
  have h := hadj i j
  rw [SimpleGraph.compl_adj] at h ⊢
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    exact G.irrefl
  · have hf : f i ≠ f j := fun e => hij (hinj e)
    constructor
    · intro hG; exact ⟨hij, fun hp => (h.2 hp).2 hG⟩
    · rintro ⟨-, hnp⟩; by_contra hG; exact hnp (h.1 ⟨hf, hG⟩)

/-- A set that is `x^3`-sparse and has at least `4/x` vertices splits into an
    `x`-sparse blockade of length at least `1/x` and width `x|F|/4`. -/
theorem equal_parts_sparse_blockade {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1 / 4)
    {F S : Finset V} (hFS : F ⊆ S) (hFsp : EHP6.Sparse G (x ^ 3) F)
    (hF4 : 4 / x ≤ (F.card : ℝ)) :
    ∃ β : EHP6.Blockade S (1 / x) (x * F.card / 4), β.IsSparse G x := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈1 / x⌉₊ := ⟨_, rfl⟩
  have hm1 : 1 / x ≤ m := by rw [hm]; exact Nat.le_ceil _
  have hxinv : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hm2 : (m : ℝ) ≤ 2 / x := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / x)
    rw [← hm] at this
    linarith [show 2 / x = 1 / x + 1 / x by ring]
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by norm_num) (hxinv.trans hm1)
  have hz : x * F.card / 2 ≤ (F.card : ℝ) / m := by
    rw [le_div_iff₀ hmpos]
    have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ x * F.card / 2)
    have e : x * F.card / 2 * (2 / x) = F.card := by field_simp
    linarith
  have hz1 : 1 ≤ (F.card : ℝ) / m := by
    have : 2 ≤ x * F.card / 2 := by
      have := mul_le_mul_of_nonneg_left hF4 hx.le
      rw [show x * (4 / x) = 4 by field_simp] at this
      linarith
    linarith
  obtain ⟨sz, hsz⟩ : ∃ sz : ℕ, sz = ⌊(F.card : ℝ) / m⌋₊ := ⟨_, rfl⟩
  have hsz1 : x * F.card / 4 ≤ sz := by
    have := EHP6.floor_half hz1
    rw [← hsz] at this
    linarith
  have hsz2 : m * sz ≤ F.card := by
    have h1 : (sz : ℝ) ≤ F.card / m := by rw [hsz]; exact Nat.floor_le (by positivity)
    have h2 : (m : ℝ) * sz ≤ F.card := by
      have := mul_le_mul_of_nonneg_left h1 hmpos.le
      rwa [mul_div_cancel₀ _ hmpos.ne'] at this
    exact_mod_cast h2
  obtain ⟨P, hP1, hP2, hP3⟩ := EHP6.exists_equal_parts sz m F hsz2
  refine ⟨⟨m, P, hm1, fun i => (hP1 i).trans hFS, fun i => ?_, hP3⟩, fun i j hij => ?_⟩
  · rw [hP2 i]; exact hsz1
  · intro v hv
    have h1 : (EHP6.nbrs G v (P i)).card ≤ (EHP6.nbrs G v F).card :=
      card_le_card (filter_subset_filter _ (hP1 i))
    have h1' : ((EHP6.nbrs G v (P i)).card : ℝ) ≤ (EHP6.nbrs G v F).card := by exact_mod_cast h1
    have h2 := hFsp v (hP1 j hv)
    have h3 : x ^ 3 * F.card ≤ x * (x * F.card / 4) := by
      have := mul_le_mul_of_nonneg_right hx1 (by positivity : (0 : ℝ) ≤ x ^ 2 * F.card)
      linarith [show x * (x ^ 2 * (F.card : ℝ)) = x ^ 3 * F.card by ring,
        show 1 / 4 * (x ^ 2 * (F.card : ℝ)) = x * (x * F.card / 4) by ring]
    have h4 : x * (x * F.card / 4) ≤ x * (P i).card := by
      rw [hP2 i]; exact mul_le_mul_of_nonneg_left hsz1 hx.le
    linarith

/-- Admissible pair of the round-one scale potential for P7: `F` is
    `y^3/2^8`-sparse and has at least `y^150 |S|` vertices. -/
def P7Adm (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (y : ℝ) (F : Finset V) : Prop :=
  F ⊆ S ∧ EHP6.Sparse G (y ^ 3 / 2 ^ 8) F ∧ y ^ 150 * (S.card : ℝ) ≤ F.card

/-- The target of round one: an `x`-semisparse blockade of real length
    `k ∈ [2, 1/x]` and width `|S|/k^20310`. -/
def P7Goal (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : ℝ) : Prop :=
  ∃ k : ℝ, 2 ≤ k ∧ k * x ≤ 1 ∧
    ∃ β : EHP6.Blockade S k (S.card / k ^ 20310), β.IsSemisparse G x

theorem p7_inv_big {x : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) : (2 : ℝ) ^ 64 ≤ 1 / x := by
  rw [le_div_iff₀ hx]
  have := mul_le_mul_of_nonneg_left hx64 (show (0 : ℝ) ≤ 2 ^ 64 by positivity)
  norm_num at this ⊢
  linarith

theorem p7_order_F {x y s f : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) (hxy : x ≤ y)
    (hs : 1 / x ^ 1359 ≤ s) (hf : y ^ 150 * s ≤ f) : 2 ^ 8 / x ^ 1208 ≤ f := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have h1 : 1 ≤ s * x ^ 1359 := (div_le_iff₀ (by positivity)).mp hs
  have h2 : x ^ 150 * s ≤ f :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le hxy 150) hs0.le).trans hf
  rw [div_le_iff₀ (by positivity)]
  have h3 : (2 : ℝ) ^ 8 * x ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hx64 (show (0 : ℝ) ≤ 2 ^ 8 by positivity)
    norm_num at this ⊢
    linarith
  have h4 : s * x ^ 1359 ≤ f * x ^ 1208 * x := by
    have := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ x ^ 1209 by positivity)
    have e1 : x ^ 150 * s * x ^ 1209 = s * x ^ 1359 := by ring
    have e2 : f * x ^ 1209 = f * x ^ 1208 * x := by ring
    linarith
  have h5 : (2 : ℝ) ^ 8 * x ≤ f * x ^ 1208 * x := by linarith
  exact le_of_mul_le_mul_right h5 hx

theorem p7_width_block {x y s f K k : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy1 : y ≤ 1)
    (hK1 : 1 / y ≤ K) (hK2 : K ≤ 1 / x ^ 280) (hk : k = min K (1 / x))
    (hf : y ^ 150 * s ≤ f) (hs : 0 ≤ s) : s / k ^ 20310 ≤ f / K ^ 72 := by
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
  have hKk : K ≤ k ^ 280 := by
    rcases le_total K (1 / x) with h | h
    · have e : k = K := by rw [hk]; exact min_eq_left h
      rw [e]
      have hK1' : 1 ≤ K := by rw [← e]; exact hk1
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 280 := pow_le_pow_right₀ hK1' (by norm_num)
    · have e : k = 1 / x := by rw [hk]; exact min_eq_right h
      rw [e, one_div_pow]
      exact hK2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : s * K ^ 72 ≤ s * (k ^ 280) ^ 72 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0.le hKk 72) hs
  have h2 : (y * k) ^ 150 * (s * k ^ 20160) ≤ f * k ^ 20310 := by
    have := mul_le_mul_of_nonneg_right hf (show (0 : ℝ) ≤ k ^ 20310 by positivity)
    have e : y ^ 150 * s * k ^ 20310 = (y * k) ^ 150 * (s * k ^ 20160) := by ring
    linarith
  have h3 : 1 * (s * k ^ 20160) ≤ (y * k) ^ 150 * (s * k ^ 20160) :=
    mul_le_mul_of_nonneg_right (one_le_pow₀ hyk1) (mul_nonneg hs (pow_nonneg hk0.le _))
  have e2 : s * (k ^ 280) ^ 72 = s * k ^ 20160 := by rw [← pow_mul]
  linarith

theorem p7_width_chain {y s f : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (hs : 0 ≤ s)
    (hf : y ^ 150 * s ≤ f) : s / (1 / y) ^ 20310 ≤ y ^ 6 * f := by
  have e : s / (1 / y) ^ 20310 = y ^ 20310 * s := by
    rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
  rw [e]
  have h1 : y ^ 20310 ≤ y ^ 156 := pow_le_pow_of_le_one hy0.le hy1 (by norm_num)
  have h2 : y ^ 20310 * s ≤ y ^ 156 * s := mul_le_mul_of_nonneg_right h1 hs
  have h3 : y ^ 6 * (y ^ 150 * s) ≤ y ^ 6 * f := mul_le_mul_of_nonneg_left hf (by positivity)
  have e2 : y ^ 6 * (y ^ 150 * s) = y ^ 156 * s := by ring
  linarith

theorem p7_width_terminal {x y s f : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hy3 : x ^ 3 ≤ y) (hs : 1 / x ^ 1359 ≤ s) (hf : y ^ 150 * s ≤ f) :
    4 / x ≤ f ∧ s / (1 / x) ^ 20310 ≤ x * f / 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hx4 : 4 * x ≤ 1 := by linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 4 by norm_num]
  have h1 : 1 ≤ s * x ^ 1359 := (div_le_iff₀ (by positivity)).mp hs
  have h2 : x ^ 450 * s ≤ f := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x ^ 3) hy3 150
    have e : (x ^ 3) ^ 150 = x ^ 450 := by rw [← pow_mul]
    rw [e] at h
    exact (mul_le_mul_of_nonneg_right h hs0.le).trans hf
  constructor
  · rw [div_le_iff₀ hx]
    have h3 : s * x ^ 1359 ≤ f * x * x ^ 908 := by
      have := mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ x ^ 909 by positivity)
      have e1 : x ^ 450 * s * x ^ 909 = s * x ^ 1359 := by ring
      have e2 : f * x ^ 909 = f * x * x ^ 908 := by ring
      linarith
    have h4 : (4 : ℝ) * x ^ 908 ≤ 1 := by
      have : x ^ 908 ≤ x ^ 1 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
      rw [pow_one] at this
      linarith
    have hfx : 0 ≤ f * x := mul_nonneg (le_trans (by positivity) h2) hx.le
    by_contra hcon
    push Not at hcon
    have h5 : f * x * x ^ 908 ≤ 4 * x ^ 908 :=
      mul_le_mul_of_nonneg_right hcon.le (by positivity)
    have h6 : f * x * x ^ 908 < 4 * x ^ 908 :=
      mul_lt_mul_of_pos_right hcon (by positivity)
    linarith
  · have e : s / (1 / x) ^ 20310 = x ^ 20310 * s := by
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [e]
    have h3 : x ^ 20310 ≤ x ^ 452 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
    have h4 : x ^ 20310 * s ≤ x ^ 452 * s := mul_le_mul_of_nonneg_right h3 hs0.le
    have h5 : x ^ 452 * s ≤ x ^ 451 * s / 4 := by
      have : x ^ 451 * s * (4 * x) ≤ x ^ 451 * s * 1 :=
        mul_le_mul_of_nonneg_left hx4 (by positivity)
      have e2 : x ^ 451 * s * (4 * x) = 4 * (x ^ 452 * s) := by ring
      linarith
    have h6 : x ^ 451 * s / 4 ≤ x * f / 4 := by
      have := mul_le_mul_of_nonneg_left h2 hx.le
      have e3 : x * (x ^ 450 * s) = x ^ 451 * s := by ring
      linarith
    linarith

/-- The terminal case of round one: the admissible scale has dropped below `x`. -/
theorem p7_round1_terminal {x y : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hy0 : 0 < y) (hy3 : x ^ 3 ≤ y) (hyx : y < x) {S F : Finset V}
    (hS : 1 / x ^ 1359 ≤ (S.card : ℝ)) (hadm : P7Adm G S y F) : P7Goal G S x := by
  obtain ⟨hFS, hFsp, hFc⟩ := hadm
  obtain ⟨hF4, hwid⟩ := p7_width_terminal hx hx64 hy3 hS hFc
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

theorem p7_sixth_root {z : ℝ} (hz0 : 0 < z) (hz64 : z ≤ 1 / 2 ^ 64) :
    ∃ w : ℝ, 0 < w ∧ w ^ 6 = z ∧ w ≤ 1 / 2 ^ 8 := by
  refine ⟨z ^ ((1 : ℝ) / 6), Real.rpow_pos_of_pos hz0 _, ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
    norm_num
  · have hw0 : 0 < z ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hz0 _
    have hw6 : (z ^ ((1 : ℝ) / 6)) ^ 6 = z := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
      norm_num
    by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h (by positivity) (show (6 : ℕ) ≠ 0 by norm_num)
    rw [hw6] at h1
    have : ((1 : ℝ) / 2 ^ 8) ^ 6 = 1 / 2 ^ 48 := by norm_num
    rw [this] at h1
    linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 2 ^ 48 by norm_num]

theorem p7_sparse_scale {x y z w s f t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hw0 : 0 < w) (hw6 : w ^ 6 = z) (hw8 : w ≤ 1 / 2 ^ 8)
    (hz1 : x ^ 2 ≤ z) (hz2 : z ≤ y) (hz64 : z ≤ 1 / 2 ^ 64) (hs : 0 ≤ s)
    (hf : y ^ 150 * s ≤ f) (ht : z ^ 24 * (f / 2 ^ 8) ≤ t) :
    x ^ 3 ≤ w ^ 7 ∧ w ^ 7 ≤ y / 2 ^ 8 ∧ z ^ 4 ≤ (w ^ 7) ^ 3 / 2 ^ 8 ∧ (w ^ 7) ^ 150 * s ≤ t := by
  have hz0 : 0 < z := by rw [← hw6]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h (by positivity) (show (6 : ℕ) ≠ 0 by norm_num)
    have e1 : (w ^ 7) ^ 6 = z ^ 7 := by rw [← hw6]; ring
    have e2 : (x ^ 3) ^ 6 = x ^ 18 := by ring
    rw [e1, e2] at h1
    have h2 : (x ^ 2) ^ 7 ≤ z ^ 7 := pow_le_pow_left₀ (by positivity) hz1 7
    have e3 : (x ^ 2) ^ 7 = x ^ 14 := by ring
    rw [e3] at h2
    have h3 : x ^ 18 ≤ x ^ 14 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
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
    have h1 : z ^ 150 * s ≤ y ^ 150 * s :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hz2 150) hs
    have h2 : z ^ 24 * (z ^ 150 * s / 2 ^ 8) ≤ z ^ 24 * (f / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right (h1.trans hf) (by positivity)
    have e1 : (w ^ 7) ^ 150 * s = z ^ 174 * s * z := by rw [← hw6]; ring
    have e2 : z ^ 24 * (z ^ 150 * s / 2 ^ 8) = z ^ 174 * s * (1 / 2 ^ 8) := by ring
    rw [e1]
    have h3 : z ^ 174 * s * z ≤ z ^ 174 * s * (1 / 2 ^ 8) :=
      mul_le_mul_of_nonneg_left hz8 (mul_nonneg (pow_nonneg hz0.le _) hs)
    linarith

theorem p7_width_compl {x y z s f t k : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64)
    (hz1 : x ^ 2 ≤ z) (hz2 : z ≤ y) (hz64 : z ≤ 1 / 2 ^ 64)
    (hk : k = min (1 / z ^ 2) (1 / x)) (hs : 1 / x ^ 1359 ≤ s)
    (hf : y ^ 150 * s ≤ f) (ht : z ^ 24 * (f / 2 ^ 8) ≤ t) :
    2 ≤ k ∧ k * x ≤ 1 ∧ s / k ^ 20310 ≤ (⌊(z ^ 2) ^ 2 * t⌋₊ : ℝ) := by
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
  have hzk : 1 ≤ z * k ^ 2 := by
    rcases le_total (1 / z ^ 2) (1 / x) with h | h
    · have e : k = 1 / z ^ 2 := by rw [hk]; exact min_eq_left h
      rw [e]
      have e2 : z * (1 / z ^ 2) ^ 2 = 1 / z ^ 3 := by field_simp
      rw [e2, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_one₀ hz0.le hz1'
    · have e : k = 1 / x := by rw [hk]; exact min_eq_right h
      rw [e]
      have e2 : z * (1 / x) ^ 2 = z / x ^ 2 := by field_simp
      rw [e2, le_div_iff₀ (by positivity), one_mul]
      exact hz1
  have h1 : z ^ 150 * s ≤ f :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0.le hz2 150) hs0.le).trans hf
  have h2 : z ^ 178 * s / 2 ^ 8 ≤ (z ^ 2) ^ 2 * t := by
    have a1 : z ^ 24 * (z ^ 150 * s / 2 ^ 8) ≤ z ^ 24 * (f / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have a2 := mul_le_mul_of_nonneg_left (a1.trans ht) (show (0 : ℝ) ≤ (z ^ 2) ^ 2 by positivity)
    have e : (z ^ 2) ^ 2 * (z ^ 24 * (z ^ 150 * s / 2 ^ 8)) = z ^ 178 * s / 2 ^ 8 := by ring
    linarith
  have hk2 : (2 : ℝ) ^ 9 ≤ k ^ 2 := by nlinarith [show (2 : ℝ) ^ 9 ≤ 2 ^ 64 by norm_num]
  -- s * 2^9 ≤ z^178 * s * k^20310
  have hkey : s * 2 ^ 9 ≤ z ^ 178 * s * k ^ 20310 := by
    have b1 : (k ^ 2) ^ 179 ≤ k ^ 20310 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hk1 (by norm_num)
    have b2 : (z * k ^ 2) ^ 178 * k ^ 2 = z ^ 178 * (k ^ 2) ^ 179 := by ring
    have b3 : 1 * k ^ 2 ≤ (z * k ^ 2) ^ 178 * k ^ 2 :=
      mul_le_mul_of_nonneg_right (one_le_pow₀ hzk) (by positivity)
    have b4 : z ^ 178 * (k ^ 2) ^ 179 ≤ z ^ 178 * k ^ 20310 :=
      mul_le_mul_of_nonneg_left b1 (by positivity)
    have b5 : (2 : ℝ) ^ 9 ≤ z ^ 178 * k ^ 20310 := by linarith
    have := mul_le_mul_of_nonneg_left b5 hs0.le
    linarith [show z ^ 178 * s * k ^ 20310 = s * (z ^ 178 * k ^ 20310) by ring]
  have hlow : s / k ^ 20310 ≤ z ^ 178 * s / 2 ^ 9 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hone : 1 ≤ (z ^ 2) ^ 2 * t := by
    refine le_trans ?_ h2
    -- z^178 * s / 2^8 ≥ x^356 * s / 2^8 ≥ 1
    have c1 : (x ^ 2) ^ 178 ≤ z ^ 178 := pow_le_pow_left₀ (by positivity) hz1 178
    have e : (x ^ 2) ^ 178 = x ^ 356 := by rw [← pow_mul]
    rw [e] at c1
    have c2 : 1 ≤ s * x ^ 1359 := (div_le_iff₀ (by positivity)).mp hs
    have c3 : x ^ 1003 ≤ 1 / 2 ^ 8 := by
      have : x ^ 1003 ≤ x ^ 1 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
      rw [pow_one] at this
      linarith [show (1 : ℝ) / 2 ^ 64 ≤ 1 / 2 ^ 8 by norm_num]
    have c4 : s * x ^ 1359 ≤ x ^ 356 * s * (1 / 2 ^ 8) := by
      have := mul_le_mul_of_nonneg_left c3 (show (0 : ℝ) ≤ x ^ 356 * s by positivity)
      have e2 : x ^ 356 * s * x ^ 1003 = s * x ^ 1359 := by ring
      linarith
    have c5 : x ^ 356 * s * (1 / 2 ^ 8) ≤ z ^ 178 * s * (1 / 2 ^ 8) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right c1 hs0.le
    linarith [show z ^ 178 * s * (1 / 2 ^ 8) = z ^ 178 * s / 2 ^ 8 by ring]
  have hfl := EHP6.floor_half hone
  refine ⟨le_trans (by norm_num) hk64, hkx, ?_⟩
  have : z ^ 178 * s / 2 ^ 9 ≤ (z ^ 2) ^ 2 * t / 2 := by
    have := div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 2 by norm_num)
    linarith [show z ^ 178 * s / 2 ^ 8 / 2 = z ^ 178 * s / 2 ^ 9 by ring]
  linarith

/-- One improvement step of the scale potential: either the round-one target is
    reached, or there is an admissible pair at a scale smaller by a factor `2^8`,
    still at least `x^3`. The restricted outcome keeps its actual scale `z`. -/
theorem p7_round1_improve (hcomb : EHP6.NssComb) (hP : NssPath7) (hfree : EHP6.Free G P7ᶜ)
    {x y : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64)
    {S F : Finset V} (hS : 1 / x ^ 1359 ≤ (S.card : ℝ)) (hadm : P7Adm G S y F) :
    P7Goal G S x ∨ ∃ y' : ℝ, ∃ F' : Finset V, x ^ 3 ≤ y' ∧ y' ≤ y / 2 ^ 8 ∧ P7Adm G S y' F' := by
  obtain ⟨hFS, hFsp, hFc⟩ := hadm
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hFbig := p7_order_F hx hx64 hxy hS hFc
  rcases round1_step_p7 hcomb hfree hx hxy hy F hFsp hFbig with ⟨T, hTF, hTc, hTsp⟩ |
      ⟨K, hK1, hK2, β, hβ⟩ | ⟨β, hβ⟩ | ⟨z, hz1, hz2, T, hTF, hTs, hTr⟩
  · -- sparser subset: scale y / 2^8
    right
    refine ⟨y / 2 ^ 8, T, ?_, le_rfl, hTF.trans hFS, ?_, ?_⟩
    · have h1 : x ^ 3 ≤ x * (1 / 2 ^ 8) := by
        have h2 : x ^ 2 ≤ 1 / 2 ^ 8 := by
          have := pow_le_pow_left₀ hx.le hx64 2
          linarith [show ((1 : ℝ) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 8 by norm_num]
        have := mul_le_mul_of_nonneg_left h2 hx.le
        linarith [show x * x ^ 2 = x ^ 3 by ring]
      have h3 : x * (1 / 2 ^ 8) ≤ y * (1 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right hxy (by positivity)
      linarith [show y * (1 / 2 ^ 8) = y / 2 ^ 8 by ring]
    · refine EHP6.sparse_sub hTsp subset_rfl (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
      rw [show (y / 2 ^ 8) ^ 3 / 2 ^ 8 = y ^ 3 * (1 / 2 ^ 32) by ring,
        show 2 * y ^ 4 = y ^ 3 * (2 * y) by ring]
      exact mul_le_mul_of_nonneg_left
        (by linarith [show (2 : ℝ) * (1 / 2 ^ 64) ≤ 1 / 2 ^ 32 by norm_num]) (by positivity)
    · have e : (y / 2 ^ 8) ^ 150 * (S.card : ℝ) = y ^ 150 * S.card * (1 / 2 ^ 8) ^ 150 := by ring
      rw [e]
      have h1 : y ^ 150 * (S.card : ℝ) * (1 / 2 ^ 8) ^ 150 ≤ y ^ 150 * S.card * (1 / 2 ^ 8) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hy0.le _) hS0)
        calc ((1 : ℝ) / 2 ^ 8) ^ 150 ≤ (1 / 2 ^ 8) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) (by norm_num)
          _ = 1 / 2 ^ 8 := pow_one _
      have h2 : y ^ 150 * (S.card : ℝ) * (1 / 2 ^ 8) ≤ F.card * (1 / 2 ^ 8) :=
        mul_le_mul_of_nonneg_right hFc (by positivity)
      linarith [show (F.card : ℝ) * (1 / 2 ^ 8) = F.card / 2 ^ 8 by ring]
  · -- blockade from the comb oracle
    left
    obtain ⟨k, hk⟩ : ∃ k : ℝ, k = min (K : ℝ) (1 / x) := ⟨_, rfl⟩
    have hK64 : (2 : ℝ) ^ 64 ≤ K := EHP6.cl_ell64 hy0 hy hK1
    have hk64 : (2 : ℝ) ^ 64 ≤ k := by rw [hk]; exact le_min hK64 (p7_inv_big hx hx64)
    refine ⟨k, le_trans (by norm_num) hk64, ?_, β.mono hFS (by rw [hk]; exact min_le_left _ _)
      (p7_width_block hx hxy hy1 hK1 hK2 hk hFc hS0), fun i j hij => hβ i j hij⟩
    have h1 : k ≤ 1 / x := by rw [hk]; exact min_le_right _ _
    have := mul_le_mul_of_nonneg_right h1 hx.le
    rwa [one_div, inv_mul_cancel₀ hx.ne'] at this
  · -- sparse chain
    left
    have h64 := p7_inv_big hy0 hy
    refine ⟨1 / y, le_trans (by norm_num) h64, ?_, β.mono hFS le_rfl
      (p7_width_chain hy0 hy1 hS0 hFc), fun i j hij => EHP6.semisparse_of_sparse β hβ i j hij⟩
    rw [one_div, inv_mul_le_iff₀ hy0]
    linarith
  · -- restricted set at its actual scale z
    have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
    have hz64 : z ≤ 1 / 2 ^ 64 := hz2.trans hy
    rcases hTr with hsp | hspc
    · right
      obtain ⟨w, hw0, hw6, hw8⟩ := p7_sixth_root hz0 hz64
      obtain ⟨c1, c2, c3, c4⟩ := p7_sparse_scale hx hx1 hw0 hw6 hw8 hz1 hz2 hz64 hS0 hFc hTs
      exact ⟨w ^ 7, T, c1, c2, hTF.trans hFS,
        EHP6.sparse_sub hsp subset_rfl (mul_le_mul_of_nonneg_right c3 (Nat.cast_nonneg _)), c4⟩
    · left
      obtain ⟨k, hk⟩ : ∃ k : ℝ, k = min (1 / z ^ 2) (1 / x) := ⟨_, rfl⟩
      obtain ⟨hk2, hkx, hwid⟩ := p7_width_compl hx hx64 hz1 hz2 hz64 hk hS hFc hTs
      have hnot := compl_not_contains_p7 hfree T
      have hz420 : z ^ 2 ≤ 1 / 420 := by
        have : z ^ 2 ≤ (1 / 2 ^ 64) ^ 2 := pow_le_pow_left₀ hz0.le hz64 2
        linarith [show ((1 : ℝ) / 2 ^ 64) ^ 2 ≤ 1 / 420 by norm_num]
      have hspc' : EHP6.Sparse Gᶜ ((z ^ 2) ^ 2) T := by
        rw [show (z ^ 2) ^ 2 = z ^ 4 by ring]
        exact hspc
      obtain ⟨β, hβ⟩ := hP (z ^ 2) (by positivity) hz420 V Gᶜ T hspc' hnot
      refine ⟨k, hk2, hkx, β.mono (hTF.trans hFS) (by rw [hk]; exact min_le_left _ _) hwid,
        fun i j hij => Or.inl ?_⟩
      intro a ha b hb
      have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
      by_contra hn
      exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj G a b).2 ⟨hab, hn⟩)

/-- Round one for complement-P7-free graphs: a `(2^-64)^3/2^8`-sparse set of order
    at least `x^(-1359)` has an `x`-semisparse blockade of real length `k ∈ [2, 1/x]`
    and width `|S|/k^20310`. -/
theorem round1_p7 (hcomb : EHP6.NssComb) (hP : NssPath7) (hfree : EHP6.Free G P7ᶜ)
    {x : ℝ} (hx : 0 < x) (hx64 : x ≤ 1 / 2 ^ 64) (S : Finset V)
    (hsp : EHP6.Sparse G ((1 / 2 ^ 64) ^ 3 / 2 ^ 8) S)
    (hS : 1 / x ^ 1359 ≤ (S.card : ℝ)) : P7Goal G S x := by
  have hx1 : x ≤ 1 := hx64.trans (by norm_num)
  have hx3 : 0 < x ^ 3 := by positivity
  have key : ∀ n : ℕ, ∀ (y : ℝ) (F : Finset V), x ^ 3 ≤ y → y ≤ 1 / 2 ^ 64 →
      y ≤ x * (2 ^ 8) ^ n → P7Adm G S y F → P7Goal G S x := by
    intro n
    induction n with
    | zero =>
      intro y F h3 hy hyn hadm
      have hy0 : 0 < y := hx3.trans_le h3
      by_cases hyx : y < x
      · exact p7_round1_terminal hx hx64 hy0 h3 hyx hS hadm
      · push Not at hyx
        rcases p7_round1_improve hcomb hP hfree hx hx64 hyx hy hS hadm with h |
          ⟨y', F', h3', hy', hadm'⟩
        · exact h
        · have hy'0 : 0 < y' := hx3.trans_le h3'
          have hy'x : y' < x := by
            have : y ≤ x := by simpa using hyn
            have h2 : y / 2 ^ 8 ≤ x / 2 ^ 8 := div_le_div_of_nonneg_right this (by positivity)
            have h4 : x / 2 ^ 8 < x := by
              rw [div_lt_iff₀ (by positivity)]
              nlinarith
            linarith
          exact p7_round1_terminal hx hx64 hy'0 h3' hy'x hS hadm'
    | succ n ih =>
      intro y F h3 hy hyn hadm
      have hy0 : 0 < y := hx3.trans_le h3
      by_cases hyx : y < x
      · exact p7_round1_terminal hx hx64 hy0 h3 hyx hS hadm
      · push Not at hyx
        rcases p7_round1_improve hcomb hP hfree hx hx64 hyx hy hS hadm with h |
          ⟨y', F', h3', hy', hadm'⟩
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
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((1 / 2 ^ 64) / x) (by norm_num : (1 : ℝ) < 2 ^ 8)
  have hN' : (1 : ℝ) / 2 ^ 64 ≤ x * (2 ^ 8) ^ N := by
    have := (div_lt_iff₀ hx).mp hN
    linarith
  refine key N (1 / 2 ^ 64) S ?_ le_rfl hN' ⟨subset_rfl, hsp, ?_⟩
  · have : x ^ 3 ≤ x ^ 1 := pow_le_pow_of_le_one hx.le hx1 (by norm_num)
    rw [pow_one] at this
    linarith
  · exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by
      apply pow_le_one₀ (by positivity)
      norm_num)

#print axioms round1_step_p7
#print axioms p7_round1_terminal
#print axioms p7_round1_improve
#print axioms round1_p7
end AllPathsLocal
