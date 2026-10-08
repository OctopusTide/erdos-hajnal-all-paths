import AllPathsRecurrenceGraph
import AllPathsNegativeBridge
import RP5Reduction

/-!
# The RPq Tooth recurrence

Main paper, Theorem "The relative-ambient RPq recurrence". From the contracts
`T_(q-1)` and `T_(q-2)` in a host `G` (with common constants) and an EH exponent `κ`
of the ordered class `E_(q-1)` inside an ambient property containing every induced
subgraph of the complement of `G`, the contract `T_q` holds in `G`, with explicit
constants. Here `q = n + 3`, `H ≥ max(2, 1/κ)` is an integer and `d_t = 4H + 5`.

The full cut tree, the retained tree, the mass accounting, the small-component
grouping and the positive size selection are the q-independent theorems proved for
the RP5 Tooth. The two frontier branches use `rpq_frontier_list`; the negative
branch uses the EH-transversal bridge `actual_negative_direction_conclusion_eh`.
-/

namespace AllPathsLocal

open Finset Classical

theorem rn_t {x y : ℝ} {dt t : ℕ} (hdt : 1 ≤ dt) (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2 ^ 16) (ht : t = ⌈1 / y ^ dt⌉₊) :
    2 ^ 16 ≤ t ∧ 1 / y ^ dt ≤ (t : ℝ) ∧ (t : ℝ) ≤ 2 / y ^ dt ∧ (t : ℝ) ≤ 2 / x ^ dt := by
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := hy.trans (by norm_num)
  have h1 : 1 / y ^ dt ≤ (t : ℝ) := by rw [ht]; exact Nat.le_ceil _
  have hyd : y ^ dt ≤ y := by
    calc y ^ dt ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy1 hdt
      _ = y := pow_one y
  have h16 : (2 : ℝ) ^ 16 ≤ 1 / y ^ dt := by
    rw [le_div_iff₀ (pow_pos hy0 _)]
    have h2 : (2 : ℝ) ^ 16 * y ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hy (show (0 : ℝ) ≤ 2 ^ 16 by positivity)
      norm_num at this ⊢
      linarith
    have := mul_le_mul_of_nonneg_left hyd (show (0 : ℝ) ≤ 2 ^ 16 by positivity)
    linarith
  have h2 : (t : ℝ) ≤ 2 / y ^ dt := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / y ^ dt)
    rw [← ht] at this
    have e : 2 / y ^ dt = 1 / y ^ dt + 1 / y ^ dt := by ring
    linarith [show (1 : ℝ) ≤ 2 ^ 16 by norm_num]
  refine ⟨?_, h1, h2, h2.trans ?_⟩
  · have : ((2 ^ 16 : ℕ) : ℝ) ≤ t := by push_cast; linarith
    exact_mod_cast this
  · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
      (pow_le_pow_left₀ hx.le hxy dt)

theorem rn_pow6 {a t : ℝ} {dt : ℕ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht : t ≤ 2 / a ^ dt) :
    t ^ 6 ≤ 64 / a ^ (6 * dt) := by
  have h6 : t ^ 6 ≤ (2 / a ^ dt) ^ 6 := pow_le_pow_left₀ ht0 ht 6
  have e : (2 / a ^ dt) ^ 6 = 64 / a ^ (6 * dt) := by
    rw [div_pow, ← pow_mul, Nat.mul_comm]; norm_num
  rw [e] at h6
  exact h6

theorem rn_clean {y t N : ℝ} {dt : ℕ} (hy0 : 0 < y) (hy : y ≤ 1 / 2 ^ 16) (ht0 : 0 < t)
    (ht : t ≤ 2 / y ^ dt) (hN : 0 ≤ N) : y ^ (6 * dt + 2) * N ≤ N / t ^ 6 := by
  rw [le_div_iff₀ (pow_pos ht0 6)]
  have h6 := rn_pow6 hy0 ht0.le ht
  have hy2 : y ^ 2 * 64 ≤ 1 := by
    have h := pow_le_pow_left₀ hy0.le hy 2
    linarith [show ((1 : ℝ) / 2 ^ 16) ^ 2 * 64 ≤ 1 by norm_num]
  have h1 : y ^ (6 * dt + 2) * N * t ^ 6 ≤ y ^ (6 * dt + 2) * N * (64 / y ^ (6 * dt)) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have e2 : y ^ (6 * dt + 2) * N * (64 / y ^ (6 * dt)) = (y ^ 2 * 64) * N := by
    rw [pow_add]
    field_simp
  have h2 : (y ^ 2 * 64) * N ≤ 1 * N := mul_le_mul_of_nonneg_right hy2 hN
  linarith

theorem rn_m_upper {x t M : ℝ} {dt : ℕ} (hx : 0 < x) (hx16 : x ≤ 1 / 2 ^ 16) (ht0 : 0 ≤ t)
    (ht : t ≤ 2 / x ^ dt) (hM : M ≤ 4 * t ^ 6 / x) : M ≤ 1 / x ^ (6 * dt + 2) := by
  have h6 := rn_pow6 hx ht0 ht
  have h1 : 4 * t ^ 6 / x ≤ 4 * (64 / x ^ (6 * dt)) / x :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h6 (by norm_num)) hx.le
  have h256 : 256 * x ≤ 1 := by
    linarith [show (256 : ℝ) * (1 / 2 ^ 16) ≤ 1 by norm_num]
  have e : 4 * (64 / x ^ (6 * dt)) / x = 256 * x / x ^ (6 * dt + 2) := by
    rw [pow_add]
    field_simp
    ring
  have h2 : 256 * x / x ^ (6 * dt + 2) ≤ 1 / x ^ (6 * dt + 2) :=
    div_le_div_of_nonneg_right h256 (pow_nonneg hx.le _)
  linarith

theorem rn_caps {x M : ℝ} {dt : ℕ} (hx : 0 < x) (hM1 : 1 ≤ M)
    (hM : M ≤ 1 / x ^ (6 * dt + 2)) (j : ℕ) :
    (M / x) ^ j ≤ 1 / x ^ ((6 * dt + 3) * j) ∧ x ^ ((6 * dt + 3) * j) ≤ (x / M) ^ j := by
  have hM0 : 0 < M := by linarith
  have hMx : M * x ^ (6 * dt + 2) ≤ 1 := (le_div_iff₀ (pow_pos hx _)).mp hM
  have e3 : x ^ (6 * dt + 3) = x ^ (6 * dt + 2) * x := by
    rw [show 6 * dt + 3 = (6 * dt + 2) + 1 by ring, pow_succ]
  have h1 : M / x ≤ 1 / x ^ (6 * dt + 3) := by
    rw [div_le_div_iff₀ hx (pow_pos hx _), e3]
    nlinarith
  have h2 : x ^ (6 * dt + 3) ≤ x / M := by
    rw [le_div_iff₀ hM0, e3]
    nlinarith
  constructor
  · calc (M / x) ^ j ≤ (1 / x ^ (6 * dt + 3)) ^ j := pow_le_pow_left₀ (by positivity) h1 j
      _ = 1 / x ^ ((6 * dt + 3) * j) := by rw [one_div_pow, ← pow_mul]
  · calc x ^ ((6 * dt + 3) * j) = (x ^ (6 * dt + 3)) ^ j := by rw [← pow_mul]
      _ ≤ (x / M) ^ j := pow_le_pow_left₀ (by positivity) h2 j

theorem rn_order {x M N : ℝ} {dt Q : ℕ} (hx : 0 < x) (hM1 : 1 ≤ M)
    (hM : M ≤ 1 / x ^ (6 * dt + 2))
    (hN : 1 / x ^ ((6 * dt + 3) * Q + 36 * dt + 12) ≤ N) : (M / x) ^ Q ≤ N / M ^ 6 := by
  have hM0 : 0 < M := by linarith
  rw [le_div_iff₀ (pow_pos hM0 6)]
  have h1 := (rn_caps hx hM1 hM Q).1
  have h2 : M ^ 6 ≤ 1 / x ^ (36 * dt + 12) := by
    calc M ^ 6 ≤ (1 / x ^ (6 * dt + 2)) ^ 6 := pow_le_pow_left₀ hM0.le hM 6
      _ = 1 / x ^ (36 * dt + 12) := by
          rw [one_div_pow, ← pow_mul, show (6 * dt + 2) * 6 = 36 * dt + 12 by ring]
  have h3 : (M / x) ^ Q * M ^ 6 ≤ (1 / x ^ ((6 * dt + 3) * Q)) * (1 / x ^ (36 * dt + 12)) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have e : (1 / x ^ ((6 * dt + 3) * Q)) * (1 / x ^ (36 * dt + 12)) =
      1 / x ^ ((6 * dt + 3) * Q + 36 * dt + 12) := by
    rw [div_mul_div_comm, one_mul, ← pow_add, Nat.add_assoc]
  linarith

theorem rn_complete_cap {x t : ℝ} {dt kn : ℕ} (hx : 0 < x) (hx16 : x ≤ 1 / 2 ^ 16)
    (ht : t ≤ 2 / x ^ dt) (hkn : dt + 1 ≤ kn) : t ≤ 1 / x ^ kn := by
  have hx1 : x ≤ 1 := hx16.trans (by norm_num)
  have h2x : 2 * x ≤ 1 := by linarith [show (2 : ℝ) * (1 / 2 ^ 16) ≤ 1 by norm_num]
  have h1 : 2 / x ^ dt ≤ 1 / x ^ (dt + 1) := by
    rw [div_le_div_iff₀ (pow_pos hx _) (pow_pos hx _), pow_succ]
    have : 0 < x ^ dt := pow_pos hx _
    nlinarith
  have h2 : 1 / x ^ (dt + 1) ≤ 1 / x ^ kn :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _) (pow_le_pow_of_le_one hx.le hx1 hkn)
  linarith

theorem rn_complete_width {t N : ℝ} {dn : ℕ} (ht : 1 ≤ t) (hN : 0 ≤ N) (hdn : 7 ≤ dn) :
    N / t ^ dn ≤ N / t ^ 6 / t := by
  have ht0 : 0 < t := by linarith
  have e : N / t ^ 6 / t = N / t ^ 7 := by rw [div_div, ← pow_succ]
  rw [e]
  exact div_le_div_of_nonneg_left hN (pow_pos ht0 _) (pow_le_pow_right₀ ht hdn)

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1600000 in
/-- **The RPq Tooth recurrence.** -/
theorem rpq_tooth (n : ℕ) {A e c k d E : ℕ} {η₀ : ℝ} (hE : 1 ≤ E) (hk : 1 ≤ k) (hc : 1 ≤ c)
    (hη₀ : η₀ ≤ 1 / 2 ^ 16)
    (hT1 : LowerTooth G (n + 2) A e c k d E η₀) (hT2 : LowerTooth G (n + 1) A e c k d E η₀)
    (Amb : ∀ (W : Type), SimpleGraph W → Prop)
    (hAmb : ∀ S : Finset V, Amb ↥(S : Set V) (Gᶜ.induce (S : Set V)))
    (κ : ℝ) (H : ℕ) (hκ : 0 ≤ κ) (hH : 2 ≤ H) (hHκ : 1 ≤ (H : ℝ) * κ)
    (hEH : OrderedClassEH Amb (n + 1) κ) :
    LowerTooth G (n + 3) (6 * (4 * H + 5) + 2) (e + 2 * A + 7 + 8 * H + (4 * H + 5) + 10)
      (c * (4 * A + 11) * (6 * (4 * H + 5) + 3)) (k * (4 * A + 11) * (6 * (4 * H + 5) + 3))
      (9 * A + d + 21) ((6 * (4 * H + 5) + 3) * (E * (4 * A + 11)) + 36 * (4 * H + 5) + 12)
      (min η₀ ((2 : ℝ) ^ (-((H : ℝ) + 10)))) := by
  obtain ⟨dt, hdt⟩ : ∃ dt : ℕ, dt = 4 * H + 5 := ⟨_, rfl⟩
  rw [← hdt]
  intro U Y x y hout hfree hx hxy hyy hN
  have hyη : y ≤ η₀ := hyy.trans (min_le_left _ _)
  have hyH : y ≤ (2 : ℝ) ^ (-((H : ℝ) + 10)) := hyy.trans (min_le_right _ _)
  have hy16 : y ≤ 1 / 2 ^ 16 := hyη.trans hη₀
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := hy16.trans (by norm_num)
  have hx16 : x ≤ 1 / 2 ^ 16 := hxy.trans hy16
  have hx1 : x ≤ 1 := hxy.trans hy1
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈1 / y ^ dt⌉₊ := ⟨_, rfl⟩
  obtain ⟨ht16, htLower, htUpperY, htUpperX⟩ := rn_t (by omega) hx hxy hy16 ht
  have ht16R : (2 : ℝ) ^ 16 ≤ t := by exact_mod_cast ht16
  have ht1 : (1 : ℝ) ≤ t := le_trans (by norm_num) ht16R
  have ht0 : (0 : ℝ) < t := by linarith
  obtain ⟨s, hscale⟩ : ∃ s : ℝ, s = (Y.card : ℝ) / (t : ℝ) ^ 6 := ⟨_, rfl⟩
  have hN0 : 0 < (Y.card : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hs : 0 < s := by rw [hscale]; positivity
  have hslarge : s ≤ (Y.card : ℝ) := by
    rw [hscale]; exact div_le_self hN0.le (one_le_pow₀ ht1)
  have hyd : y ^ dt ≤ y := by
    calc y ^ dt ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy1 (by omega)
      _ = y := pow_one y
  have hty : 1 / (t : ℝ) ≤ y := by
    rw [div_le_iff₀ ht0]
    have h3 : 1 / y ≤ (t : ℝ) :=
      le_trans (div_le_div_of_nonneg_left (by norm_num) (pow_pos hy0 _) hyd) htLower
    have := (div_le_iff₀ hy0).mp h3
    linarith
  by_cases hclean : ∃ A' ⊆ Y, s ≤ (A'.card : ℝ) ∧ FullOrSmall G U x A'
  · obtain ⟨A', hA'Y, hA's, hA'f⟩ := hclean
    left
    refine ⟨A', hA'Y, le_trans ?_ hA's, hA'f⟩
    rw [hscale]
    exact rn_clean hy0 hy16 ht0 htUpperY hN0.le
  right
  -- common conversion of the frontier lemma's two outcomes
  have hfront : ∀ Z : List (Finset V), (∀ K ∈ Z, K ⊆ Y) → Z.Pairwise Disjoint →
      (∀ (N' : ℕ) (f : Fin N' → Fin Z.length), StrictMono f →
        (∀ a b : Fin N', a.val + 1 = b.val →
          ¬ EHP6.Complete G (Z.get (f a)) (Z.get (f b))) →
        ∀ a b, a < b → ∃ u ∈ U, RootSeparates G u (Z.get (f a)) (Z.get (f b))) →
      t ≤ Z.length → (Z.length : ℝ) ≤ 4 * (t : ℝ) ^ 6 / x →
      (∀ K ∈ Z, (Y.card : ℝ) / (Z.length : ℝ) ^ 6 ≤ (K.card : ℝ)) →
      (∃ z : ℝ, x ^ (c * (4 * A + 11) * (6 * dt + 3)) ≤ z ∧ z ≤ y ∧ ∃ W ⊆ Y,
        z ^ (e + 2 * A + 7 + 8 * H + dt + 10) * Y.card ≤ (W.card : ℝ) ∧
        EHP6.Restricted G (z ^ 4) W) ∨
      (∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x ^ (k * (4 * A + 11) * (6 * dt + 3)) ∧
        ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ) ^ (9 * A + d + 21)), γ.m = K ∧
          ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
            EHP6.SparseTo G x (γ.B j) (γ.B i)) := by
    intro Z hZY hZdis hZsep htm hmup hZsize
    have hmM : (Z.length : ℝ) ≤ 1 / x ^ (6 * dt + 2) := rn_m_upper hx hx16 ht0.le htUpperX hmup
    have hm16 : 2 ^ 16 ≤ Z.length := le_trans ht16 htm
    have htmR : (t : ℝ) ≤ Z.length := by exact_mod_cast htm
    have hM1 : (1 : ℝ) ≤ Z.length := ht1.trans htmR
    have hM0 : (0 : ℝ) < Z.length := by linarith
    have hmy : 1 / (Z.length : ℝ) ≤ y :=
      (div_le_div_of_nonneg_left (by norm_num) ht0 htmR).trans hty
    rcases rpq_frontier_list n hE hk hT1 hT2 Z hZY hZdis hout hfree hZsep (τ := x)
        (N := (Y.card : ℝ)) (b₀ := 6) hm16 (hmy.trans hyη) hx hx1 hN0.le hZsize
        (fun K hK => (rn_order hx hM1 hmM hN).trans (hZsize K hK)) with
      ⟨z, hz1, hz2, T', hT'Y, hT'size, hT'res⟩ | ⟨K, hK1, hK2, γ, hγm, hγ⟩
    · left
      have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
      have hzy : z ≤ y := hz2.trans hmy
      refine ⟨z, le_trans ?_ hz1, hzy, T', hT'Y, le_trans ?_ hT'size, hT'res⟩
      · rw [Nat.mul_comm (c * (4 * A + 11)) (6 * dt + 3)]
        exact (rn_caps hx hM1 hmM (c * (4 * A + 11))).2
      · apply mul_le_mul_of_nonneg_right _ hN0.le
        exact pow_le_pow_of_le_one hz0.le (hzy.trans hy1) (by omega)
    · right
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      refine ⟨K, ?_, ?_, γ.mono subset_rfl le_rfl (le_of_eq ?_), hγm, hγ⟩
      · apply paper_output_length_lower y K hy0 hK0
        have h4 : 1 / y ^ 4 ≤ 1 / y ^ dt :=
          div_le_div_of_nonneg_left (by norm_num) (pow_pos hy0 _)
            (pow_le_pow_of_le_one hy0.le hy1 (by omega))
        linarith
      · refine hK2.trans ?_
        rw [Nat.mul_comm (k * (4 * A + 11)) (6 * dt + 3)]
        exact (rn_caps hx hM1 hmM (k * (4 * A + 11))).1
      · rw [show 3 * 6 + 9 * A + d + 3 = 9 * A + d + 21 by ring]
  by_cases hcomplete : ∃ β : EHP6.Blockade Y t (s / t), β.m = t ∧ β.IsComplete G
  · obtain ⟨β, hβm, hβ⟩ := hcomplete
    right
    refine ⟨t, ?_, ?_, β.mono subset_rfl le_rfl ?_, hβm,
      fun i j hij => Or.inl (hβ i j (ne_of_lt hij))⟩
    · have := (div_le_iff₀ ht0).mp hty
      rw [div_le_iff₀ hy0]
      linarith
    · refine rn_complete_cap hx hx16 htUpperX ?_
      have h1 : 1 ≤ k * (4 * A + 11) := Nat.mul_pos hk (by omega)
      nlinarith
    · rw [hscale]
      exact rn_complete_width ht1 hN0.le (by omega)
  have hno : ∀ K ⊆ Y, s ≤ (K.card : ℝ) → ¬ FullOrSmall G U x K :=
    fun K hK hs' hf => hclean ⟨K, hK, hs', hf⟩
  obtain ⟨tree⟩ := finite_root_cut_tree_exists G U x s hx hs Y
  obtain ⟨T⟩ := cut_tree_prune G U x s tree (Finset.Subset.refl Y) hslarge hno
  by_cases hq : t ≤ treeLeafCount T.toWeighted
  · obtain ⟨Z, hZ, hsize, hlength⟩ := retained_terminal_frontier G T
    have hm : t ≤ Z.length := by simpa only [hlength] using hq
    have hsize' : ∀ K ∈ Z, (Y.card : ℝ) / (t : ℝ) ^ 6 ≤ (K.card : ℝ) := by
      simpa only [hscale] using hsize
    have hmt6 := ordered_frontier_count_from_scale hZ t (by omega) hN0 hsize'
    have htmR : (t : ℝ) ≤ Z.length := by exact_mod_cast hm
    refine hfront Z (ordered_frontier_properties G U hZ).1 (ordered_frontier_disjoint G U hZ)
      (fun N' f hf hlinks => ordered_frontier_increasing_path_roots G U hZ f hf hlinks)
      hm ?_ ?_
    · refine hmt6.trans ?_
      rw [le_div_iff₀ hx]
      have : (0 : ℝ) ≤ (t : ℝ) ^ 6 := by positivity
      nlinarith
    · intro K hK
      refine le_trans ?_ (hsize' K hK)
      exact div_le_div_of_nonneg_left hN0.le (by positivity) (pow_le_pow_left₀ ht0.le htmR 6)
  · obtain ⟨P, hP, hmass⟩ := actual_direction_carries_mass T (Finset.Subset.refl Y) t (by omega)
      hscale (Nat.lt_of_not_ge hq) hcomplete
    rcases hmass with hpos | hneg
    · obtain ⟨m, Z, htm, hmL, hZsub, hZlen, hwidth⟩ :=
        actual_positive_size_selection hP (Finset.Subset.refl Y) t (by omega) hN0 hscale
          hcomplete hpos
      have hLbound := gen_positive_count_bound hP (Finset.Subset.refl Y) hx t (by omega) hN0
        hscale
      have hprops := gen_positive_blocks_properties (U := U) hP (Finset.Subset.refl Y)
      have hZpair := hprops.2.sublist hZsub
      have hmR1 : (1 : ℝ) ≤ m := ht1.trans (by exact_mod_cast htm)
      refine hfront Z (fun K hK => (hprops.1 K (hZsub.subset hK)).1)
        (hZpair.imp (fun h => h.1)) ?_ (by omega) ?_ ?_
      · intro N' f hf _ a b hab
        exact ((List.pairwise_iff_get.mp hZpair) (f a) (f b) (hf hab)).2
      · rw [hZlen]
        exact (by exact_mod_cast hmL : (m : ℝ) ≤ (positiveBlocks s P).length).trans hLbound
      · intro K hK
        rw [hZlen]
        refine le_trans ?_ (hwidth K hK)
        exact div_le_div_of_nonneg_left hN0.le (by positivity)
          (pow_le_pow_right₀ hmR1 (by norm_num))
    · obtain ⟨W, hWY, hWsize, hWdeg⟩ := actual_negative_direction_conclusion_eh (n + 1) hP hout
        hfree Amb (fun A' _ => hAmb A') κ (H : ℝ) hκ (by exact_mod_cast hH) hHκ hEH y hy0 hyH
        hN0 dt t (by rw [hdt]; push_cast; linarith) htLower htUpperY hscale hneg
      left
      have e1 : (8 * (H : ℝ) + (dt : ℝ) + 10) = ((8 * H + dt + 10 : ℕ) : ℝ) := by
        push_cast; ring
      rw [e1, Real.rpow_natCast] at hWsize
      refine ⟨y, ?_, le_rfl, W, hWY, le_trans ?_ hWsize, ?_⟩
      · have h1 : 1 ≤ c * (4 * A + 11) * (6 * dt + 3) :=
          Nat.mul_pos (Nat.mul_pos hc (by omega)) (by omega)
        calc x ^ (c * (4 * A + 11) * (6 * dt + 3)) ≤ x ^ 1 :=
              pow_le_pow_of_le_one hx.le hx1 h1
          _ = x := pow_one x
          _ ≤ y := hxy
      · apply mul_le_mul_of_nonneg_right _ hN0.le
        exact pow_le_pow_of_le_one hy0.le hy1 (by omega)
      · have he0 : (0 : ℝ) ≤ y ^ 4 := by positivity
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

#print axioms rpq_tooth
end AllPathsLocal
