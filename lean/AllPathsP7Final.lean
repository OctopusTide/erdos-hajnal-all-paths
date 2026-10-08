import AllPathsRound2Gen
import AllPathsP7Nice
import EHP6.Final

/-!
# The Erdős–Hajnal property for P7 from EH(P6)

This file closes the chain for `s = 7`. The inputs are displayed hypotheses:

* `RodlCoP7` — Rödl's theorem for the complement of `P7`;
* `NssPath7` — NSS V statement 3.1 for the path `P7` (proved below as
  `nss_path7_proof` from `EHP6.nss_path`);
* `EHP6.NssComb` — the comb lemma (NSS VII Lemma 4.3);
* `EHP6.EHforP6` — the Erdős–Hajnal property of `P6`.

`crux_P7`, `c01_lemma1_p7`, `polyRodl_p7` and `eh_of_polyRodl_p7` follow the proofs
of `EHP6.crux_P6`, `EHP6.c01_lemma1`, `EHP6.polyRodl` and `EHP6.eh_of_polyRodl`
with `P6` replaced by `P7` (and the numerical constants `1/360`, `2⁻¹⁷` replaced
by `1/420`, `2⁻¹⁸`). The P6-specific house lemma is replaced by the forcing
template and `light_hom_template`.
-/

namespace AllPathsLocal

open EHP6 Finset Classical

/-- The Erdős–Hajnal property for P7. -/
def EHforP7 : Prop :=
  ∃ τ : ℝ, 0 < τ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Free G P7 → ∃ T : Finset V, (IsCliqueF G T ∨ IsStableF G T) ∧
        (Fintype.card V : ℝ) ^ τ ≤ T.card

/-- Crux (C) for P̄7-free graphs (compare `EHP6.CruxC`). -/
def CruxC7 (a : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Free G P7ᶜ → ∀ y : ℝ, 0 < y → y ≤ 1 / 2 ^ 16 → ∀ S : Finset V, Sparse G y S →
      (∃ T ⊆ S, y ^ a * S.card ≤ T.card ∧ Sparse G (y ^ 2) T) ∨
      (∃ β : Blockade S (1 / Real.sqrt y) (y ^ a * S.card), β.IsComplete G ∨ β.IsAnticomplete G)

/-- An all-orders exponent for `P6` in the `EHOn` form used by the substitution
    lemmas. -/
theorem ehOn_P6_of_EHforP6 (hE : EHforP6) :
    ∃ γ : ℝ, 0 < γ ∧ EHOn (pathGraph' 6) Finset.univ γ := by
  obtain ⟨τ, hτ, h⟩ := hE
  refine ⟨τ, hτ, ?_⟩
  intro V _ G S hno
  let G' : SimpleGraph {x // x ∈ S} := G.comap Subtype.val
  have hfree : Free G' P6 := by
    rintro ⟨f, hinj, -, hadj⟩
    apply hno
    refine ⟨fun i => (f i).val, ?_, fun i _ => (f i).prop, fun i _ j _ => hadj i j⟩
    intro i _ j _ hij
    exact hinj (Subtype.ext hij)
  obtain ⟨T, hT, hTc⟩ := h {x // x ∈ S} G' hfree
  refine ⟨T.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hu
    exact w.prop
  · rcases hT with hc | hs
    · left
      intro u hu w hw huw
      obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
      exact hc u' hu' w' hw' (fun e => huw (by rw [e]))
    · right
      intro u hu w hw
      obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
      by_cases e : u' = w'
      · subst e
        exact G.irrefl
      · exact hs u' hu' w' hw' e
  · rw [Finset.card_map]
    rwa [Fintype.card_coe] at hTc

/-- **Strong wonderfulness input for P7**: a uniform `LightHom` exponent for all
    P̄7-free graphs, from EH(P6) through the forcing template. -/
theorem lightHom_P7 (hE : EHforP6) : ∃ κ : ℝ, 0 < κ ∧ ∃ θ₀ : ℝ, 0 < θ₀ ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Free G P7ᶜ → LightHom G κ θ₀ := by
  obtain ⟨α, iF, iD, Q, ⟨κ, hκ, hQ⟩, hforce⟩ :=
    forcing_template 6 (by norm_num) (ehOn_P6_of_EHforP6 hE)
  refine ⟨κ, hκ, 1 / (8 * ((Fintype.card α : ℝ) + 1)), by positivity, ?_⟩
  intro V _ _ G _ hfree ℓ B W x hS hdisj hx hW v
  have hnp : ¬ ∃ p : Fin (6 + 1) → V, IsInducedPath Gᶜ p := by
    rintro ⟨p, hp⟩
    exact hfree (compl_contains_of_inducedPath G p hp)
  have hx0 := hS.hx
  have hq0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hx' : 8 * (Fintype.card α : ℝ) * x ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hx
    nlinarith
  exact light_hom_template Q hforce hQ hnp hS hdisj hx' hW v

/-- **Crux (C) for P̄7-free graphs.** -/
theorem crux_P7 (hR : RodlCoP7) (hP : NssPath7) (hcomb : NssComb) (hE : EHforP6) :
    ∃ a : ℕ, CruxC7 a := by
  obtain ⟨d, hd, hnd⟩ := nice_P7 hR hP hcomb
  obtain ⟨κ, hκ, θ₀, hθ₀, hLH⟩ := lightHom_P7 hE
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hθ₀ (by norm_num : (1 : ℝ) / 8 < 1)
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, M' = ⌈5 / κ + 4⌉₊ + n₀ := ⟨_, rfl⟩
  have hM : 5 / κ + 4 ≤ ((2 * M' : ℕ) : ℝ) := by
    have h1 : 5 / κ + 4 ≤ ((⌈5 / κ + 4⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h0 : ((⌈5 / κ + 4⌉₊ : ℕ) : ℝ) ≤ M' := by rw [hM']; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n₀]
    have h2 : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
    push_cast; linarith
  have hMθ : ((1 : ℝ) / 8) ^ (2 * M') ≤ θ₀ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans hn₀.le
  refine ⟨M' * (10 * d ^ 2 + 3) + 1, fun V _ _ G _ hfree y hy0 hy S hsp => ?_⟩
  have h61 : Out61 G ((2 * M') * (10 * d ^ 2 + 3)) := fun y' hy'0 hy' S' hsp' =>
    round2_step_gen (hLH V G hfree) hd
      (fun ε hε0 hε S'' hS'' => hnd ε hε0 hε V G hfree S'' hS'') hκ hM hMθ hy'0 hy' S' hsp'
  exact round2 (k := M' * (10 * d ^ 2 + 3)) (by ring) h61 hy0 hy S hsp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
/-- **Lemma 8.1.** From Crux (C): there is `A` such that for every `x ∈ (0, ½)` and every
P̄7-free `G[S]`, either some `F ⊆ S` with `|F| ≥ x^A|S|` is `x`-restricted, or `G[S]` has a complete or
anticomplete `(k, |S|/k^A)`-blockade for some integer `k ∈ [2, 1/x]`. -/
theorem c01_lemma1_p7 (hRodl : RodlCoP7) (hP : NssPath7) {a : ℕ} (hcrux : CruxC7 a) : ∃ A : ℕ, 1 ≤ A ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P7ᶜ → ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ S : Finset W,
        (∃ F ⊆ S, x ^ A * S.card ≤ F.card ∧ Restricted H x F) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * x ≤ 1 ∧
          ∃ β : Blockade S k (S.card / (k : ℝ) ^ A), β.IsComplete H ∨ β.IsAnticomplete H) := by
  obtain ⟨δ, hδ0, hR⟩ := hRodl (1 / 2 ^ 18) (by norm_num) (by norm_num)
  obtain ⟨t₀, ht₀⟩ := exists_pow_lt_of_lt_one hδ0 (by norm_num : (1 : ℝ) / 2 ^ 18 < 1)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 / ((1 / 420) ^ 2 * δ)) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨t, ht⟩ : ∃ t, t = t₀ + a + 1 := ⟨_, rfl⟩
  have hct : ((1 : ℝ) / 2 ^ 18) ^ t ≤ δ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans ht₀.le
  have hηδ : 0 < (1 / 420 : ℝ) ^ 2 * δ := by positivity
  have hL' : 2 ≤ (1 / 420) ^ 2 * δ * 2 ^ L := by
    rw [div_lt_iff₀ hηδ] at hL; linarith
  refine ⟨2 * (a + t) + L, by omega, fun W _ _ H _ hfree x hx0 hx S => ?_⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * (a + t) + L := ⟨_, rfl⟩
  rw [← hA]
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx1 : x ≤ 1 := by linarith
  -- small `S`
  by_cases hsmall : (S.card : ℝ) < 1 / x ^ A
  · left
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · subst hSe
      exact ⟨∅, subset_rfl, by simp, Or.inl fun v hv => absurd hv (notMem_empty v)⟩
    obtain ⟨F, hF, hF1, hFr⟩ := restricted_single (G := H) x hx0.le S hSne
    refine ⟨F, hF, ?_, hFr⟩
    rw [lt_div_iff₀ (by positivity)] at hsmall; linarith
  push Not at hsmall
  have h2A : (2 : ℝ) ^ A ≤ S.card := by
    have h2x : (2 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
    have : (2 : ℝ) ^ A ≤ (1 / x) ^ A := pow_le_pow_left₀ (by norm_num) h2x A
    rw [one_div_pow] at this; linarith
  have h2L : (2 : ℝ) ^ L ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨F₀, hF₀S, hF₀c, hF₀r⟩ := hR W H hfree S
  by_cases hxc : 1 / 2 ^ 18 ≤ x
  · -- `F₀` is already `x`-restricted
    left
    refine ⟨F₀, hF₀S, le_trans ?_ hF₀c, hF₀r.imp (fun h => sparse_mono_param (G := H) h hxc)
      (fun h => sparse_mono_param (G := Hᶜ) h hxc)⟩
    apply mul_le_mul_of_nonneg_right _ hS0
    have a1 : x ^ A ≤ (1 / 2) ^ A := pow_le_pow_left₀ hx0.le hx.le A
    have a2 : ((1 : ℝ) / 2) ^ A * 2 ^ A = 1 := by rw [← mul_pow]; norm_num
    have a3 : (1 : ℝ) ≤ δ * 2 ^ A := by
      have : (1 / 420 : ℝ) ^ 2 * δ * 2 ^ L ≤ δ * 2 ^ A := by
        have b1 : (1 / 420 : ℝ) ^ 2 * δ ≤ δ := by nlinarith
        exact mul_le_mul b1 h2L (by positivity) hδ0.le
      linarith
    nlinarith
  push Not at hxc
  rcases hF₀r with hsp | hspc
  swap
  · -- the complement of `F₀` is sparse: a complete pair of blocks
    right
    have hnot := compl_not_contains_p7 hfree F₀
    have hspc' : Sparse Hᶜ ((1 / 420) ^ 2) F₀ := sparse_mono_param (G := Hᶜ) hspc (by norm_num)
    obtain ⟨β, hβ⟩ := hP (1 / 420) (by norm_num) le_rfl W Hᶜ F₀ hspc' hnot
    have hwid : (S.card : ℝ) / (2 : ℕ) ^ A ≤ (⌊((1 : ℝ) / 420) ^ 2 * F₀.card⌋₊ : ℝ) := by
      have hηF : (1 / 420 : ℝ) ^ 2 * δ * S.card ≤ (1 / 420) ^ 2 * F₀.card := by
        have := mul_le_mul_of_nonneg_left hF₀c (by positivity : (0 : ℝ) ≤ (1 / 420) ^ 2)
        linarith [show (1 / 420 : ℝ) ^ 2 * (δ * S.card) = (1 / 420) ^ 2 * δ * S.card by ring]
      have hηδA : 2 ≤ (1 / 420 : ℝ) ^ 2 * δ * 2 ^ A :=
        hL'.trans (mul_le_mul_of_nonneg_left h2L hηδ.le)
      have h1 : 1 ≤ (1 / 420 : ℝ) ^ 2 * F₀.card := by
        have := mul_le_mul_of_nonneg_left h2A hηδ.le
        nlinarith
      have h2 := floor_half h1
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have h3 : 2 * (S.card : ℝ) ≤ (1 / 420) ^ 2 * δ * 2 ^ A * S.card :=
        mul_le_mul_of_nonneg_right hηδA hS0
      have h4 : (1 / 420 : ℝ) ^ 2 * δ * S.card / 2 ≤ (⌊((1 : ℝ) / 420) ^ 2 * F₀.card⌋₊ : ℝ) := by
        linarith
      have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 2 ^ A)
      linarith [show (1 / 420 : ℝ) ^ 2 * δ * S.card / 2 * 2 ^ A =
        (1 / 420) ^ 2 * δ * 2 ^ A * S.card / 2 by ring]
    refine ⟨2, le_rfl, by push_cast; linarith, ⟨β.m, β.B, le_trans (by norm_num) β.len,
      fun i => (β.sub i).trans hF₀S, fun i => hwid.trans (β.wid i), β.disj⟩, Or.inl ?_⟩
    intro i j hij a ha b hb
    have hab : a ≠ b := fun e => disjoint_left.1 (β.disj i j hij) ha (e ▸ hb)
    by_contra hn
    exact hβ i j hij a ha b hb ((SimpleGraph.compl_adj H a b).2 ⟨hab, hn⟩)
  -- `F₀` is sparse: the discretized minimal scale `y_j = c₀^{2^j}`
  obtain ⟨Nb, hNb⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < x ^ 2)
    (by norm_num : (1 : ℝ) / 2 ^ 18 < 1)
  let Q : ℕ → Prop := fun j => x ^ 2 ≤ ((1 : ℝ) / 2 ^ 18) ^ (2 ^ j) ∧ ∃ F ⊆ S,
    Sparse H (((1 : ℝ) / 2 ^ 18) ^ (2 ^ j)) F ∧ (((1 : ℝ) / 2 ^ 18) ^ (2 ^ j)) ^ t * S.card ≤ F.card
  have hbound : ∀ j, Q j → j ≤ Nb := by
    intro j hj
    by_contra hjN; push Not at hjN
    have h1 : ((1 : ℝ) / 2 ^ 18) ^ (2 ^ j) ≤ (1 / 2 ^ 18) ^ Nb :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hjN.le.trans (Nat.lt_pow_self (by norm_num : 1 < 2) : j < 2 ^ j).le)
    linarith [hj.1]
  have hQ0 : Q 0 := by
    refine ⟨?_, F₀, hF₀S, ?_, ?_⟩ <;> simp only [pow_zero, pow_one]
    · nlinarith
    · exact hsp
    · exact le_trans (mul_le_mul_of_nonneg_right hct hS0) hF₀c
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.findGreatest Q Nb := ⟨_, rfl⟩
  have hQj : Q j := by rw [hj]; exact Nat.findGreatest_spec (Nat.zero_le _) hQ0
  have hQj1 : ¬ Q (j + 1) := fun h => by
    have hb := hbound _ h
    rw [hj] at h hb
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hb h
  obtain ⟨hxj, F, hFS, hFsp, hFc⟩ := hQj
  have hsq : ((1 : ℝ) / 2 ^ 18) ^ (2 ^ (j + 1)) = (((1 : ℝ) / 2 ^ 18) ^ (2 ^ j)) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  have hyc : ((1 : ℝ) / 2 ^ 18) ^ (2 ^ j) ≤ 1 / 2 ^ 18 := by
    calc ((1 : ℝ) / 2 ^ 18) ^ (2 ^ j) ≤ (1 / 2 ^ 18) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.one_le_two_pow)
      _ = 1 / 2 ^ 18 := pow_one _
  generalize hydef : ((1 : ℝ) / 2 ^ 18) ^ (2 ^ j) = y at hxj hFsp hFc hsq hyc
  have hy0 : 0 < y := by rw [← hydef]; positivity
  by_cases hxy : x ≤ y
  · -- Crux (C) applies to `F`
    rcases hcrux W H hfree y hy0 (hyc.trans (by norm_num)) F hFsp with ⟨T, hTF, hTc, hTsp⟩ |
        ⟨β, hβ⟩
    · exfalso
      apply hQj1
      refine ⟨?_, T, hTF.trans hFS, ?_, ?_⟩ <;> rw [hsq]
      · exact pow_le_pow_left₀ hx0.le hxy 2
      · exact hTsp
      · -- `(y²)^t |S| ≤ y^{a+t}|S| ≤ y^a |F| ≤ |T|`
        have h1 : (y ^ 2) ^ t ≤ y ^ (a + t) := by
          rw [← pow_mul]
          exact pow_le_pow_of_le_one hy0.le (hyc.trans (by norm_num)) (by omega)
        have h2 : y ^ (a + t) * S.card ≤ y ^ a * F.card := by
          rw [pow_add, mul_assoc]; exact mul_le_mul_of_nonneg_left hFc (by positivity)
        have := mul_le_mul_of_nonneg_right h1 hS0
        linarith
    · right
      obtain ⟨hk2, hkx, hky⟩ := l1_kbounds hx0 (by linarith) hxy (hyc.trans (by norm_num))
      have hkm : ((⌈1 / Real.sqrt y⌉₊ : ℕ) : ℝ) ≤ β.m := by
        have : ⌈1 / Real.sqrt y⌉₊ ≤ β.m := Nat.ceil_le.2 β.len
        exact_mod_cast this
      have hw := l1_width (a := a) (t := t) (A := A) hy0 (by linarith) hky (by omega) hFc hS0
      refine ⟨⌈1 / Real.sqrt y⌉₊, by exact_mod_cast hk2, hkx, ⟨β.m, β.B, hkm,
        fun i => (β.sub i).trans hFS, fun i => hw.trans (β.wid i), β.disj⟩, ?_⟩
      rcases hβ with h | h
      · exact Or.inl fun i j hij => h i j hij
      · exact Or.inr fun i j hij => h i j hij
  · -- `y < x`: `F` is `x`-sparse
    push Not at hxy
    left
    refine ⟨F, hFS, le_trans ?_ hFc, Or.inl (sparse_mono_param (G := H) hFsp hxy.le)⟩
    apply mul_le_mul_of_nonneg_right _ hS0
    calc x ^ A ≤ x ^ (2 * t) := pow_le_pow_of_le_one hx0.le hx1 (by omega)
      _ = (x ^ 2) ^ t := by rw [pow_mul]
      _ ≤ y ^ t := pow_le_pow_left₀ (by positivity) hxj t

/-- a P7-free graph has P̄7-free complement -/
theorem compl_free_p7 (hfree : Free G P7) : Free Gᶜ P7ᶜ := by
  rintro ⟨f, hinj, -, hadj⟩
  apply hfree
  refine ⟨f, hinj, fun i => mem_univ _, fun i j => ?_⟩
  have h := hadj i j
  rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj] at h
  by_cases hij : i = j
  · subst hij
    simp only [SimpleGraph.irrefl]
  · have hf : f i ≠ f j := fun e => hij (hinj e)
    constructor
    · intro hG; by_contra hp; exact (h.2 ⟨hij, hp⟩).2 hG
    · intro hp; by_contra hG; exact (h.1 ⟨hf, hG⟩).2 hp

/-- **Proof of Theorem A** (paper, §8). The polynomial Rödl property for P̄7-free graphs, with
exponent `3A`, gives EH(P7) with `τ = 1/((3A+1)(3A+2))`. -/
theorem eh_of_polyRodl_p7 {A : ℕ}
    (hR : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P7ᶜ → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        ∃ T : Finset W, ε ^ (3 * A) * Fintype.card W ≤ T.card ∧ Restricted H ε T) : EHforP7 := by
  obtain ⟨N, hN⟩ : ∃ N, N = (3 * A + 1) * (3 * A + 2) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; positivity
  refine ⟨((N : ℕ) : ℝ)⁻¹, by positivity, fun W _ _ H _ hfree => ?_⟩
  have hfc := compl_free_p7 hfree
  obtain ⟨n, hn⟩ : ∃ n, n = Fintype.card W := ⟨_, rfl⟩
  rw [← hn]
  have hu0 : (0 : ℝ) ≤ (n : ℝ) ^ ((N : ℝ)⁻¹) := by positivity
  have hu : ((n : ℝ) ^ ((N : ℝ)⁻¹)) ^ N = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hN0
  generalize hudef : (n : ℝ) ^ ((N : ℝ)⁻¹) = u at hu0 hu ⊢
  by_cases hsmall : u < 2
  · -- small graphs: one or two vertices suffice
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · refine ⟨univ, Or.inl fun a _ b _ hab => absurd (Finset.card_le_one.1 (by
        rw [card_univ, ← hn]; omega) a (mem_univ _) b (mem_univ _)) hab, ?_⟩
      rw [card_univ, ← hn]
      by_contra h
      push Not at h
      have : (n : ℝ) < u ^ N := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ N := by
              rcases Nat.eq_zero_or_pos n with h0 | h0
              · rw [h0]; simp [hN0]
              · exact pow_le_pow_right₀ (by exact_mod_cast h0) (Nat.one_le_iff_ne_zero.2 hN0)
          _ < u ^ N := pow_lt_pow_left₀ h (Nat.cast_nonneg _) hN0
      linarith
    · obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by rw [← hn]; omega)
      have hc : ({a, b} : Finset W).card = 2 := card_pair hab
      by_cases hadj : H.Adj a b
      · refine ⟨{a, b}, Or.inl ?_, by rw [hc]; push_cast; linarith⟩
        intro x hx y hy hxy
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hadj
        · exact H.adj_symm hadj
        · exact absurd rfl hxy
      · refine ⟨{a, b}, Or.inr ?_, by rw [hc]; push_cast; linarith⟩
        intro x hx y hy hxy
        simp only [mem_insert, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hadj
        · exact fun h => hadj (H.adj_symm h)
        · exact absurd rfl hxy
  push Not at hsmall
  -- large graphs: `ε = 1/z`, `z = u^{3A+2} = n^{1/(3A+1)}`
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = u ^ (3 * A + 2) := ⟨_, rfl⟩
  have hz4 : 2 * u ≤ z := by
    rw [hz, pow_succ]
    have : (2 : ℝ) ≤ u ^ (3 * A + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (3 * A + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ u ^ (3 * A + 1) := pow_le_pow_left₀ (by norm_num) hsmall _
    nlinarith
  have hzpos : 0 < z := by linarith
  have hzn : z ^ (3 * A + 1) = n := by
    rw [hz, ← pow_mul, ← hu, hN]; ring
  have hε0 : 0 < 1 / z := by positivity
  have hε2 : 1 / z < 1 / 2 := by
    rw [div_lt_div_iff₀ hzpos (by norm_num)]; linarith
  obtain ⟨T, hTc, hTr⟩ := hR W Hᶜ hfc (1 / z) hε0 hε2
  rw [← hn] at hTc
  have hTz : z ≤ T.card := by
    have e : (1 / z) ^ (3 * A) * (n : ℝ) = z := by
      rw [← hzn, pow_succ, one_div_pow]; field_simp
    linarith
  have hεT : 1 ≤ 1 / z * T.card := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hzpos]; linarith
  have hbound : ∀ I : Finset W, (T.card : ℝ) ≤ (1 / z * T.card + 1) * I.card → u ≤ I.card := by
    intro I hI
    have h1 : (T.card : ℝ) ≤ (2 * (1 / z * T.card)) * I.card := by nlinarith
    have h2 : (T.card : ℝ) ≤ (2 / z) * T.card * I.card := by
      have e : 2 * (1 / z * (T.card : ℝ)) * I.card = (2 / z) * T.card * I.card := by ring
      linarith
    have hTpos : (0 : ℝ) < T.card := lt_of_lt_of_le hzpos hTz
    have h3 : z / 2 ≤ I.card := by
      have : (1 : ℝ) ≤ (2 / z) * I.card := by
        have := h2
        rw [mul_assoc, mul_comm (T.card : ℝ), ← mul_assoc] at this
        nlinarith
      rw [div_le_iff₀ (by norm_num)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hzpos] at this
      linarith
    linarith
  rcases hTr with hs | hs
  · obtain ⟨I, -, hIst, hIc⟩ := greedy_stable (H := Hᶜ) (1 / z * T.card) T.card T rfl hs
    refine ⟨I, Or.inl fun a ha b hb hab => ?_, hbound I hIc⟩
    by_contra h
    exact hIst a ha b hb hab ((SimpleGraph.compl_adj H a b).2 ⟨hab, h⟩)
  · obtain ⟨I, -, hIst, hIc⟩ := greedy_stable (H := Hᶜᶜ) (1 / z * T.card) T.card T rfl hs
    refine ⟨I, Or.inr fun a ha b hb hab h => ?_, hbound I hIc⟩
    apply hIst a ha b hb hab
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    exact ⟨hab, fun h' => h'.2 h⟩

/-- **Theorem 8.3** (paper): the polynomial Rödl property for P̄7-free graphs. -/
theorem polyRodl_p7 {A : ℕ} (hA : 1 ≤ A)
    (hL1 : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Free H P7ᶜ → ∀ x : ℝ, 0 < x → x < 1 / 2 → ∀ S : Finset W,
        (∃ F ⊆ S, x ^ A * S.card ≤ F.card ∧ Restricted H x F) ∨
        (∃ k : ℕ, 2 ≤ k ∧ (k : ℝ) * x ≤ 1 ∧
          ∃ β : Blockade S k (S.card / (k : ℝ) ^ A), β.IsComplete H ∨ β.IsAnticomplete H))
    (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hfree : Free H P7ᶜ) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ T : Finset W, ε ^ (3 * A) * Fintype.card W ≤ T.card ∧ Restricted H ε T := by
  rw [← card_univ]
  by_cases h : ∃ F ⊆ (univ : Finset W), ε ^ (2 * A) * (univ : Finset W).card ≤ F.card ∧
      ∃ T ⊆ F, ε ^ A * F.card ≤ T.card ∧ Restricted H ε T
  · obtain ⟨F, -, hFc, T, -, hTc, hTr⟩ := h
    refine ⟨T, le_trans ?_ hTc, hTr⟩
    have := mul_le_mul_of_nonneg_left hFc (by positivity : (0 : ℝ) ≤ ε ^ A)
    rw [show 3 * A = A + 2 * A by ring, pow_add, mul_assoc]; exact this
  · push Not at h
    obtain ⟨T, -, hTc, hTr⟩ := c01_lemma2 (G := H) (S := univ) hA hε0 (by linarith)
      (fun F hF hFc => by
        rcases hL1 W H hfree ε hε0 hε F with ⟨F', hF', hF'c, hF'r⟩ | hb
        · exact absurd hF'r (h F hF hFc F' hF' hF'c)
        · exact hb)
    exact ⟨T, hTc, hTr⟩

/-- **EH(P7) from its displayed inputs.** Rödl's theorem for P̄7, NSS V 3.1 for P7,
    the comb lemma and EH(P6) imply the Erdős–Hajnal property of P7. -/
theorem erdos_hajnal_P7_of_inputs (hR : RodlCoP7) (hP : NssPath7) (hC : NssComb)
    (hE : EHforP6) : EHforP7 := by
  obtain ⟨a, ha⟩ := crux_P7 hR hP hC hE
  obtain ⟨A, hA, hL1⟩ := c01_lemma1_p7 hR hP ha
  exact eh_of_polyRodl_p7 (A := A) fun W _ _ H _ hfree ε hε0 hε =>
    polyRodl_p7 hA hL1 W H hfree ε hε0 hε

/-- NSS V statement 3.1 for `P7`, from the general sparse-path theorem
    `EHP6.nss_path` proved in the base project. -/
theorem nss_path7_proof : NssPath7 := by
  intro y hy hy7 V _ _ G _ S hsp hfree
  exact nss_path 7 (by norm_num) y hy (by norm_num at hy7 ⊢; linarith) G S hsp hfree

/-- **EH(P7) from Rödl's theorem for P̄7, the comb lemma and EH(P6).** -/
theorem erdos_hajnal_P7_of_cited (hR : RodlCoP7) (hC : NssComb) (hE : EHforP6) : EHforP7 :=
  erdos_hajnal_P7_of_inputs hR nss_path7_proof hC hE

/-- EH(P7) with EH(P6) supplied by the base project, which itself rests on the three
    literature axioms `rodl_coP6`, `eh_P5`, `nss_comb`. -/
theorem erdos_hajnal_P7_of_rodl (hR : RodlCoP7) : EHforP7 :=
  erdos_hajnal_P7_of_cited hR nss_comb erdos_hajnal_P6

#print axioms ehOn_P6_of_EHforP6
#print axioms lightHom_P7
#print axioms crux_P7
#print axioms c01_lemma1_p7
#print axioms erdos_hajnal_P7_of_inputs
#print axioms nss_path7_proof
#print axioms erdos_hajnal_P7_of_cited
#print axioms erdos_hajnal_P7_of_rodl
end AllPathsLocal
