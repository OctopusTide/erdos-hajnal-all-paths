import RP5Tooth
import EHP6.Round1

/-!
The final comb oracle for the seven-vertex path (main paper, "The final comb oracle",
at `s = 7`, where the final rooted order is `s - 2 = 5`). The comb itself is the one
already extracted, without any forbidden-subgraph hypothesis, by `EHP6.comb_extract`.
Each tooth is passed to the kernel-checked `rp5_tooth`. Nothing here asserts EH(P7).
-/

namespace AllPathsLocal

open Finset

/-- The seven-vertex path. -/
def P7 : SimpleGraph (Fin 7) := EHP6.pathGraph' 7

/-- An induced path of the complement is an induced copy of the complement path. -/
theorem compl_contains_of_inducedPath {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (p : Fin n → V)
    (hp : IsInducedPath Gᶜ p) :
    EHP6.ContainsInduced G (EHP6.pathGraph' n)ᶜ Finset.univ := by
  refine ⟨p, hp.1, fun i => Finset.mem_univ _, fun i j => ?_⟩
  have h := hp.2 i j
  rw [SimpleGraph.compl_adj] at h
  rw [SimpleGraph.compl_adj]
  simp only [EHP6.pathGraph', SimpleGraph.fromRel_adj]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : p i ≠ p j := fun e => hij (hp.1 e)
    constructor
    · intro hG
      exact ⟨hij, fun hc => (h.mpr hc.2).2 hG⟩
    · rintro ⟨_, hnc⟩
      by_contra hG
      exact hnc ⟨hij, h.mp ⟨hne, hG⟩⟩

/-- The comb supplies the rooted P5 exclusion: a rooted induced complement-P5 from
    `u` into the tooth `Y`, prefixed by the special vertex `v` and the tooth's own
    root `a`, would be an induced complement-P7. -/
theorem comb_rooted_p5 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : EHP6.Free G P7ᶜ)
    {v a u : V} {Y : Finset V}
    (hva : ¬ G.Adj v a) (hY : ∀ z ∈ Y, G.Adj v z ∧ G.Adj a z)
    (hvu : G.Adj v u) (hau : ¬ G.Adj a u) : RootedP5Free G Y u := by
  rintro ⟨p, hp, hp0, htail⟩
  have hvne : v ≠ a := by
    rintro rfl
    exact hau hvu
  have hvp : ∀ i, G.Adj v (p i) := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hp0]
      exact hvu
    · exact (hY _ (htail i hi)).1
  have hanew : ∀ i, a ≠ p i := by
    intro i he
    exact hva (he ▸ hvp i)
  have hahead : ∀ i, Gᶜ.Adj a (p i) ↔ i = 0 := by
    intro i
    by_cases hi : i = 0
    · have hau' : a ≠ u := by
        rintro rfl
        exact hva hvu
      simp [SimpleGraph.compl_adj, hi, hp0, hau', hau]
    · simp [SimpleGraph.compl_adj, hi, (hY _ (htail i hi)).2]
  have hvnew : ∀ i, v ≠ p i := fun i => G.ne_of_adj (hvp i)
  have hedge : Gᶜ.Adj v a := (G.compl_adj v a).mpr ⟨hvne, hva⟩
  have hnochord : ∀ i, ¬ Gᶜ.Adj v (p i) := fun i h => ((G.compl_adj _ _).mp h).2 (hvp i)
  have hpath := prefix_two_inducedPath Gᶜ p v a hp hanew hahead hvne hvnew hedge hnochord
  exact hfree (compl_contains_of_inducedPath G _ hpath)

/-- Blockade outcome of the variable-scale oracle: actual integer length
    `1/y ≤ K ≤ x^(-c)`, width `|S|/K^e`, pairs complete or weakly `x`-sparse. -/
def OracleBlockade {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (x y : ℝ) (c e : ℕ) : Prop :=
  ∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x ^ c ∧
    ∃ β : EHP6.Blockade S K (S.card / (K : ℝ) ^ e), β.IsSemisparse G x

/-- Restricted outcome of the variable-scale oracle with its ACTUAL scale `z`. -/
def OracleRestricted {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (x y : ℝ) (c e : ℕ) : Prop :=
  ∃ z : ℝ, x ^ c ≤ z ∧ z ≤ y ∧ ∃ T ⊆ S, z ^ e * S.card ≤ T.card ∧ EHP6.Restricted G (z ^ 4) T

theorem p7_tooth_fraction {y l S C : ℝ} (hy0 : 0 < y) (hl : 1 / y ≤ l) (hS : 0 ≤ S)
    (hC : y ^ 4 * S / l ^ 2 ≤ C) : S / l ^ 6 ≤ C := by
  have hl0 : 0 < l := lt_of_lt_of_le (by positivity) hl
  have hyl : 1 ≤ y * l := by
    rw [div_le_iff₀ hy0] at hl
    linarith
  refine le_trans ?_ hC
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : 1 ≤ (y * l) ^ 4 := one_le_pow₀ hyl
  have h5 : y ^ 4 * S * l ^ 6 = (y * l) ^ 4 * (S * l ^ 2) := by ring
  rw [h5]
  have h6 : 0 ≤ S * l ^ 2 := by positivity
  nlinarith

theorem p7_tooth_order {x y l S C : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hl0 : 0 < l) (hlx : l ≤ 1 / x ^ 2) (hS : 1 / x ^ 1208 ≤ S)
    (hC : y ^ 4 * S / l ^ 2 ≤ C) : 1 / (x ^ 2) ^ 600 ≤ C := by
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hlx2 : l * x ^ 2 ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hlx
    exact hlx
  have hlx4 : l ^ 2 * x ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ l * x ^ 2) hlx2 2
    have e : (l * x ^ 2) ^ 2 = l ^ 2 * x ^ 4 := by ring
    rw [e] at h
    simpa using h
  have hxy4 : x ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hx.le hxy 4
  have h1 : x ^ 8 * S ≤ y ^ 4 * S / l ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have e : x ^ 8 * S * l ^ 2 = (l ^ 2 * x ^ 4) * (x ^ 4 * S) := by ring
    rw [e]
    have h2 : (l ^ 2 * x ^ 4) * (x ^ 4 * S) ≤ 1 * (x ^ 4 * S) :=
      mul_le_mul_of_nonneg_right hlx4 (by positivity)
    have h3 : x ^ 4 * S ≤ y ^ 4 * S := mul_le_mul_of_nonneg_right hxy4 hS0.le
    linarith
  have h2 : 1 / (x ^ 2) ^ 600 ≤ x ^ 8 * S := by
    have e : (x ^ 2) ^ 600 = x ^ 1200 := by rw [← pow_mul]
    rw [e, div_le_iff₀ (by positivity)]
    have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < x ^ 1208)).mp hS
    have e2 : x ^ 8 * S * x ^ 1200 = S * x ^ 1208 := by ring
    rw [e2]
    exact h3
  exact h2.trans (h1.trans hC)

theorem p7_width_clean {l S C A : ℝ} (hl : 1 ≤ l) (hS : 0 ≤ S) (hC : S / l ^ 6 ≤ C)
    (hA : (1 / l) ^ 26 * C ≤ A) : S / l ^ 70 ≤ A := by
  have hl0 : 0 < l := by linarith
  refine le_trans ?_ hA
  have h1 : (1 / l) ^ 26 * (S / l ^ 6) ≤ (1 / l) ^ 26 * C :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  refine le_trans ?_ h1
  have e : (1 / l) ^ 26 * (S / l ^ 6) = S / l ^ 32 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left hS (by positivity) (pow_le_pow_right₀ hl (by norm_num))

theorem p7_width_restricted {l S C W : ℝ} (hl : 0 < l) (hC : S / l ^ 6 ≤ C)
    (hW : (1 / l) ^ 18 * C ≤ W) : (1 / l) ^ 24 * S ≤ W := by
  refine le_trans ?_ hW
  have h1 : (1 / l) ^ 18 * (S / l ^ 6) ≤ (1 / l) ^ 18 * C :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  refine le_trans (le_of_eq ?_) h1
  field_simp

theorem p7_width_blockade {l K S C : ℝ} (hl : 1 ≤ l) (hK : l ≤ K) (hS : 0 ≤ S)
    (hC : S / l ^ 6 ≤ C) : S / K ^ 70 ≤ C / K ^ 64 := by
  have hl0 : 0 < l := by linarith
  have hK0 : 0 < K := by linarith
  have h1 : S / K ^ 6 ≤ C :=
    (div_le_div_of_nonneg_left hS (by positivity) (pow_le_pow_left₀ hl0.le hK 6)).trans hC
  have h2 : S / K ^ 6 / K ^ 64 ≤ C / K ^ 64 :=
    div_le_div_of_nonneg_right h1 (by positivity)
  have e : S / K ^ 6 / K ^ 64 = S / K ^ 70 := by
    rw [div_div, ← pow_add]
  rw [e] at h2
  exact h2

/-- The final comb oracle at `s = 7`: every comb in a complement-P7-free graph
    gives a weakly `x`-semisparse blockade of actual length in `[1/y, x^(-280)]` and
    width `|S|/K^70`, or a `z^4`-restricted set of size `z^24 |S|` at the ACTUAL
    scale `z = 1/l`, where `l` is the comb's length. -/
theorem comb_from_data_p7 {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hfree : EHP6.Free G P7ᶜ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64)
    {S : Finset V} (hS : 1 / x ^ 1208 ≤ (S.card : ℝ))
    (D : EHP6.CombData G S x y) :
    OracleBlockade G S x y 280 70 ∨ OracleRestricted G S x y 2 24 := by
  classical
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hx1 : x ≤ 1 := (hxy.trans hy).trans (by norm_num)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hl64 : (2 : ℝ) ^ 64 ≤ D.ℓ := EHP6.cl_ell64 hy0 hy D.hℓy
  have hlpos : (0 : ℝ) < D.ℓ := lt_of_lt_of_le (by positivity) hl64
  have hl1 : (1 : ℝ) ≤ D.ℓ := le_trans (by norm_num) hl64
  let Y : Fin D.ℓ → Finset V := D.C
  let U : Fin D.ℓ → Finset V := fun i => (univ.filter (fun j => j ≠ i)).biUnion Y
  have hYS : ∀ i, Y i ⊆ S := fun i => (D.hC i).trans (filter_subset _ _)
  have hfrac : ∀ i, (S.card : ℝ) / (D.ℓ : ℝ) ^ 6 ≤ (Y i).card := fun i =>
    p7_tooth_fraction hy0 D.hℓy hS0 (D.hsize i)
  have hout : ∀ i, ∀ u ∈ U i, u ∉ Y i := by
    intro i u hu huY
    obtain ⟨j, hj, huj⟩ := mem_biUnion.1 hu
    exact Finset.disjoint_left.mp (D.hdisj j i (mem_filter.1 hj).2) huj huY
  have hroot : ∀ i, ∀ u ∈ U i, RootedP5Free G (Y i) u := by
    intro i u hu
    obtain ⟨j, hj, huj⟩ := mem_biUnion.1 hu
    have hji : j ≠ i := (mem_filter.1 hj).2
    refine comb_rooted_p5 G hfree (v := D.v) (a := D.a i) (D.ha i).2 ?_ ?_ ?_
    · intro z hz
      exact ⟨(mem_filter.1 (D.hC i hz)).2, D.hcomp i z hz⟩
    · exact (mem_filter.1 (D.hC j huj)).2
    · exact D.hanti i j (Ne.symm hji) u huj
  have hfine : x ^ 2 ≤ 1 / (D.ℓ : ℝ) := by
    rw [le_div_iff₀ hlpos]
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)).mp D.hℓx
    linarith
  have hcoarse : 1 / (D.ℓ : ℝ) ≤ 1 / 2 ^ 16 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact le_trans (by norm_num) hl64
  have T := fun i => rp5_tooth G (U i) (Y i) (x ^ 2) (1 / (D.ℓ : ℝ)) (hout i) (hroot i)
    (by positivity) hfine hcoarse
    (p7_tooth_order hx hxy hlpos D.hℓx hS (D.hsize i))
  by_cases hall : ∀ i, ∃ A ⊆ Y i, (1 / (D.ℓ : ℝ)) ^ 26 * (Y i).card ≤ (A.card : ℝ) ∧
      FullOrSmall G (U i) (x ^ 2) A
  · left
    choose A hAsub hAsize hAprop using hall
    refine ⟨D.ℓ, D.hℓy, ?_, ⟨D.ℓ, A, le_rfl, fun i => (hAsub i).trans (hYS i),
      fun i => p7_width_clean hl1 hS0 (hfrac i) (hAsize i),
      fun i j h => disjoint_of_subset_left (hAsub i)
        (disjoint_of_subset_right (hAsub j) (D.hdisj i j h))⟩, fun i j hij => ?_⟩
    · refine D.hℓx.trans ?_
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_of_le_one hx.le hx1 (by norm_num)
    · have mem_U : ∀ i j, i ≠ j → ∀ w ∈ A i, w ∈ U j := fun i j h w hw =>
        mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, h⟩, hAsub i hw⟩
      have conv : ∀ i j, i ≠ j → ∀ w ∈ A i, A j ⊆ EHP6.nbrs G w (A j) ∨
          ((EHP6.nbrs G w (A j)).card : ℝ) < x ^ 2 / 4 * (A j).card := by
        intro i j h w hw
        rcases hAprop j w (mem_U i j h w hw) with h' | h'
        · exact Or.inl fun z hz => mem_filter.2 ⟨hz, h' z hz⟩
        · exact Or.inr (by linarith)
      rcases EHP6.pair_lemma G (A i) (A j) (x ^ 2 / 4) (by positivity) (conv i j hij)
        (conv j i (Ne.symm hij)) with h | h
      · exact Or.inl h
      · refine Or.inr (EHP6.weaklySparse_mono ?_ h)
        nlinarith
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rcases T i with ⟨A, hA, hAsize, hAprop⟩ | ⟨W, hWY, hWsize, hWdeg⟩ |
      ⟨K, hKlow, hKup, γ, _, hγ⟩
    · exact absurd hAprop (hi A hA hAsize)
    · right
      refine ⟨1 / (D.ℓ : ℝ), hfine, ?_, W, hWY.trans (hYS i),
        p7_width_restricted hlpos (hfrac i) hWsize, ?_⟩
      · rw [div_le_iff₀ hlpos]
        have h := (div_le_iff₀ hy0).mp D.hℓy
        linarith
      · have he0 : (0 : ℝ) ≤ (1 / (D.ℓ : ℝ)) ^ 4 := by positivity
        rcases hWdeg with hdeg | hdeg
        · left
          intro v hv
          have h1 := hdeg v hv
          have h2 : (1 / (D.ℓ : ℝ)) ^ 4 * ((W.card : ℝ) - 1) ≤ (1 / (D.ℓ : ℝ)) ^ 4 * W.card :=
            mul_le_mul_of_nonneg_left (by linarith) he0
          unfold EHP6.nbrs
          rw [filter_card_classical]
          rw [filter_card_classical] at h1
          linarith
        · right
          intro v hv
          have h1 := hdeg v hv
          have h2 : (1 / (D.ℓ : ℝ)) ^ 4 * ((W.card : ℝ) - 1) ≤ (1 / (D.ℓ : ℝ)) ^ 4 * W.card :=
            mul_le_mul_of_nonneg_left (by linarith) he0
          unfold EHP6.nbrs
          rw [filter_card_classical]
          rw [filter_card_classical] at h1
          linarith
    · left
      have hKl : (D.ℓ : ℝ) ≤ K := by
        have e : 1 / (1 / (D.ℓ : ℝ)) = (D.ℓ : ℝ) := by field_simp
        rw [e] at hKlow
        exact hKlow
      refine ⟨K, D.hℓy.trans hKl, ?_, γ.mono (hYS i) le_rfl
        (p7_width_blockade hl1 hKl hS0 (hfrac i)), fun a b hab => ?_⟩
      · have e : (x ^ 2) ^ 140 = x ^ 280 := by rw [← pow_mul]
        rw [e] at hKup
        exact hKup
      · have hxx : x ^ 2 ≤ x := by nlinarith
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · rcases hγ a b hlt with h | h
          · exact Or.inl h
          · exact Or.inr (EHP6.weaklySparse_mono hxx (EHP6.weaklySparse_of_sparseTo h))
        · rcases hγ b a hlt with h | h
          · exact Or.inl (fun p hp q hq => G.adj_symm (h q hq p hp))
          · exact Or.inr (EHP6.weaklySparse_mono hxx
              (EHP6.weaklySparse_symm (EHP6.weaklySparse_of_sparseTo h)))

/-- The final local oracle for complement-P7-free graphs, from the comb lemma of
    NSS VII (the cited `EHP6.NssComb`) and the RP5 Tooth: a `y^3`-sparse set is
    `2y^4`-sparse, or has the directed sparse pair, or a semisparse blockade, or a
    restricted set at its actual floating scale. -/
theorem comb_oracle_p7 {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcomb : EHP6.NssComb)
    (hfree : EHP6.Free G P7ᶜ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1 / 2 ^ 64) (S : Finset V) (hsp : EHP6.Sparse G (y ^ 3) S)
    (hS : 1 / x ^ 1208 ≤ (S.card : ℝ)) :
    EHP6.Sparse G (2 * y ^ 4) S ∨ EHP6.Outcome3 G S x y ∨
      OracleBlockade G S x y 280 70 ∨ OracleRestricted G S x y 2 24 := by
  have hx1 : x ≤ 1 := (hxy.trans hy).trans (by norm_num)
  have hS18 : 1 / x ^ 18 ≤ (S.card : ℝ) := by
    refine le_trans ?_ hS
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_of_le_one hx.le hx1 (by norm_num)
  rcases EHP6.comb_extract hcomb hx hxy hy S hsp hS18 with h | h | hD
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨D⟩ := hD
    exact Or.inr (Or.inr (comb_from_data_p7 hfree hx hxy hy hS D))

#print axioms compl_contains_of_inducedPath
#print axioms comb_rooted_p5
#print axioms comb_from_data_p7
#print axioms comb_oracle_p7
end AllPathsLocal
