import AllPathsContract

/-!
# The final comb oracle from the contract `T_(s-2)`

Main paper, Section "The final comb oracle", for an arbitrary path order
`s = n + 3`. A comb in a graph whose complement has no induced `P_s` supplies the
rooted `P_(s-2)` exclusion for the vertices of the other teeth; the Tooth contract
`T_(s-2)` applied to every tooth gives the variable-scale local oracle. The comb
itself is extracted by `EHP6.comb_extract` from the cited comb lemma `EHP6.NssComb`.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The comb supplies the rooted `P_(n+1)` exclusion: a rooted induced path of the
    complement from `u` into the tooth `Y`, prefixed by the special vertex `v` and the
    tooth's own root `a`, would be an induced path on `n + 3` vertices. -/
theorem comb_rooted_gen (n : ℕ) (hfree : CoPathFree (n + 3) G)
    {v a u : V} {Y : Finset V}
    (hva : ¬ G.Adj v a) (hY : ∀ z ∈ Y, G.Adj v z ∧ G.Adj a z)
    (hvu : G.Adj v u) (hau : ¬ G.Adj a u) : RootedPathFree G (n + 1) Y u := by
  rintro ⟨p, i, hi, hp, hp0, htail⟩
  have he : i = 0 := Fin.ext hi
  subst he
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
  exact hfree ⟨_, hpath⟩

theorem gen_tooth_order {x y l S C : ℝ} {E : ℕ} (hx : 0 < x) (hx1 : x ≤ 1) (hxy : x ≤ y)
    (hl0 : 0 < l) (hlx : l ≤ 1 / x ^ 2) (hS : 1 / x ^ (2 * E + 18) ≤ S)
    (hC : y ^ 4 * S / l ^ 2 ≤ C) : 1 / (x ^ 2) ^ E ≤ C := by
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
  have h2 : 1 / (x ^ 2) ^ E ≤ x ^ 8 * S := by
    have e : (x ^ 2) ^ E = x ^ (2 * E) := (pow_mul x 2 E).symm
    rw [e, div_le_iff₀ (by positivity)]
    have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < x ^ (2 * E + 18))).mp hS
    have h4 : x ^ (2 * E + 18) ≤ x ^ (2 * E + 8) := pow_le_pow_of_le_one hx.le hx1 (by omega)
    have h5 : S * x ^ (2 * E + 18) ≤ S * x ^ (2 * E + 8) := mul_le_mul_of_nonneg_left h4 hS0.le
    have e2 : x ^ 8 * S * x ^ (2 * E) = S * x ^ (2 * E + 8) := by ring
    rw [e2]
    linarith
  exact h2.trans (h1.trans hC)

theorem gen_width_clean {l S C Ac : ℝ} {A d : ℕ} (hl : 1 ≤ l) (hS : 0 ≤ S)
    (hC : S / l ^ 6 ≤ C) (hA : (1 / l) ^ A * C ≤ Ac) : S / l ^ (d + A + 6) ≤ Ac := by
  have hl0 : 0 < l := by linarith
  refine le_trans ?_ hA
  have h1 : (1 / l) ^ A * (S / l ^ 6) ≤ (1 / l) ^ A * C :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  refine le_trans ?_ h1
  have e : (1 / l) ^ A * (S / l ^ 6) = S / l ^ (A + 6) := by
    rw [one_div_pow, div_mul_div_comm, one_mul, ← pow_add]
  rw [e]
  exact div_le_div_of_nonneg_left hS (pow_pos hl0 _) (pow_le_pow_right₀ hl (by omega))

theorem gen_width_restricted {l z S C W : ℝ} {e : ℕ} (hl : 0 < l) (hz0 : 0 < z)
    (hzl : z ≤ 1 / l) (hS : 0 ≤ S) (hC : S / l ^ 6 ≤ C)
    (hW : z ^ e * C ≤ W) : z ^ (e + 6) * S ≤ W := by
  refine le_trans ?_ hW
  have h1 : z ^ 6 ≤ (1 / l) ^ 6 := pow_le_pow_left₀ hz0.le hzl 6
  rw [one_div_pow] at h1
  have h2 : z ^ 6 * S ≤ 1 / l ^ 6 * S := mul_le_mul_of_nonneg_right h1 hS
  have h3 : z ^ 6 * S ≤ C := by
    have e1 : 1 / l ^ 6 * S = S / l ^ 6 := by ring
    linarith
  have h4 : z ^ e * (z ^ 6 * S) ≤ z ^ e * C := mul_le_mul_of_nonneg_left h3 (by positivity)
  have e2 : z ^ (e + 6) * S = z ^ e * (z ^ 6 * S) := by ring
  linarith

theorem gen_width_blockade {l K S C : ℝ} {A d : ℕ} (hl : 1 ≤ l) (hK : l ≤ K) (hS : 0 ≤ S)
    (hC : S / l ^ 6 ≤ C) : S / K ^ (d + A + 6) ≤ C / K ^ d := by
  have hl0 : 0 < l := by linarith
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have h1 : S / K ^ 6 ≤ C :=
    (div_le_div_of_nonneg_left hS (by positivity) (pow_le_pow_left₀ hl0.le hK 6)).trans hC
  have h2 : S / K ^ 6 / K ^ d ≤ C / K ^ d :=
    div_le_div_of_nonneg_right h1 (pow_nonneg hK0.le _)
  have e : S / K ^ 6 / K ^ d = S / K ^ (6 + d) := by
    rw [div_div, ← pow_add]
  rw [e] at h2
  refine le_trans ?_ h2
  exact div_le_div_of_nonneg_left hS (pow_pos hK0 _) (pow_le_pow_right₀ hK1 (by omega))

/-- The comb oracle from comb data and the contract `T_(n+1)`. -/
theorem comb_from_data_gen (n : ℕ) (hfree : CoPathFree (n + 3) G)
    {A e c k d E : ℕ} {η : ℝ} (hT : LowerTooth G (n + 1) A e c k d E η)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1 / 2 ^ 64) (hyη : y ≤ η)
    {S : Finset V} (hS : 1 / x ^ (2 * E + 18) ≤ (S.card : ℝ))
    (D : EHP6.CombData G S x y) :
    OracleBlockade G S x y (2 * c + 2 * k + 2) (d + A + 6) ∨
      OracleRestricted G S x y (2 * c + 2 * k + 2) (e + 6) := by
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
  have hroot : ∀ i, ∀ u ∈ U i, RootedPathFree G (n + 1) (Y i) u := by
    intro i u hu
    obtain ⟨j, hj, huj⟩ := mem_biUnion.1 hu
    have hji : j ≠ i := (mem_filter.1 hj).2
    refine comb_rooted_gen n hfree (v := D.v) (a := D.a i) (D.ha i).2 ?_ ?_ ?_
    · intro z hz
      exact ⟨(mem_filter.1 (D.hC i hz)).2, D.hcomp i z hz⟩
    · exact (mem_filter.1 (D.hC j huj)).2
    · exact D.hanti i j (Ne.symm hji) u huj
  have hfine : x ^ 2 ≤ 1 / (D.ℓ : ℝ) := by
    rw [le_div_iff₀ hlpos]
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)).mp D.hℓx
    linarith
  have hly : 1 / (D.ℓ : ℝ) ≤ y := by
    rw [div_le_iff₀ hlpos]
    have h := (div_le_iff₀ hy0).mp D.hℓy
    linarith
  have hcoarse : 1 / (D.ℓ : ℝ) ≤ η := hly.trans hyη
  have hxcap : (1 : ℝ) / x ^ 2 ≤ 1 / x ^ (2 * c + 2 * k + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
      (pow_le_pow_of_le_one hx.le hx1 (by omega))
  have T := fun i => hT (U i) (Y i) (x ^ 2) (1 / (D.ℓ : ℝ)) (hout i) (hroot i)
    (by positivity) hfine hcoarse
    (gen_tooth_order hx hx1 hxy hlpos D.hℓx hS (D.hsize i))
  by_cases hall : ∀ i, ∃ Ai ⊆ Y i, (1 / (D.ℓ : ℝ)) ^ A * (Y i).card ≤ (Ai.card : ℝ) ∧
      FullOrSmall G (U i) (x ^ 2) Ai
  · left
    choose Ac hAsub hAsize hAprop using hall
    refine ⟨D.ℓ, D.hℓy, D.hℓx.trans hxcap, ⟨D.ℓ, Ac, le_rfl, fun i => (hAsub i).trans (hYS i),
      fun i => gen_width_clean hl1 hS0 (hfrac i) (hAsize i),
      fun i j h => disjoint_of_subset_left (hAsub i)
        (disjoint_of_subset_right (hAsub j) (D.hdisj i j h))⟩, fun i j hij => ?_⟩
    have mem_U : ∀ i j, i ≠ j → ∀ w ∈ Ac i, w ∈ U j := fun i j h w hw =>
      mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, h⟩, hAsub i hw⟩
    have conv : ∀ i j, i ≠ j → ∀ w ∈ Ac i, Ac j ⊆ EHP6.nbrs G w (Ac j) ∨
        ((EHP6.nbrs G w (Ac j)).card : ℝ) < x ^ 2 / 4 * (Ac j).card := by
      intro i j h w hw
      rcases hAprop j w (mem_U i j h w hw) with h' | h'
      · exact Or.inl fun z hz => mem_filter.2 ⟨hz, h' z hz⟩
      · exact Or.inr (by linarith)
    rcases EHP6.pair_lemma G (Ac i) (Ac j) (x ^ 2 / 4) (by positivity) (conv i j hij)
      (conv j i (Ne.symm hij)) with h | h
    · exact Or.inl h
    · refine Or.inr (EHP6.weaklySparse_mono ?_ h)
      nlinarith
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rcases T i with ⟨Ai, hA, hAsize, hAprop⟩ | ⟨z, hz1, hz2, W, hWY, hWsize, hWres⟩ |
      ⟨K, hKlow, hKup, γ, _, hγ⟩
    · exact absurd hAprop (hi Ai hA hAsize)
    · right
      have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hz1
      refine ⟨z, ?_, hz2.trans hly, W, hWY.trans (hYS i),
        gen_width_restricted hlpos hz0 hz2 hS0 (hfrac i) hWsize, hWres⟩
      refine le_trans ?_ hz1
      have e1 : (x ^ 2) ^ c = x ^ (2 * c) := (pow_mul x 2 c).symm
      rw [e1]
      exact pow_le_pow_of_le_one hx.le hx1 (by omega)
    · left
      have hKl : (D.ℓ : ℝ) ≤ K := by
        have e1 : 1 / (1 / (D.ℓ : ℝ)) = (D.ℓ : ℝ) := by field_simp
        rw [e1] at hKlow
        exact hKlow
      refine ⟨K, D.hℓy.trans hKl, ?_, γ.mono (hYS i) le_rfl
        (gen_width_blockade hl1 hKl hS0 (hfrac i)), fun a b hab => ?_⟩
      · refine hKup.trans ?_
        have e1 : (x ^ 2) ^ k = x ^ (2 * k) := (pow_mul x 2 k).symm
        rw [e1]
        exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
          (pow_le_pow_of_le_one hx.le hx1 (by omega))
      · have hxx : x ^ 2 ≤ x := by nlinarith
        rcases lt_or_gt_of_ne hab with hlt | hlt
        · rcases hγ a b hlt with h | h
          · exact Or.inl h
          · exact Or.inr (EHP6.weaklySparse_mono hxx (EHP6.weaklySparse_of_sparseTo h))
        · rcases hγ b a hlt with h | h
          · exact Or.inl (fun p hp q hq => G.adj_symm (h q hq p hp))
          · exact Or.inr (EHP6.weaklySparse_mono hxx
              (EHP6.weaklySparse_symm (EHP6.weaklySparse_of_sparseTo h)))

/-- **The final local oracle** for graphs with no induced `P_(n+3)` in the
    complement, from the cited comb lemma and the contract `T_(n+1)`. -/
theorem comb_oracle_gen (hcomb : EHP6.NssComb) (n : ℕ) (hfree : CoPathFree (n + 3) G)
    {A e c k d E : ℕ} {η : ℝ} (hT : LowerTooth G (n + 1) A e c k d E η) :
    LocalOracle G (min η (1 / 2 ^ 64)) 4 (2 * c + 2 * k + 2) (d + A + 6) (e + 6)
      (2 * E + 18) := by
  intro x y hx hxy hyy S hsp hS
  have hy : y ≤ 1 / 2 ^ 64 := hyy.trans (min_le_right _ _)
  have hyη : y ≤ η := hyy.trans (min_le_left _ _)
  have hx1 : x ≤ 1 := (hxy.trans hy).trans (by norm_num)
  have hS18 : 1 / x ^ 18 ≤ (S.card : ℝ) := by
    refine le_trans ?_ hS
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_of_le_one hx.le hx1 (by omega)
  rcases EHP6.comb_extract hcomb hx hxy hy S hsp hS18 with h | h | hD
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨D⟩ := hD
    exact Or.inr (Or.inr (comb_from_data_gen n hfree hT hx hxy hy hyη hS D))

#print axioms comb_rooted_gen
#print axioms comb_from_data_gen
#print axioms comb_oracle_gen
end AllPathsLocal
