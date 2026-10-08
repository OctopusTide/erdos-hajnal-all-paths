import AllPathsContract
import RP5PathSelection

/-!
# The purification passes of the RPq frontier lemma

Main paper, Appendix "The RPq recurrence in the same hereditary ambient class",
subsections "Two preparatory passes" and "Offending pairs and the RP(q-2) pass".
`column_purify` is the common deletion step: representatives are sent to a lower
Tooth call (kept abstract as `hcall`), and the opposite frozen type is deleted for
each selected pair, simultaneously with the exactification of red roots.
`rpq_pass2_column` is the canonical RP(q-1) purification of good pairs, and
`rpq_pass3_column` is the offending-pair pass with RP(q-2) representatives obtained
by the two-root prefix `r - z`. No connectedness of blocks is used.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Early outcomes of a Tooth call: restricted at an actual scale, or a blockade. -/
def ToothEarly (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (x y : ℝ)
    (e c k d : ℕ) : Prop :=
  (∃ z : ℝ, x ^ c ≤ z ∧ z ≤ y ∧ ∃ W ⊆ Y, z ^ e * Y.card ≤ (W.card : ℝ) ∧
    EHP6.Restricted G (z ^ 4) W) ∨
  (∃ K : ℕ, 1 / y ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / x ^ k ∧
    ∃ γ : EHP6.Blockade Y K ((Y.card : ℝ) / (K : ℝ) ^ d), γ.m = K ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G x (γ.B j) (γ.B i))

/-- The common deletion step of the purification passes. -/
theorem column_purify {ι : Type} [DecidableEq ι] (Bj : Finset V) (Sp : ι → Finset V)
    (sel : Finset ι) (T : Finset V) {r' : ℕ} {w δ₀ ξ η : ℝ} (Early : Prop)
    (hcall : ∀ P : Finset V, (∀ p ∈ P, p ∉ Bj) → (∀ p ∈ P, RootedPathFree G r' Bj p) →
      Early ∨ ∃ D ⊆ Bj, w * Bj.card ≤ (D.card : ℝ) ∧ FullOrSmall G P ξ D)
    (hrep : ∀ i ∈ sel, ∃ p, p ∉ Bj ∧ RootedPathFree G r' Bj p ∧
      ((EHP6.nbrs G p (Sp i)).card : ℝ) ≤ δ₀ * Bj.card ∧ ∀ v ∈ Bj \ Sp i, G.Adj p v)
    (hred : ∀ r ∈ T, ((Bj \ EHP6.nbrs G r Bj).card : ℝ) ≤ η * Bj.card)
    (hw : 0 < w) (hδ₀ : 0 ≤ δ₀) (hξ : 0 ≤ ξ) (hη : 0 ≤ η)
    (hgoodBudget : (sel.card : ℝ) * (δ₀ / w + ξ / 4) ≤ 1 / 8)
    (hredBudget : (T.card : ℝ) * η ≤ w / 16) :
    Early ∨ ∃ E ⊆ Bj, 13 * (w * Bj.card) / 16 ≤ (E.card : ℝ) ∧
      (∀ i ∈ sel, E ⊆ Sp i ∨ Disjoint E (Sp i)) ∧ ∀ r ∈ T, ∀ v ∈ E, G.Adj r v := by
  have hrep' : ∀ i : {i // i ∈ sel}, ∃ p, p ∉ Bj ∧ RootedPathFree G r' Bj p ∧
      ((EHP6.nbrs G p (Sp i.1)).card : ℝ) ≤ δ₀ * Bj.card ∧ ∀ v ∈ Bj \ Sp i.1, G.Adj p v :=
    fun i => hrep i.1 i.2
  choose p hp1 hp2 hp3 hp4 using hrep'
  obtain ⟨P, hPdef⟩ : ∃ P : Finset V, P = sel.attach.image p := ⟨_, rfl⟩
  have hPmem : ∀ i : {i // i ∈ sel}, p i ∈ P := fun i => by
    rw [hPdef]; exact mem_image_of_mem p (mem_attach _ _)
  have hPout : ∀ q ∈ P, q ∉ Bj := by
    intro q hq
    rw [hPdef] at hq
    obtain ⟨i, -, rfl⟩ := mem_image.mp hq
    exact hp1 i
  have hPfree : ∀ q ∈ P, RootedPathFree G r' Bj q := by
    intro q hq
    rw [hPdef] at hq
    obtain ⟨i, -, rfl⟩ := mem_image.mp hq
    exact hp2 i
  rcases hcall P hPout hPfree with h | ⟨D, hDB, hDc, hDfull⟩
  · exact Or.inl h
  right
  have hB0 : (0 : ℝ) ≤ Bj.card := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  have hsmall : ∀ i ∈ sel.attach,
      ((EHP6.nbrs G (p i) (Sp i.1)).card : ℝ) ≤ δ₀ / w * D.card := by
    intro i _
    have h1 : δ₀ * (Bj.card : ℝ) = δ₀ / w * (w * Bj.card) := by field_simp
    have h2 : δ₀ / w * (w * Bj.card) ≤ δ₀ / w * D.card :=
      mul_le_mul_of_nonneg_left hDc (div_nonneg hδ₀ hw.le)
    linarith [hp3 i]
  have hcomplete : ∀ i ∈ sel.attach, ∀ v ∈ D \ Sp i.1, G.Adj (p i) v := by
    intro i _ v hv
    obtain ⟨hvD, hvS⟩ := mem_sdiff.mp hv
    exact hp4 i v (mem_sdiff.mpr ⟨hDB hvD, hvS⟩)
  have hcore : ∀ i ∈ sel.attach, (∀ v ∈ D, G.Adj (p i) v) ∨
      ((EHP6.nbrs G (p i) D).card : ℝ) ≤ ξ / 4 * D.card := by
    intro i _
    rcases hDfull (p i) (hPmem i) with h | h
    · exact Or.inl h
    · right
      linarith [show ξ * (D.card : ℝ) / 4 = ξ / 4 * D.card by ring]
  have hgb : ((sel.attach).card : ℝ) * (δ₀ / w + ξ / 4) ≤ 1 / 8 := by
    rw [card_attach]; exact hgoodBudget
  have hrb : (T.card : ℝ) * η * Bj.card ≤ (D.card : ℝ) / 16 := by
    have h1 : (T.card : ℝ) * η * Bj.card ≤ w / 16 * Bj.card :=
      mul_le_mul_of_nonneg_right hredBudget hB0
    linarith [show w / 16 * (Bj.card : ℝ) = w * Bj.card / 16 by ring]
  obtain ⟨E, hED, hEc, hEt, hEr⟩ := purify_and_exactify G Bj D T sel.attach p
    (fun i => Sp i.1) (δ₀ / w) (ξ / 4) η (div_nonneg hδ₀ hw.le) (by positivity) hDB
    hsmall hcomplete hcore hred hgb hrb
  refine ⟨E, hED.trans hDB, ?_, ?_, hEr⟩
  · linarith
  · intro i hi
    exact hEt ⟨i, hi⟩ (mem_attach _ _)

/-- A blockade along an increasing path of blocks on which later vertices never
    reverse from sparse to full: each later block keeps a largest prefix-profile
    cell. -/
theorem norev_path_blockade {m n : ℕ} (Y : Finset V) (C : Fin m → Finset V) {β w : ℝ}
    (hn : 0 < n) (hCY : ∀ i, C i ⊆ Y)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) (hβ0 : 0 ≤ β)
    (hwidth : ∀ i, w ≤ ((C i).card : ℝ))
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (f : Fin n → Fin m) (hf : StrictMono f)
    (hnorev : ∀ a b c : Fin n, a.val + 1 = b.val → b < c → ∀ z ∈ C (f c),
      (∀ v ∈ C (f b), G.Adj z v) → ∀ v ∈ C (f a), G.Adj z v) :
    ∃ γ : EHP6.Blockade Y n (w / n), γ.m = n ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (n * β) (γ.B j) (γ.B i) := by
  have hc : ∀ t : Fin n, ∃ cut : Fin (t.val + 1), ∃ D ⊆ C (f t),
      ((C (f t)).card : ℝ) / (t.val + 1) ≤ D.card ∧
      ∀ z ∈ D, ∀ a : Fin t.val,
        (∀ b ∈ C (f ⟨a.val, a.isLt.trans t.isLt⟩), G.Adj z b) ↔ a.val < cut.val := by
    intro t
    let e : Fin t.val → Fin n := fun a => ⟨a.val, a.isLt.trans t.isLt⟩
    let P : V → Fin t.val → Prop := fun z a => ∀ b ∈ C (f (e a)), G.Adj z b
    have hmon : ∀ z ∈ C (f t), Antitone (P z) := by
      intro z hz
      apply antitone_predicate_of_consecutive
      intro a b hab hfull
      have hbt : e b < t := b.isLt
      exact hnorev (e a) (e b) t hab hbt z hz hfull
    exact large_uniform_prefix_cell (C (f t)) t.val P hmon
  choose cut D hDC hDc hprofile using hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : ∀ t, ((C (f t)).card : ℝ) / n ≤ (D t).card := by
    intro t
    have ht : (t.val : ℝ) + 1 ≤ n := by exact_mod_cast (show t.val + 1 ≤ n by omega)
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity) ht).trans (hDc t)
  have hDbound : ∀ t, ((C (f t)).card : ℝ) ≤ (n : ℝ) * (D t).card := by
    intro t
    simpa only [mul_comm] using (div_le_iff₀ hnR).mp (hratio t)
  let γ : EHP6.Blockade Y n (w / n) :=
    ⟨n, D, le_rfl, fun i => (hDC i).trans (hCY (f i)),
      fun i => (div_le_div_of_nonneg_right (hwidth (f i)) hnR.le).trans (hratio i),
      fun i j hij => (hdisj (fun h => hij (hf.injective h))).mono (hDC i) (hDC j)⟩
  refine ⟨γ, rfl, ?_⟩
  intro i j hij
  let a : Fin j.val := ⟨i.val, hij⟩
  have heq : (⟨a.val, a.isLt.trans j.isLt⟩ : Fin n) = i := rfl
  have hprof : ∀ z ∈ D j, (∀ b ∈ C (f i), G.Adj z b) ↔ i.val < (cut j).val := by
    intro z hz
    simpa only [heq] using hprofile j z hz a
  by_cases ht : i.val < (cut j).val
  · left
    intro b hb z hz
    exact ((hprof z hz).mpr ht b (hDC i hb)).symm
  · right
    intro z hz
    have hnot : ¬ ∀ b ∈ C (f i), G.Adj z b := fun hh => ht ((hprof z hz).mp hh)
    have hs := (htypes (f i) (f j) (hf hij) z (hDC j hz)).resolve_left hnot
    exact (sparse_type_restrict G (hDC i) hβ0 (hDbound i) hs).le

/-- The canonical RP(q-1) purification of one column: good pairs become uniform in
    their frozen type, and the roots of red later pairs become exactly complete. -/
theorem rpq_pass2_column (n : ℕ) {m : ℕ} (B R : Fin m → Finset V) {U Y : Finset V}
    {θ η w ξ : ℝ} (Early : Prop) (j : Fin m)
    (hBY : ∀ i, B i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hRU : ∀ i, R i ⊆ U) (hRc : ∀ i, (R i).card ≤ m)
    (hrootfull : ∀ r ∈ R j, ∀ v ∈ B j, G.Adj r v)
    (hout : ∀ r ∈ U, r ∉ Y) (hfree : ∀ r ∈ U, RootedPathFree G (n + 3) Y r)
    (hBne : ∀ i, (B i).Nonempty)
    (htypes : ∀ i, i < j → ∀ v ∈ B j,
      (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card)
    (hcall : ∀ P : Finset V, (∀ p ∈ P, p ∉ B j) →
      (∀ p ∈ P, RootedPathFree G (n + 2) (B j) p) →
      Early ∨ ∃ D ⊆ B j, w * (B j).card ≤ (D.card : ℝ) ∧ FullOrSmall G P ξ D)
    (hw : 0 < w) (hθ0 : 0 ≤ θ) (hη : 0 < η) (hξ : 0 ≤ ξ)
    (hb1 : (m : ℝ) * (θ / η / w + ξ / 4) ≤ 1 / 8) (hb2 : (m : ℝ) ^ 2 * η ≤ w / 16) :
    Early ∨ ∃ E ⊆ B j, 13 * (w * (B j).card) / 16 ≤ (E.card : ℝ) ∧
      (∀ i, i < j → GoodPair G B R η i j →
        (∀ v ∈ E, ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) ∨
        (∀ v ∈ E, ∀ b ∈ B i, G.Adj v b)) ∧
      ∀ l, j < l → ¬ GoodPair G B R η j l → ∀ r ∈ R l, ∀ v ∈ E, G.Adj r v := by
  obtain ⟨I, hIdef⟩ : ∃ I : Finset (Fin m),
      I = Finset.univ.filter (fun i : Fin m => i < j ∧ GoodPair G B R η i j) := ⟨_, rfl⟩
  have hI : I.card ≤ m := by
    rw [hIdef]
    simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin m)))
  obtain ⟨T, hTc, hTsmall, hTcover⟩ := red_root_union G B R η j hRc
  have hrep : ∀ i ∈ I, ∃ p, p ∉ B j ∧ RootedPathFree G (n + 2) (B j) p ∧
      ((EHP6.nbrs G p (SparseType G (B i) (B j))).card : ℝ) ≤ θ / η * (B j).card ∧
      ∀ v ∈ B j \ SparseType G (B i) (B j), G.Adj p v := by
    intro i hi
    rw [hIdef] at hi
    obtain ⟨hij, r, hr, hgood⟩ := (Finset.mem_filter.mp hi).2
    have hSB : SparseType G (B i) (B j) ⊆ B j := fun v hv => (mem_sparseType G |>.mp hv).1
    have hsparse : ∀ v ∈ SparseType G (B i) (B j),
        ((EHP6.nbrs G v (B i)).card : ℝ) ≤ θ * (B i).card := by
      intro v hv
      have hv' := (mem_sparseType G).mp hv
      exact ((htypes i hij v hv'.1).resolve_left hv'.2).le
    obtain ⟨p, hp, hnot, hsmall⟩ :=
      good_pair_representative G (B i) (B j) (SparseType G (B i) (B j)) r θ η
        (hBne i) hSB hθ0 hη hgood hsparse
    have hrU := hRU j hr
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · exact fun hpj => Finset.disjoint_left.mp (hdisj (ne_of_lt hij)) hp hpj
    · exact rooted_path_free_prefix G (n + 1) (hout r hrU) (hBY i hp) (hBY j)
        (hfree r hrU) hnot (hrootfull r hr)
    · linarith [show θ * ((B j).card : ℝ) / η = θ / η * (B j).card by ring]
    · intro v hv
      have hv' := Finset.mem_sdiff.mp hv
      have hf : ∀ b ∈ B i, G.Adj v b := by
        by_contra hn
        exact hv'.2 ((mem_sparseType G).mpr ⟨hv'.1, hn⟩)
      exact (hf _ hp).symm
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hfac : 0 ≤ θ / η / w + ξ / 4 := by
    have : 0 ≤ θ / η / w := div_nonneg (div_nonneg hθ0 hη.le) hw.le
    linarith
  have hgb : (I.card : ℝ) * (θ / η / w + ξ / 4) ≤ 1 / 8 := by
    have h1 : (I.card : ℝ) ≤ m := by exact_mod_cast hI
    exact (mul_le_mul_of_nonneg_right h1 hfac).trans hb1
  have hrb : (T.card : ℝ) * η ≤ w / 16 := by
    have h1 : (T.card : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hTc
    exact (mul_le_mul_of_nonneg_right h1 hη.le).trans hb2
  rcases column_purify (B j) (fun i => SparseType G (B i) (B j)) I T Early hcall hrep
      hTsmall hw (div_nonneg hθ0 hη.le) hξ hη.le hgb hrb with h | ⟨E, hEB, hEc, hEt, hEr⟩
  · exact Or.inl h
  right
  refine ⟨E, hEB, hEc, ?_, ?_⟩
  · intro i hij hg
    have hi : i ∈ I := by
      rw [hIdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hg⟩
    rcases hEt i hi with hsub | hnon
    · left
      intro v hv
      have hv' := (mem_sparseType G).mp (hsub hv)
      exact (htypes i hij v hv'.1).resolve_left hv'.2
    · right
      intro v hv
      by_contra hn
      exact Finset.disjoint_left.mp hnon hv ((mem_sparseType G).mpr ⟨hEB hv, hn⟩)
  · intro l hjl hn u hu v hv
    exact hEr u (hTcover l hjl hn hu) v hv

/-- An ambiguous pair `i < j` is offending if some later original vertex `z` and
    some recorded root `r` of `j` satisfy: `r` is nonadjacent to `z`, `z` is full to
    `C j`, and `z` is not full to `C i`. -/
def Offending (G : SimpleGraph V) {m : ℕ} (C R : Fin m → Finset V) (i j : Fin m) : Prop :=
  MixedPair G C i j ∧ ∃ l, j < l ∧ ∃ z ∈ C l, ∃ r ∈ R j,
    ¬ G.Adj r z ∧ (∀ v ∈ C j, G.Adj z v) ∧ ¬ ∀ b ∈ C i, G.Adj z b

/-- The offending-pair pass on one column: every offending pair becomes uniform in
    its old type. The representatives exclude rooted `P_(q-2)` by the two-root prefix. -/
theorem rpq_pass3_column (n : ℕ) {m : ℕ} (C R : Fin m → Finset V) {U Y : Finset V}
    {β w ξ : ℝ} (Early : Prop) (j : Fin m)
    (hCY : ∀ i, C i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hRU : ∀ i, R i ⊆ U)
    (hrootfull : ∀ r ∈ R j, ∀ v ∈ C j, G.Adj r v)
    (hout : ∀ r ∈ U, r ∉ Y) (hfree : ∀ r ∈ U, RootedPathFree G (n + 3) Y r)
    (hCne : ∀ i, (C i).Nonempty)
    (htypes : ∀ i l, i < l → ∀ v ∈ C l,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (hredmixed : ∀ i, i < j → MixedPair G C i j → ∀ r ∈ R j, ∀ v ∈ C i, G.Adj r v)
    (hβ0 : 0 ≤ β) (hβ : 2 * β ≤ 1)
    (hcall : ∀ P : Finset V, (∀ p ∈ P, p ∉ C j) →
      (∀ p ∈ P, RootedPathFree G (n + 1) (C j) p) →
      Early ∨ ∃ D ⊆ C j, w * (C j).card ≤ (D.card : ℝ) ∧ FullOrSmall G P ξ D)
    (hw : 0 < w) (hξ : 0 ≤ ξ)
    (hb : (m : ℝ) * (β / (1 / 2) / w + ξ / 4) ≤ 1 / 8) :
    Early ∨ ∃ E ⊆ C j, 13 * (w * (C j).card) / 16 ≤ (E.card : ℝ) ∧
      ∀ i, i < j → Offending G C R i j →
        E ⊆ SparseType G (C i) (C j) ∨ Disjoint E (SparseType G (C i) (C j)) := by
  obtain ⟨I, hIdef⟩ : ∃ I : Finset (Fin m),
      I = Finset.univ.filter (fun i : Fin m => i < j ∧ Offending G C R i j) := ⟨_, rfl⟩
  have hI : I.card ≤ m := by
    rw [hIdef]
    simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin m)))
  have hrep : ∀ i ∈ I, ∃ p, p ∉ C j ∧ RootedPathFree G (n + 1) (C j) p ∧
      ((EHP6.nbrs G p (SparseType G (C i) (C j))).card : ℝ) ≤ β / (1 / 2) * (C j).card ∧
      ∀ v ∈ C j \ SparseType G (C i) (C j), G.Adj p v := by
    intro i hi
    rw [hIdef] at hi
    obtain ⟨hij, hmix, l, hjl, z, hz, r, hr, hrz, hzfull, hznot⟩ := (Finset.mem_filter.mp hi).2
    have hil : i < l := hij.trans hjl
    have hzs := (htypes i l hil z hz).resolve_left hznot
    have hSB : SparseType G (C i) (C j) ⊆ C j := fun v hv => (mem_sparseType G |>.mp hv).1
    have hsparse : ∀ v ∈ SparseType G (C i) (C j),
        ((EHP6.nbrs G v (C i)).card : ℝ) ≤ β * (C i).card := by
      intro v hv
      have hv' := (mem_sparseType G).mp hv
      exact ((htypes i j hij v hv'.1).resolve_left hv'.2).le
    have hgood : (1 / 2 : ℝ) * (C i).card ≤ (((C i) \ EHP6.nbrs G z (C i)).card : ℝ) := by
      have hsub : EHP6.nbrs G z (C i) ⊆ C i := Finset.filter_subset _ _
      rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
      have hc0 : (0 : ℝ) ≤ (C i).card := Nat.cast_nonneg _
      nlinarith
    obtain ⟨p, hp, hnot, hsmall⟩ :=
      good_pair_representative G (C i) (C j) (SparseType G (C i) (C j)) z β (1 / 2)
        (hCne i) hSB hβ0 (by norm_num) hgood hsparse
    have hrU := hRU j hr
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · exact fun hpj => Finset.disjoint_left.mp (hdisj (ne_of_lt hij)) hp hpj
    · refine rooted_path_free_two_prefix G n (hout r hrU) (hCY l hz) (hCY i hp) (hCY j)
        ?_ ?_ (hfree r hrU) hrz hnot (hredmixed i hij hmix r hr p hp) (hrootfull r hr) hzfull
      · exact fun hzj => Finset.disjoint_left.mp (hdisj (ne_of_lt hjl)) hzj hz
      · rintro rfl
        exact Finset.disjoint_left.mp (hdisj (ne_of_lt hil)) hp hz
    · linarith [show β * ((C j).card : ℝ) / (1 / 2) = β / (1 / 2) * (C j).card by ring]
    · intro v hv
      have hv' := Finset.mem_sdiff.mp hv
      have hf : ∀ b ∈ C i, G.Adj v b := by
        by_contra hn
        exact hv'.2 ((mem_sparseType G).mpr ⟨hv'.1, hn⟩)
      exact (hf _ hp).symm
  have hfac : 0 ≤ β / (1 / 2) / w + ξ / 4 := by
    have : 0 ≤ β / (1 / 2) / w := div_nonneg (div_nonneg hβ0 (by norm_num)) hw.le
    linarith
  have hgb : (I.card : ℝ) * (β / (1 / 2) / w + ξ / 4) ≤ 1 / 8 := by
    have h1 : (I.card : ℝ) ≤ m := by exact_mod_cast hI
    exact (mul_le_mul_of_nonneg_right h1 hfac).trans hb
  rcases column_purify (η := 0) (C j) (fun i => SparseType G (C i) (C j)) I ∅ Early hcall hrep
      (fun r hr => absurd hr (Finset.notMem_empty r)) hw (div_nonneg hβ0 (by norm_num)) hξ
      le_rfl hgb (by simp; positivity) with h | ⟨E, hEC, hEc, hEt, -⟩
  · exact Or.inl h
  right
  refine ⟨E, hEC, hEc, ?_⟩
  intro i hij hoff
  exact hEt i (by rw [hIdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hoff⟩)

#print axioms column_purify
#print axioms norev_path_blockade
#print axioms rpq_pass2_column
#print axioms rpq_pass3_column
end AllPathsLocal
