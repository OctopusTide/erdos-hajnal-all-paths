import AllPathsFrontierPasses

/-!
# The RPq frontier purification, graph part

Main paper, Lemma "RPq frontier purification" (and its RP6 instance), with all
scalar side conditions displayed as hypotheses. Blocks `Z_1, …, Z_m` in `Y` carry
recorded root families `R_j` with: (I) every root has RPq into the original `Y` and
is complete to its own block; (II) every vertex of a later block has RP(q-1) into
each earlier block; (III) along every increasing path of originally non-complete
pairs, each earlier index has a recorded root separating it from each later index.
Three lower Tooth calls (two with RP(q-1) roots, one with RP(q-2) roots) either give
an early output or, after the two preparatory passes and the offending-pair pass, a
directed semisparse blockade of `r₀` blocks.
-/

namespace AllPathsLocal

open Finset Classical

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1600000 in
theorem rpq_frontier_core (n : ℕ) {A e c k d E : ℕ} {η₀ : ℝ}
    (hT1 : LowerTooth G (n + 2) A e c k d E η₀) (hT2 : LowerTooth G (n + 1) A e c k d E η₀)
    {m r₀ : ℕ} (Z R : Fin m → Finset V) {U Y : Finset V}
    (hZY : ∀ i, Z i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hRU : ∀ i, R i ⊆ U) (hRc : ∀ i, (R i).card ≤ m)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n + 3) Y u)
    (hrootfull : ∀ j, ∀ r ∈ R j, ∀ v ∈ Z j, G.Adj r v)
    (hII : ∀ i j, i < j → ∀ v ∈ Z j, RootedPathFree G (n + 2) (Z i) v)
    (hIII : ∀ (N : ℕ) (f : Fin N → Fin m), StrictMono f →
      (∀ a b : Fin N, a.val + 1 = b.val → ¬ EHP6.Complete G (Z (f a)) (Z (f b))) →
      ∀ a b, a < b → ∃ u ∈ R (f a), RootSeparates G u (Z (f a)) (Z (f b)))
    {a₀ a₁ η τ Wmin w β β' : ℝ}
    (hw : w = (1 / (m : ℝ)) ^ A) (hm : 0 < m)
    (ha₀ : 0 < a₀) (ha₀m : a₀ ≤ 1 / (m : ℝ)) (ha₁ : 0 < a₁) (ha₁m : a₁ ≤ 1 / (m : ℝ))
    (hmη : 1 / (m : ℝ) ≤ η₀) (hη : 0 < η)
    (hWpos : 0 < Wmin) (hWmin : ∀ i, Wmin ≤ ((Z i).card : ℝ))
    (hord1 : 1 / a₀ ^ E ≤ Wmin) (hord2 : 1 / a₁ ^ E ≤ w * Wmin)
    (hord3 : 1 / a₁ ^ E ≤ 13 * (w * (w * Wmin)) / 16)
    (hb2 : (m : ℝ) * (a₀ / 4 / η / w + a₁ / 4) ≤ 1 / 8) (hb2' : (m : ℝ) ^ 2 * η ≤ w / 16)
    (hβθ : a₀ / 4 ≤ β * (13 * w / 16)) (hβ : 2 * β ≤ 1)
    (hb3 : (m : ℝ) * (β / (1 / 2) / w + a₁ / 4) ≤ 1 / 8)
    (hβ'β : β ≤ β' * (13 * w / 16)) (hβ'1 : β' ≤ 1) (hβ'τ : (r₀ : ℝ) * β' ≤ τ)
    (hr₀ : 2 ≤ r₀) (hr₀m : r₀ * r₀ ≤ m) :
    (∃ i, ToothEarly G (Z i) a₀ (1 / (m : ℝ)) e c k d) ∨
    (∃ j, ∃ B ⊆ Z j, w * (Z j).card ≤ (B.card : ℝ) ∧
      ToothEarly G B a₁ (1 / (m : ℝ)) e c k d) ∨
    (∃ j, ∃ C ⊆ Z j, 13 * (w * (w * (Z j).card)) / 16 ≤ (C.card : ℝ) ∧
      ToothEarly G C a₁ (1 / (m : ℝ)) e c k d) ∨
    ∃ γ : EHP6.Blockade Y r₀ (13 * (w * (13 * (w * (w * Wmin)) / 16)) / 16 / r₀),
      γ.m = r₀ ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨ EHP6.SparseTo G τ (γ.B j) (γ.B i) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwpos : 0 < w := by rw [hw]; positivity
  have hβ0 : 0 < β := by
    by_contra h
    push Not at h
    have : β * (13 * w / 16) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  have hβ'0 : 0 < β' := by
    by_contra h
    push Not at h
    have : β' * (13 * w / 16) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  have hβ1 : β ≤ 1 := by linarith
  by_cases h1 : ∃ i, ToothEarly G (Z i) a₀ (1 / (m : ℝ)) e c k d
  · exact Or.inl h1
  right
  -- pass 1: every later original vertex gets a frozen type toward `B i`
  obtain ⟨later, hlaterdef⟩ : ∃ later : Fin m → Finset V,
      later = fun i => (Finset.univ.filter (fun j => i < j)).biUnion Z := ⟨_, rfl⟩
  have hlater_mem : ∀ i j, i < j → ∀ v ∈ Z j, v ∈ later i := fun i j hij v hv => by
    rw [hlaterdef]
    exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hij⟩, hv⟩
  have hlater_elim : ∀ i, ∀ u ∈ later i, ∃ j, i < j ∧ u ∈ Z j := fun i u hu => by
    rw [hlaterdef] at hu
    obtain ⟨j, hj, huj⟩ := mem_biUnion.mp hu
    exact ⟨j, (mem_filter.mp hj).2, huj⟩
  have hpass1 : ∀ i, ∃ B ⊆ Z i, w * (Z i).card ≤ (B.card : ℝ) ∧
      FullOrSmall G (later i) a₀ B := by
    intro i
    have hlout : ∀ u ∈ later i, u ∉ Z i := by
      intro u hu hui
      obtain ⟨j, hij, huj⟩ := hlater_elim i u hu
      exact Finset.disjoint_left.mp (hdisj (ne_of_lt hij)) hui huj
    have hlfree : ∀ u ∈ later i, RootedPathFree G (n + 2) (Z i) u := by
      intro u hu
      obtain ⟨j, hij, huj⟩ := hlater_elim i u hu
      exact hII i j hij u huj
    rcases hT1 (later i) (Z i) a₀ (1 / (m : ℝ)) hlout hlfree ha₀ ha₀m hmη
      (hord1.trans (hWmin i)) with hclean | hearly
    · rw [hw]; exact hclean
    · exact absurd ⟨i, hearly⟩ h1
  choose B hBZ hBsize hBfull using hpass1
  have hZpos : ∀ i, (0 : ℝ) < (Z i).card := fun i => hWpos.trans_le (hWmin i)
  have hBpos : ∀ i, (0 : ℝ) < (B i).card := fun i =>
    lt_of_lt_of_le (mul_pos hwpos (hZpos i)) (hBsize i)
  have hBne : ∀ i, (B i).Nonempty := fun i => card_pos.mp (by exact_mod_cast hBpos i)
  have hBtypes : ∀ i j, i < j → ∀ v ∈ Z j, (∀ b ∈ B i, G.Adj v b) ∨
      ((EHP6.nbrs G v (B i)).card : ℝ) < a₀ / 4 * (B i).card := by
    intro i j hij v hv
    rcases hBfull i v (hlater_mem i j hij v hv) with h | h
    · exact Or.inl h
    · right
      linarith [show a₀ * ((B i).card : ℝ) / 4 = a₀ / 4 * (B i).card by ring]
  have hBdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := fun i j hij =>
    (hdisj hij).mono (hBZ i) (hBZ j)
  by_cases h2 : ∃ j, ∃ B' ⊆ Z j, w * (Z j).card ≤ (B'.card : ℝ) ∧
      ToothEarly G B' a₁ (1 / (m : ℝ)) e c k d
  · exact Or.inl h2
  right
  -- pass 2: canonical purification of good pairs, exactification of red roots
  have hpass2 : ∀ j, ∃ Cj ⊆ B j, 13 * (w * (B j).card) / 16 ≤ (Cj.card : ℝ) ∧
      (∀ i, i < j → GoodPair G B R η i j →
        (∀ v ∈ Cj, ((EHP6.nbrs G v (B i)).card : ℝ) < a₀ / 4 * (B i).card) ∨
        (∀ v ∈ Cj, ∀ b ∈ B i, G.Adj v b)) ∧
      ∀ l, j < l → ¬ GoodPair G B R η j l → ∀ r ∈ R l, ∀ v ∈ Cj, G.Adj r v := by
    intro j
    have hcall : ∀ P : Finset V, (∀ p ∈ P, p ∉ B j) →
        (∀ p ∈ P, RootedPathFree G (n + 2) (B j) p) →
        ToothEarly G (B j) a₁ (1 / (m : ℝ)) e c k d ∨
          ∃ D ⊆ B j, w * (B j).card ≤ (D.card : ℝ) ∧ FullOrSmall G P a₁ D := by
      intro P hPout hPfree
      have hord : 1 / a₁ ^ E ≤ ((B j).card : ℝ) :=
        hord2.trans ((mul_le_mul_of_nonneg_left (hWmin j) hwpos.le).trans (hBsize j))
      rcases hT1 P (B j) a₁ (1 / (m : ℝ)) hPout hPfree ha₁ ha₁m hmη hord with hclean | hearly
      · right; rw [hw]; exact hclean
      · exact Or.inl hearly
    rcases rpq_pass2_column n B R (ToothEarly G (B j) a₁ (1 / (m : ℝ)) e c k d) j
        (fun i => (hBZ i).trans (hZY i)) hBdisj hRU hRc
        (fun r hr v hv => hrootfull j r hr v (hBZ j hv)) hout hfree hBne
        (fun i hij v hv => hBtypes i j hij v (hBZ j hv)) hcall hwpos (by positivity) hη ha₁.le
        hb2 hb2' with hearly | h
    · exact absurd ⟨j, B j, hBZ j, hBsize j, hearly⟩ h2
    · exact h
  choose C hCB hCsize hCgood hCred using hpass2
  have hCZ : ∀ i, C i ⊆ Z i := fun i => (hCB i).trans (hBZ i)
  have hCsizeZ : ∀ i, 13 * (w * (w * (Z i).card)) / 16 ≤ ((C i).card : ℝ) := by
    intro i
    have := mul_le_mul_of_nonneg_left (hBsize i) hwpos.le
    linarith [hCsize i]
  have hCpos : ∀ i, (0 : ℝ) < (C i).card := fun i => by
    have : 0 < 13 * (w * (w * ((Z i).card : ℝ))) / 16 := by
      have := hZpos i
      positivity
    linarith [hCsizeZ i]
  have hCne : ∀ i, (C i).Nonempty := fun i => card_pos.mp (by exact_mod_cast hCpos i)
  have hBsparseC : ∀ i (v : V), ((EHP6.nbrs G v (B i)).card : ℝ) < a₀ / 4 * (B i).card →
      ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card := by
    intro i v h
    have h1 : ((EHP6.nbrs G v (C i)).card : ℝ) ≤ (EHP6.nbrs G v (B i)).card := by
      exact_mod_cast card_le_card (EHP6.nbrs_mono (G := G) (hCB i))
    have h2 : a₀ / 4 * ((B i).card : ℝ) ≤ β * (13 * w / 16) * (B i).card :=
      mul_le_mul_of_nonneg_right hβθ (Nat.cast_nonneg _)
    have h3 : β * (13 * (w * (B i).card) / 16) ≤ β * (C i).card :=
      mul_le_mul_of_nonneg_left (hCsize i) hβ0.le
    linarith [show β * (13 * w / 16) * ((B i).card : ℝ) = β * (13 * (w * (B i).card) / 16) by
      ring]
  have hCtypes : ∀ i j, i < j → ∀ v ∈ Z j, (∀ b ∈ C i, G.Adj v b) ∨
      ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card := by
    intro i j hij v hv
    rcases hBtypes i j hij v hv with h | h
    · exact Or.inl fun b hb => h b (hCB i hb)
    · exact Or.inr (hBsparseC i v h)
  have hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)) := fun i j hij =>
    (hdisj hij).mono (hCZ i) (hCZ j)
  have hCredmixed : ∀ i j, i < j → MixedPair G C i j → ∀ r ∈ R j, ∀ v ∈ C i, G.Adj r v := by
    intro i j hij hmix
    by_cases hg : GoodPair G B R η i j
    · exfalso
      obtain ⟨⟨wv, hw1, hwfull⟩, ⟨v, hv, hvnot⟩⟩ := hmix
      rcases hCgood j i hij hg with hs | hf
      · exact sparse_not_complete G hβ1 (hBsparseC i wv (hs wv hw1)) hwfull
      · exact hvnot (fun b hb => hf v hv b (hCB i hb))
    · exact hCred i j hij hg
  by_cases h3 : ∃ j, ∃ C' ⊆ Z j, 13 * (w * (w * (Z j).card)) / 16 ≤ (C'.card : ℝ) ∧
      ToothEarly G C' a₁ (1 / (m : ℝ)) e c k d
  · exact Or.inl h3
  right
  -- pass 3: the offending-pair pass
  have hpass3 : ∀ j, ∃ Ej ⊆ C j, 13 * (w * (C j).card) / 16 ≤ (Ej.card : ℝ) ∧
      ∀ i, i < j → Offending G C R i j →
        Ej ⊆ SparseType G (C i) (C j) ∨ Disjoint Ej (SparseType G (C i) (C j)) := by
    intro j
    have hcall : ∀ P : Finset V, (∀ p ∈ P, p ∉ C j) →
        (∀ p ∈ P, RootedPathFree G (n + 1) (C j) p) →
        ToothEarly G (C j) a₁ (1 / (m : ℝ)) e c k d ∨
          ∃ D ⊆ C j, w * (C j).card ≤ (D.card : ℝ) ∧ FullOrSmall G P a₁ D := by
      intro P hPout hPfree
      have hmono : 13 * (w * (w * Wmin)) / 16 ≤ 13 * (w * (w * ((Z j).card : ℝ))) / 16 := by
        have s1 := mul_le_mul_of_nonneg_left (hWmin j) hwpos.le
        have s2 := mul_le_mul_of_nonneg_left s1 hwpos.le
        linarith
      have hord : 1 / a₁ ^ E ≤ ((C j).card : ℝ) := hord3.trans (hmono.trans (hCsizeZ j))
      rcases hT2 P (C j) a₁ (1 / (m : ℝ)) hPout hPfree ha₁ ha₁m hmη hord with hclean | hearly
      · right; rw [hw]; exact hclean
      · exact Or.inl hearly
    rcases rpq_pass3_column n C R (ToothEarly G (C j) a₁ (1 / (m : ℝ)) e c k d) j
        (fun i => (hCZ i).trans (hZY i)) hCdisj hRU
        (fun r hr v hv => hrootfull j r hr v (hCZ j hv)) hout hfree hCne
        (fun i l hil v hv => hCtypes i l hil v (hCZ l hv))
        (fun i hij hmix => hCredmixed i j hij hmix) hβ0.le hβ hcall hwpos ha₁.le hb3 with
        hearly | h
    · exact absurd ⟨j, C j, hCZ j, hCsizeZ j, hearly⟩ h3
    · exact h
  choose Eb hEC hEsize hEoff using hpass3
  have hEZ : ∀ i, Eb i ⊆ Z i := fun i => (hEC i).trans (hCZ i)
  have hEY : ∀ i, Eb i ⊆ Y := fun i => (hEZ i).trans (hZY i)
  have hEdisj : Pairwise (fun i j => Disjoint (Eb i) (Eb j)) := fun i j hij =>
    (hdisj hij).mono (hEZ i) (hEZ j)
  have hEwidth : ∀ i, 13 * (w * (13 * (w * (w * Wmin)) / 16)) / 16 ≤ ((Eb i).card : ℝ) := by
    intro i
    have s1 := mul_le_mul_of_nonneg_left (hWmin i) hwpos.le
    have s2 := mul_le_mul_of_nonneg_left s1 hwpos.le
    have s3 : 13 * (w * (w * Wmin)) / 16 ≤ ((C i).card : ℝ) := by linarith [hCsizeZ i]
    have s4 := mul_le_mul_of_nonneg_left s3 hwpos.le
    linarith [hEsize i]
  have hCsparseE : ∀ i (v : V), ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card →
      ((EHP6.nbrs G v (Eb i)).card : ℝ) < β' * (Eb i).card := by
    intro i v h
    have h1 : ((EHP6.nbrs G v (Eb i)).card : ℝ) ≤ (EHP6.nbrs G v (C i)).card := by
      exact_mod_cast card_le_card (EHP6.nbrs_mono (G := G) (hEC i))
    have h2 : β * ((C i).card : ℝ) ≤ β' * (13 * w / 16) * (C i).card :=
      mul_le_mul_of_nonneg_right hβ'β (Nat.cast_nonneg _)
    have h3 : β' * (13 * (w * (C i).card) / 16) ≤ β' * (Eb i).card :=
      mul_le_mul_of_nonneg_left (hEsize i) hβ'0.le
    linarith [show β' * (13 * w / 16) * ((C i).card : ℝ) = β' * (13 * (w * (C i).card) / 16) by
      ring]
  have hEtypes : ∀ i j, i < j → ∀ v ∈ Eb j, (∀ b ∈ Eb i, G.Adj v b) ∨
      ((EHP6.nbrs G v (Eb i)).card : ℝ) < β' * (Eb i).card := by
    intro i j hij v hv
    rcases hCtypes i j hij v (hEZ j hv) with h | h
    · exact Or.inl fun b hb => h b (hEC i hb)
    · exact Or.inr (hCsparseE i v h)
  -- converse type preservation: full to `E i` implies full to `C i`
  have hEC_full : ∀ i j, i < j → ∀ v ∈ Z j, (∀ b ∈ Eb i, G.Adj v b) →
      ∀ b ∈ C i, G.Adj v b := by
    intro i j hij v hv hfull
    rcases hCtypes i j hij v hv with h | h
    · exact h
    · exact absurd hfull (sparse_not_complete G hβ'1 (hCsparseE i v h))
  have hEoff' : ∀ i j, i < j → Offending G C R i j → ¬ MixedPair G Eb i j := by
    intro i j hij hoff hmix
    obtain ⟨⟨wv, hw1, hwfull⟩, ⟨v, hv, hvnot⟩⟩ := hmix
    have hwC : ∀ b ∈ C i, G.Adj wv b := hEC_full i j hij wv (hEZ j hw1) hwfull
    have hvC : ¬ ∀ b ∈ C i, G.Adj v b := fun h => hvnot (fun b hb => h b (hEC i hb))
    rcases hEoff j i hij hoff with hsub | hdis
    · exact ((mem_sparseType G).mp (hsub hw1)).2 hwC
    · exact Finset.disjoint_left.mp hdis hv ((mem_sparseType G).mpr ⟨hEC j hv, hvC⟩)
  have hEmixC : ∀ i j, i < j → MixedPair G Eb i j → MixedPair G C i j := by
    rintro i j hij ⟨⟨wv, hw1, hwfull⟩, ⟨v, hv, hvnot⟩⟩
    exact ⟨⟨wv, hEC j hw1, hEC_full i j hij wv (hEZ j hw1) hwfull⟩,
      ⟨v, hEC j hv, fun h => hvnot (fun b hb => h b (hEC i hb))⟩⟩
  have hwE0 : (0 : ℝ) ≤ 13 * (w * (13 * (w * (w * Wmin)) / 16)) / 16 := by positivity
  obtain ⟨γ, hγm, hγ⟩ : ∃ γ : EHP6.Blockade Y r₀
      (13 * (w * (13 * (w * (w * Wmin)) / 16)) / 16 / r₀), γ.m = r₀ ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (r₀ * β') (γ.B j) (γ.B i) := by
    rcases increasing_path_or_large_independent_level (fun i j => MixedPair G Eb i j) hr₀ with
      ⟨i, hpath⟩ | ⟨I, hIc, hind⟩
    · obtain ⟨_, f, hf, -, -, hlinks⟩ := increasingQPath_sequence hpath
      refine norev_path_blockade Y Eb (by omega) hEY hEdisj hβ'0.le hEwidth hEtypes f hf ?_
      intro a b c' hab hbc z hz hfullb
      by_contra hnot
      have hab' : a < b := by show a.val < b.val; omega
      obtain ⟨u, hu, hsep⟩ := hIII r₀ f hf
        (fun a' b' h' => mixed_pair_original_noncomplete G Eb Z hEZ (hlinks a' b' h')) b c' hbc
      have huz : ¬ G.Adj u z := hsep.2 z (hEZ _ hz)
      have hzCb : ∀ v ∈ C (f b), G.Adj z v :=
        hEC_full (f b) (f c') (hf hbc) z (hEZ _ hz) hfullb
      have hzCa : ¬ ∀ v ∈ C (f a), G.Adj z v := fun h => hnot (fun v hv => h v (hEC _ hv))
      have hoff : Offending G C R (f a) (f b) :=
        ⟨hEmixC _ _ (hf hab') (hlinks a b hab), f c', hf hbc, z, hEC _ hz, u, hu, huz,
          hzCb, hzCa⟩
      exact hEoff' _ _ (hf hab') hoff (hlinks a b hab)
    · have hI : r₀ ≤ I.card := by
        have hr2 : (2 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
        have hr1 : (0 : ℝ) < (r₀ : ℝ) - 1 := by linarith
        have h1 : (r₀ : ℝ) * ((r₀ : ℝ) - 1) ≤ m := by
          have : ((r₀ * r₀ : ℕ) : ℝ) ≤ m := by exact_mod_cast hr₀m
          push_cast at this
          nlinarith
        have h2 : (r₀ : ℝ) ≤ (m : ℝ) / ((r₀ : ℝ) - 1) := by
          rw [le_div_iff₀ hr1]; exact h1
        exact_mod_cast h2.trans hIc
      exact independent_level_blockade G Y Eb (by omega) hβ'0.le hwE0 hEY hEdisj hEwidth
        hEtypes I hI hind
  refine ⟨γ, hγm, fun i j hij => ?_⟩
  rcases hγ i j hij with h | h
  · exact Or.inl h
  · right
    intro v hv
    exact (h v hv).trans (mul_le_mul_of_nonneg_right hβ'τ (Nat.cast_nonneg _))

#print axioms rpq_frontier_core
end AllPathsLocal
