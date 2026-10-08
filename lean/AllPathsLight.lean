import AllPathsTemplate
import EHP6.Round2Hom

/-!
Strong wonderfulness from a forcing template (main paper, Theorem "Uniform strong
wonderfulness", first half). In a block system of a graph whose complement has no
induced path on `s` vertices, the blocks on which a vertex is lightly mixed contain
`|I|^κ` blocks that are pairwise complete or pairwise non-complete, where `κ` is an
Erdős–Hajnal exponent of a forcing template `Q`.
-/

namespace AllPathsLocal

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 1600000 in
theorem light_hom_template {α : Type} [Fintype α] [DecidableEq α] (Q : SimpleGraph α) {s : ℕ}
    (hforce : ∀ (V : Type) (F : SimpleGraph V) (_ : Lift F Q),
      ∃ p : Fin s → V, IsInducedPath F p)
    {κ : ℝ} (hQ : EHOn Q Finset.univ κ)
    (hfree : ¬ ∃ p : Fin s → V, IsInducedPath Gᶜ p)
    {ℓ : ℕ} {B : Fin ℓ → Finset V} {W : ℕ} {x : ℝ} (hS : EHP6.BlockSystem G B W x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hx : 8 * (Fintype.card α : ℝ) * x ≤ 1) (hW : 4 ≤ W) (v : V) :
    ∃ R ⊆ EHP6.lightIdx G B W v,
      ((∀ i ∈ R, ∀ j ∈ R, i ≠ j → EHP6.Complete G (B i) (B j)) ∨
       (∀ i ∈ R, ∀ j ∈ R, i ≠ j → ¬ EHP6.Complete G (B i) (B j))) ∧
      ((EHP6.lightIdx G B W v).card : ℝ) ^ κ ≤ R.card := by
  classical
  have hcsymm : ∀ A C : Finset V, EHP6.Complete G A C → EHP6.Complete G C A :=
    fun A C h c hc a ha => G.adj_symm (h a ha c hc)
  let H : SimpleGraph (Fin ℓ) :=
    { Adj := fun i j => i ≠ j ∧ ¬ EHP6.Complete G (B i) (B j)
      symm := ⟨fun i j h => ⟨h.1.symm, fun hc => h.2 (hcsymm _ _ hc)⟩⟩
      loopless := ⟨fun i h => h.1 rfl⟩ }
  have hH : ∀ i j, H.Adj i j ↔ (i ≠ j ∧ ¬ EHP6.Complete G (B i) (B j)) := fun i j => Iff.rfl
  obtain ⟨I, hI⟩ : ∃ I, I = EHP6.lightIdx G B W v := ⟨_, rfl⟩
  rw [← hI]
  have hno : ¬ EmbedsOn Q Finset.univ H I := by
    rintro ⟨f, hinj0, hmem0, hadj0⟩
    have hinj : Function.Injective f := fun a c h =>
      hinj0 (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ c)) h
    have hmem : ∀ a, f a ∈ I := fun a => hmem0 a (Finset.mem_univ a)
    have hadj : ∀ a c, H.Adj (f a) (f c) ↔ Q.Adj a c := fun a c =>
      hadj0 a (Finset.mem_univ a) c (Finset.mem_univ c)
    have hlight : ∀ a, 0 < (EHP6.nbrs G v (B (f a))).card ∧
        ((EHP6.nbrs G v (B (f a))).card : ℝ) < W / 2 := by
      intro a
      have h := hmem a
      rw [hI] at h
      simp only [EHP6.lightIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    have hbex : ∀ a, ∃ u, u ∈ B (f a) ∧ G.Adj v u := by
      intro a
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (hlight a).1
      exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
    choose b hbB hvb using hbex
    have hsparse : ∀ a c, Q.Adj a c → ∀ u ∈ B (f c),
        ((EHP6.nbrs G u (B (f a))).card : ℝ) ≤ x * W := by
      intro a c hac u hu
      have hHac := (hadj a c).mpr hac
      have hsp := (hS.sparse_of_not_complete hHac.1 hHac.2).2 u hu
      rw [hS.card] at hsp
      exact hsp
    have hcompl : ∀ a c, a ≠ c → ¬ Q.Adj a c → EHP6.Complete G (B (f a)) (B (f c)) := by
      intro a c hne hnq
      by_contra hc
      exact hnq ((hadj a c).mp ⟨fun h => hne (hinj h), hc⟩)
    have hWr : (4 : ℝ) ≤ W := by exact_mod_cast hW
    have hx0 := hS.hx
    have hxW : (0 : ℝ) ≤ x * W := mul_nonneg hx0.le (Nat.cast_nonneg _)
    have hzex : ∀ T : Finset α, ∃ z : α → V, ∀ a ∈ T,
        z a ∈ B (f a) ∧ ¬ G.Adj v (z a) ∧ z a ≠ v ∧ (∀ c, Q.Adj a c → ¬ G.Adj (b c) (z a)) ∧
        ∀ c ∈ T, Q.Adj a c → ¬ G.Adj (z c) (z a) := by
      intro T
      induction T using Finset.induction_on with
      | empty => exact ⟨fun _ => v, fun a ha => absurd ha (Finset.notMem_empty _)⟩
      | insert a0 T ha0 ih =>
        obtain ⟨z, hz⟩ := ih
        obtain ⟨Bi, hBi⟩ : ∃ Bi, Bi = B (f a0) := ⟨_, rfl⟩
        let bad : α → Finset V := fun c =>
          if Q.Adj a0 c then
            EHP6.nbrs G (b c) Bi ∪ (if c ∈ T then EHP6.nbrs G (z c) Bi else ∅)
          else ∅
        have hbadc : ∀ c, ((bad c).card : ℝ) ≤ 2 * (x * W) := by
          intro c
          by_cases hc : Q.Adj a0 c
          · have h1 := hsparse a0 c hc (b c) (hbB c)
            rw [← hBi] at h1
            by_cases hcT : c ∈ T
            · have h2 := hsparse a0 c hc (z c) (hz c hcT).1
              rw [← hBi] at h2
              have h3 : (bad c).card ≤
                  (EHP6.nbrs G (b c) Bi).card + (EHP6.nbrs G (z c) Bi).card := by
                simp only [bad, if_pos hc, if_pos hcT]
                exact Finset.card_union_le _ _
              have h3' : ((bad c).card : ℝ) ≤
                  (EHP6.nbrs G (b c) Bi).card + (EHP6.nbrs G (z c) Bi).card := by
                exact_mod_cast h3
              linarith
            · have h3 : (bad c).card ≤ (EHP6.nbrs G (b c) Bi).card := by
                simp only [bad, if_pos hc, if_neg hcT, Finset.union_empty]
                exact le_rfl
              have h3' : ((bad c).card : ℝ) ≤ (EHP6.nbrs G (b c) Bi).card := by
                exact_mod_cast h3
              linarith
          · have h0 : bad c = ∅ := by simp only [bad, if_neg hc]
            rw [h0, Finset.card_empty, Nat.cast_zero]
            linarith
        obtain ⟨Bad, hBaddef⟩ : ∃ Bad : Finset V, Bad = insert v (Finset.univ.biUnion bad) :=
          ⟨_, rfl⟩
        have hBadc : (Bad.card : ℝ) ≤ 1 + (Fintype.card α : ℝ) * (2 * (x * W)) := by
          have h1 : Bad.card ≤ (Finset.univ.biUnion bad).card + 1 := by
            rw [hBaddef]
            exact Finset.card_insert_le _ _
          have h2 : (Finset.univ.biUnion bad).card ≤ ∑ c : α, (bad c).card :=
            Finset.card_biUnion_le
          have h3 : ∑ c : α, ((bad c).card : ℝ) ≤ ∑ _c : α, 2 * (x * W) :=
            Finset.sum_le_sum (fun c _ => hbadc c)
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
          have h1' : (Bad.card : ℝ) ≤ ((Finset.univ.biUnion bad).card : ℝ) + 1 := by
            exact_mod_cast h1
          have h2' : ((Finset.univ.biUnion bad).card : ℝ) ≤ ∑ c : α, ((bad c).card : ℝ) := by
            exact_mod_cast h2
          linarith
        obtain ⟨C, hCdef⟩ : ∃ C : Finset V, C = Bi \ EHP6.nbrs G v Bi := ⟨_, rfl⟩
        have hCc : (W : ℝ) / 2 < C.card := by
          have hsub : EHP6.nbrs G v Bi ⊆ Bi := Finset.filter_subset _ _
          have h1 : C.card = Bi.card - (EHP6.nbrs G v Bi).card := by
            rw [hCdef]
            exact Finset.card_sdiff_of_subset hsub
          have h2 : (EHP6.nbrs G v Bi).card ≤ Bi.card := Finset.card_le_card hsub
          have h3 : (C.card : ℝ) = (Bi.card : ℝ) - (EHP6.nbrs G v Bi).card := by
            rw [h1, Nat.cast_sub h2]
          have h4 : Bi.card = W := by rw [hBi]; exact hS.card _
          have h5 := (hlight a0).2
          rw [← hBi] at h5
          rw [h3, h4]
          linarith
        have hBadW : (Bad.card : ℝ) ≤ W / 2 := by
          have h1 : (Fintype.card α : ℝ) * (2 * (x * W)) =
              (8 * (Fintype.card α : ℝ) * x) * ((W : ℝ) / 4) := by ring
          have h2 : (8 * (Fintype.card α : ℝ) * x) * ((W : ℝ) / 4) ≤ 1 * ((W : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right hx (by linarith)
          linarith
        obtain ⟨w, hwC, hwBad⟩ : ∃ w ∈ C, w ∉ Bad := by
          by_contra hcon
          push Not at hcon
          have h1 : C.card ≤ Bad.card := Finset.card_le_card hcon
          have h2 : (C.card : ℝ) ≤ Bad.card := by exact_mod_cast h1
          linarith
        rw [hCdef] at hwC
        obtain ⟨hwBi, hwnv⟩ := Finset.mem_sdiff.mp hwC
        have hvw : ¬ G.Adj v w := fun h => hwnv (Finset.mem_filter.mpr ⟨hwBi, h⟩)
        rw [hBaddef] at hwBad
        have hwv : w ≠ v := fun h => hwBad (h ▸ Finset.mem_insert_self _ _)
        have hwbad : ∀ c, w ∉ bad c := fun c h =>
          hwBad (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, h⟩))
        have hwb : ∀ c, Q.Adj a0 c → ¬ G.Adj (b c) w := by
          intro c hc hadjw
          apply hwbad c
          simp only [bad, if_pos hc]
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwBi, hadjw⟩)
        have hwz : ∀ c ∈ T, Q.Adj a0 c → ¬ G.Adj (z c) w := by
          intro c hcT hc hadjw
          apply hwbad c
          simp only [bad, if_pos hc, if_pos hcT]
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwBi, hadjw⟩)
        refine ⟨Function.update z a0 w, ?_⟩
        have hup0 : Function.update z a0 w a0 = w := Function.update_self _ _ _
        have hupT : ∀ c ∈ T, Function.update z a0 w c = z c := fun c hc =>
          Function.update_of_ne (fun h : c = a0 => ha0 (by rw [← h]; exact hc)) _ _
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | haT
        · rw [hup0]
          refine ⟨by rw [← hBi]; exact hwBi, hvw, hwv, hwb, ?_⟩
          intro c hc hac
          rcases Finset.mem_insert.mp hc with rfl | hcT
          · exact absurd hac Q.irrefl
          · rw [hupT c hcT]
            exact hwz c hcT hac
        · rw [hupT a haT]
          obtain ⟨h1, h2, h3, h4, h5⟩ := hz a haT
          refine ⟨h1, h2, h3, h4, ?_⟩
          intro c hc hac
          rcases Finset.mem_insert.mp hc with rfl | hcT
          · rw [hup0]
            exact fun h => hwz a haT (Q.adj_symm hac) (G.adj_symm h)
          · rw [hupT c hcT]
            exact h5 c hcT hac
    obtain ⟨z, hz⟩ := hzex Finset.univ
    have hzB : ∀ a, z a ∈ B (f a) := fun a => (hz a (Finset.mem_univ a)).1
    have hvz : ∀ a, ¬ G.Adj v (z a) := fun a => (hz a (Finset.mem_univ a)).2.1
    have hzv : ∀ a, z a ≠ v := fun a => (hz a (Finset.mem_univ a)).2.2.1
    have hbz : ∀ a c, Q.Adj a c → ¬ G.Adj (b c) (z a) := fun a =>
      (hz a (Finset.mem_univ a)).2.2.2.1
    have hzz : ∀ a c, Q.Adj a c → ¬ G.Adj (z c) (z a) := fun a c h =>
      (hz a (Finset.mem_univ a)).2.2.2.2 c (Finset.mem_univ c) h
    have hblk : ∀ a c (u w : V), a ≠ c → u ∈ B (f a) → w ∈ B (f c) → u ≠ w := by
      intro a c u w hac hu hw huw
      have hd := hdisj (f a) (f c) (fun h => hac (hinj h))
      rw [huw] at hu
      exact Finset.disjoint_left.mp hd hu hw
    let L : Lift Gᶜ Q :=
      { v := v
        z := z
        b := b
        hvz := fun a => (SimpleGraph.compl_adj G v (z a)).mpr ⟨(hzv a).symm, hvz a⟩
        hvb := fun a h => ((SimpleGraph.compl_adj G v (b a)).mp h).2 (hvb a)
        hvb_ne := fun a => G.ne_of_adj (hvb a)
        hz_inj := by
          intro a c h
          by_contra hac
          exact hblk a c _ _ hac (hzB a) (hzB c) h
        hb_inj := by
          intro a c h
          by_contra hac
          exact hblk a c _ _ hac (hbB a) (hbB c) h
        hzb_ne := by
          intro a c
          by_cases hac : a = c
          · subst hac
            exact fun h => hvz a (by rw [h]; exact hvb a)
          · exact hblk a c _ _ hac (hzB a) (hbB c)
        hzz := by
          intro a c hac
          constructor
          · intro h
            by_contra hq
            exact ((SimpleGraph.compl_adj G _ _).mp h).2
              (hcompl a c hac hq (z a) (hzB a) (z c) (hzB c))
          · intro hq
            exact (SimpleGraph.compl_adj G _ _).mpr
              ⟨hblk a c _ _ hac (hzB a) (hzB c), fun h => hzz a c hq (G.adj_symm h)⟩
        hzb := by
          intro a c hac
          constructor
          · intro h
            by_contra hq
            exact ((SimpleGraph.compl_adj G _ _).mp h).2
              (hcompl a c hac hq (z a) (hzB a) (b c) (hbB c))
          · intro hq
            exact (SimpleGraph.compl_adj G _ _).mpr
              ⟨hblk a c _ _ hac (hzB a) (hbB c), fun h => hbz a c hq (G.adj_symm h)⟩
        hbb := by
          intro a c h
          by_contra hq
          by_cases hac : a = c
          · subst hac
            exact Gᶜ.irrefl h
          · exact ((SimpleGraph.compl_adj G _ _).mp h).2
              (hcompl a c hac hq (b a) (hbB a) (b c) (hbB c)) }
    exact hfree (hforce V Gᶜ L)
  obtain ⟨T, hTI, hThom, hTc⟩ := hQ (Fin ℓ) H I hno
  refine ⟨T, hTI, ?_, hTc⟩
  rcases hThom with hc | hs
  · right
    intro i hi j hj hij
    exact ((hH i j).mp (hc i hi j hj hij)).2
  · left
    intro i hi j hj hij
    by_contra hcomp
    exact hs i hi j hj ((hH i j).mpr ⟨hij, hcomp⟩)

#print axioms light_hom_template
end AllPathsLocal
