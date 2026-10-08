import RP5Components
import RP5Interval
import RP5Profiles

/-! Connect the actual ordered tree frontier, recorded roots and red exactification
    to the five-vertex obstruction. There is no common root along the path. -/

namespace AllPathsLocal

theorem mixed_pair_original_noncomplete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (C Z : Fin m → Finset V) (hCZ : ∀ i, C i ⊆ Z i)
    {i j : Fin m} (hmix : MixedPair G C i j) : ¬ EHP6.Complete G (Z i) (Z j) := by
  obtain ⟨v, hv, hvnot⟩ := hmix.2
  intro hcomp
  exact hvnot (fun b hb => (hcomp b (hCZ i hb) v (hCZ j hv)).symm)

/-- For each edge a->b and each later path block c, choose a recorded root of b
    which is full on a and b and empty on c. -/
theorem mixed_path_recorded_root_law {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    (C R : Fin Z.length → Finset V) (hCZ : ∀ i, C i ⊆ Z.get i)
    (hRU : ∀ i, R i ⊆ U)
    (hrecord : ∀ j l, j < l → (∃ u ∈ U, RootSeparates G u (Z.get j) (Z.get l)) →
      ∃ u ∈ R j, RootSeparates G u (Z.get j) (Z.get l))
    (hred : ∀ i j, i < j → MixedPair G C i j → ∀ u ∈ R j, ∀ v ∈ C i, G.Adj u v)
    {n : ℕ} (f : Fin n → Fin Z.length) (hf : StrictMono f)
    (hlinks : ∀ a b : Fin n, a.val + 1 = b.val → MixedPair G C (f a) (f b)) :
    ∀ a b c : Fin n, a.val + 1 = b.val → b < c →
      ∃ u ∈ U, (∀ v ∈ C (f a), G.Adj u v) ∧
        (∀ v ∈ C (f b), G.Adj u v) ∧ ∀ v ∈ C (f c), ¬ G.Adj u v := by
  have hnon : ∀ a b : Fin n, a.val + 1 = b.val →
      ¬ EHP6.Complete G (Z.get (f a)) (Z.get (f b)) := by
    intro a b hab
    exact mixed_pair_original_noncomplete G C Z.get hCZ (hlinks a b hab)
  have hroots := ordered_frontier_increasing_path_roots G U hfront f hf hnon
  intro a b c hab hbc
  obtain ⟨u, huR, hsep⟩ := hrecord (f b) (f c) (hf hbc) (hroots b c hbc)
  have hab' : a < b := by show a.val < b.val; omega
  exact ⟨u, hRU (f b) huR, hred (f a) (f b) (hf hab') (hlinks a b hab) u huR,
    fun v hv => hsep.1 v (hCZ (f b) hv), fun v hv => hsep.2 v (hCZ (f c) hv)⟩

theorem antitone_predicate_of_consecutive {n : ℕ} (P : Fin n → Prop)
    (hstep : ∀ a b, a.val + 1 = b.val → P b → P a) : Antitone P := by
  cases n with
  | zero => intro a; exact Fin.elim0 a
  | succ n =>
    exact Fin.antitone_iff_succ_le.mpr (fun i => hstep i.castSucc i.succ rfl)

/-- Every later path block has a large single prefix-profile cell. The separator
    hypotheses here are furnished by mixed_path_recorded_root_law above. -/
theorem mixed_path_large_profile_cell {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m n : ℕ}
    (Y U : Finset V) (C : Fin m → Finset V) {β : ℝ}
    (hCY : ∀ i, C i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hconn : ∀ i, EHP6.AntiConnected G (C i)) (hβ : 2 * β ≤ 1)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (f : Fin n → Fin m) (hf : StrictMono f)
    (hlinks : ∀ a b, a.val + 1 = b.val → MixedPair G C (f a) (f b))
    (hsep : ∀ a b c : Fin n, a.val + 1 = b.val → b < c →
      ∃ u ∈ U, (∀ v ∈ C (f a), G.Adj u v) ∧
        (∀ v ∈ C (f b), G.Adj u v) ∧ ∀ v ∈ C (f c), ¬ G.Adj u v)
    (t : Fin n) :
    ∃ cut : Fin (t.val + 1), ∃ D ⊆ C (f t),
      ((C (f t)).card : ℝ) / (t.val + 1) ≤ D.card ∧
      ∀ z ∈ D, ∀ a : Fin t.val,
        (∀ b ∈ C (f ⟨a.val, a.isLt.trans t.isLt⟩), G.Adj z b) ↔ a.val < cut.val := by
  let e : Fin t.val → Fin n := fun a => ⟨a.val, a.isLt.trans t.isLt⟩
  let P : V → Fin t.val → Prop := fun z a => ∀ b ∈ C (f (e a)), G.Adj z b
  have hmon : ∀ z ∈ C (f t), Antitone (P z) := by
    intro z hz
    apply antitone_predicate_of_consecutive
    intro a b hab hfull
    have hab' : e a < e b := by show a.val < b.val; omega
    have hbt : e b < t := b.isLt
    have hat : e a < t := a.isLt
    rcases htypes (f (e a)) (f t) (hf hat) z hz with h | hs
    · exact h
    obtain ⟨u, hu, hua, hub, hut⟩ := hsep (e a) (e b) t hab hbt
    have hzA : z ∉ C (f (e a)) := fun h =>
      Finset.disjoint_left.mp (hdisj (ne_of_gt (hf hat))) hz h
    exact False.elim (rp5_forcing_no_reversal G (hCY _) (hCY _)
      (hdisj (ne_of_lt (hf hab'))) (hout u hu) (hCY _ hz) hzA (hfree u hu)
      hua hub (hut z hz) hfull (hconn _) hβ hs
      (htypes _ _ (hf hab')) (hlinks (e a) (e b) hab).1 (hlinks (e a) (e b) hab).2)
  exact large_uniform_prefix_cell (C (f t)) t.val P hmon

#print axioms mixed_pair_original_noncomplete
#print axioms mixed_path_recorded_root_law
#print axioms antitone_predicate_of_consecutive
#print axioms mixed_path_large_profile_cell

end AllPathsLocal
