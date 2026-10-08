import RP5PathForcing
import RP5Order
import Mathlib.Data.Finset.Sort

namespace AllPathsLocal

theorem nonmixed_pair_uniform {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (C : Fin m → Finset V) {i j : Fin m} {β : ℝ}
    (htypes : ∀ v ∈ C j, (∀ b ∈ C i, G.Adj v b) ∨
      ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (hn : ¬ MixedPair G C i j) :
    EHP6.Complete G (C i) (C j) ∨ EHP6.SparseTo G β (C j) (C i) := by
  classical
  by_cases hfull : ∃ w ∈ C j, ∀ b ∈ C i, G.Adj w b
  · left
    intro b hb v hv
    have hf : ∀ b ∈ C i, G.Adj v b := by
      by_contra hh
      exact hn ⟨hfull, v, hv, hh⟩
    exact (hf b hb).symm
  · right
    intro v hv
    exact ((htypes v hv).resolve_left (fun h => hfull ⟨v, hv, h⟩)).le

/-- Select every prefix cell independently; the resulting actual n-block blockade
    has width w/n and later-to-earlier precision n*beta. -/
theorem mixed_path_blockade {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m n : ℕ}
    (Y U : Finset V) (C : Fin m → Finset V) {β w : ℝ} (hn : 0 < n)
    (hCY : ∀ i, C i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hconn : ∀ i, EHP6.AntiConnected G (C i)) (hβ0 : 0 ≤ β) (hβ : 2 * β ≤ 1)
    (hwidth : ∀ i, w ≤ ((C i).card : ℝ))
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (f : Fin n → Fin m) (hf : StrictMono f)
    (hlinks : ∀ a b, a.val + 1 = b.val → MixedPair G C (f a) (f b))
    (hsep : ∀ a b c : Fin n, a.val + 1 = b.val → b < c →
      ∃ u ∈ U, (∀ v ∈ C (f a), G.Adj u v) ∧
        (∀ v ∈ C (f b), G.Adj u v) ∧ ∀ v ∈ C (f c), ¬ G.Adj u v) :
    ∃ γ : EHP6.Blockade Y n (w / n), γ.m = n ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (n * β) (γ.B j) (γ.B i) := by
  classical
  have hc := fun t => mixed_path_large_profile_cell G Y U C hCY hdisj hconn hβ
    hout hfree htypes f hf hlinks hsep t
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

/-- The large height level already has uniform pairs; retain an ordered r-subfamily. -/
theorem independent_level_blockade {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m r : ℕ}
    (Y : Finset V) (C : Fin m → Finset V) {β w : ℝ}
    (hr : 1 ≤ r) (hβ : 0 ≤ β) (hw : 0 ≤ w)
    (hCY : ∀ i, C i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hwidth : ∀ i, w ≤ ((C i).card : ℝ))
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (I : Finset (Fin m)) (hI : r ≤ I.card)
    (hind : ∀ i ∈ I, ∀ j ∈ I, i < j → ¬ MixedPair G C i j) :
    ∃ γ : EHP6.Blockade Y r (w / r), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (r * β) (γ.B j) (γ.B i) := by
  classical
  let f := I.orderEmbOfCardLe hI
  have hf : ∀ i, f i ∈ I := fun i => Finset.orderEmbOfCardLe_mem I hI i
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hwr : w / (r : ℝ) ≤ w := by
    apply (div_le_iff₀ hr0).mpr
    nlinarith
  let γ : EHP6.Blockade Y r (w / r) :=
    ⟨r, fun i => C (f i), le_rfl, fun i => hCY (f i),
      fun i => hwr.trans (hwidth (f i)),
      fun i j hij => hdisj (fun h => hij (f.injective h))⟩
  refine ⟨γ, rfl, ?_⟩
  intro i j hij
  rcases nonmixed_pair_uniform G C (htypes _ _ (f.strictMono hij))
    (hind (f i) (hf i) (f j) (hf j) (f.strictMono hij)) with h | h
  · exact Or.inl h
  · right
    intro v hv
    have hsmall := h v hv
    have hscale : β ≤ (r : ℝ) * β := by nlinarith
    exact hsmall.trans (mul_le_mul_of_nonneg_right hscale (by positivity))

#print axioms nonmixed_pair_uniform
#print axioms mixed_path_blockade
#print axioms independent_level_blockade

end AllPathsLocal
