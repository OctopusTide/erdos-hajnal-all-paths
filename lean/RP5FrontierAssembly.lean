import RP5PathSelection
import RP5FirstRound

namespace AllPathsLocal

/-- Combine both alternatives of the increasing-path/height argument on an actual
    tree frontier. Separators come from the tree and recorded root families. -/
theorem ordered_frontier_component_blockade {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    (C R : Fin Z.length → Finset V) {r : ℕ} {β w : ℝ}
    (hr : 2 ≤ r) (hcount : r * (r - 1) ≤ Z.length)
    (hCZ : ∀ i, C i ⊆ Z.get i) (hCY : ∀ i, C i ⊆ Y)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hconn : ∀ i, EHP6.AntiConnected G (C i))
    (hβ0 : 0 ≤ β) (hβ : 2 * β ≤ 1) (hw : 0 ≤ w)
    (hwidth : ∀ i, w ≤ ((C i).card : ℝ))
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (hRU : ∀ i, R i ⊆ U)
    (hrecord : ∀ j l, j < l → (∃ u ∈ U, RootSeparates G u (Z.get j) (Z.get l)) →
      ∃ u ∈ R j, RootSeparates G u (Z.get j) (Z.get l))
    (hred : ∀ i j, i < j → MixedPair G C i j → ∀ u ∈ R j, ∀ v ∈ C i, G.Adj u v) :
    ∃ γ : EHP6.Blockade Y r (w / r), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (r * β) (γ.B j) (γ.B i) := by
  rcases increasing_path_or_large_independent_level (MixedPair G C) hr with
    ⟨last, hp⟩ | ⟨I, hIc, hIind⟩
  · obtain ⟨_, f, hf, _, _, hlinks⟩ := increasingQPath_sequence hp
    exact mixed_path_blockade G Y U C (by omega) hCY hdisj hconn hβ0 hβ hwidth
      hout hfree htypes f hf hlinks
      (mixed_path_recorded_root_law G U hfront C R hCZ hRU hrecord hred f hf hlinks)
  · have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcountR : (r : ℝ) * (r - 1) ≤ Z.length := by
      simpa only [Nat.cast_mul, hcast] using (show ((r * (r - 1) : ℕ) : ℝ) ≤ Z.length by exact_mod_cast hcount)
    have hrI : (r : ℝ) ≤ I.card :=
      ((le_div_iff₀ (by linarith : (0 : ℝ) < r - 1)).mpr hcountR).trans hIc
    exact independent_level_blockade G Y C (by omega) hβ0 hw hCY hdisj hwidth htypes
      I (by exact_mod_cast hrI) hIind

#print axioms ordered_frontier_component_blockade

end AllPathsLocal
