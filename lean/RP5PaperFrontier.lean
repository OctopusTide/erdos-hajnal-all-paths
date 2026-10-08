import RP5FrontierParameters
import Mathlib.Data.Nat.Sqrt

namespace AllPathsLocal

section PaperFrontier

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {S : Finset V} {Z : List (Finset V)}

local notation "m" => Z.length
local notation "r" => Nat.sqrt m

/-- III.4 with the paper's first and second Tooth parameters and integer
    r=floor(sqrt(m)). Graph-theoretic inputs are only an actual rooted cut frontier
    and the original RP5 hypothesis. Every representative and root family is built. -/
theorem paper_frontier (hfront : OrderedCutFrontier G U S Z) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hm : 2 ^ 16 ≤ m) {τ W : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1)
    (hWlarge : 16 / (τ / (64 * (m : ℝ) ^ 5)) ^ 3 ≤ W)
    (hwidth : ∀ i : Fin m, W ≤ ((Z.get i).card : ℝ)) :
    (∃ i : Fin m, RP4Early G (Z.get i) (τ / (64 * (m : ℝ) ^ 5)) m) ∨
    (∃ i : Fin m, ∃ B ⊆ Z.get i, ((Z.get i).card : ℝ) / m ≤ B.card ∧
      RP4Early G B (1 / (m : ℝ) ^ 2) m) ∨
    (∃ γ : EHP6.Blockade Y m (W / (2 * (m : ℝ) ^ 4)), γ.m = m ∧ γ.IsComplete G) ∨
    (∃ γ : EHP6.Blockade Y r (W / (2 * (m : ℝ) ^ 3 * r)), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G τ (γ.B j) (γ.B i)) := by
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hr256 : 256 ≤ r := Nat.le_sqrt.mpr (by norm_num at hm ⊢; exact hm)
  have hr2 : 2 ≤ r := by omega
  have hcount : r * (r - 1) ≤ m :=
    (Nat.mul_le_mul_left r (Nat.sub_le r 1)).trans (Nat.sqrt_le m)
  obtain ⟨hx, hx20, hkx, hxτ, hβ, hprecision, hlarge'⟩ :=
    frontier_paper_scalar_bounds (m : ℝ) (r : ℝ) τ hmR (by positivity)
      (by exact_mod_cast Nat.sqrt_le_self m) hτ0 hτ
  have hW : 0 ≤ W := (show (0 : ℝ) < 16 / (τ / (64 * (m : ℝ) ^ 5)) ^ 3 by positivity).le.trans hWlarge
  exact frontier_pipeline G U Y hfront hSY hout hfree hx hx20 hm hkx hτ hxτ hβ hprecision
    hr2 hcount hW hwidth (fun i => hWlarge.trans (hwidth i))
    (fun i => (hlarge'.trans hWlarge).trans (hwidth i))

#print axioms paper_frontier

end PaperFrontier

end AllPathsLocal
