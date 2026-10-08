import RP5FrontierAssembly
import EHP6.BlockadeUtil

namespace AllPathsLocal

section Pipeline

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {S : Finset V} {Z : List (Finset V)}

local notation "m" => Z.length

/-- Actual two-Tooth frontier construction, including all early branches. Scalar
    bounds are exposed explicitly so the subsequent paper-parameter instantiation
    can be checked independently. No graph-theoretic result is assumed. -/
theorem frontier_pipeline (hfront : OrderedCutFrontier G U S Z) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    {x τ W : ℝ} {r : ℕ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20)
    (hm : 2 ^ 16 ≤ m) (hkx : (m : ℝ) ≤ 2 / Real.sqrt x)
    (hτ : τ ≤ 1) (hxτ : x / 4 ≤ τ / (256 * (m : ℝ) ^ 5))
    (hβ : 2 * (2 * (m : ℝ) ^ 2 * (x / 4)) ≤ 1)
    (hprecision : (r : ℝ) * (2 * (m : ℝ) ^ 2 * (x / 4)) ≤ τ)
    (hr : 2 ≤ r) (hcount : r * (r - 1) ≤ m) (hW : 0 ≤ W)
    (hwidth : ∀ i : Fin m, W ≤ ((Z.get i).card : ℝ))
    (hlarge : ∀ i : Fin m, 16 / x ^ 3 ≤ ((Z.get i).card : ℝ))
    (hlarge' : ∀ i : Fin m, 16 * (m : ℝ) ^ 7 ≤ ((Z.get i).card : ℝ)) :
    (∃ i : Fin m, RP4Early G (Z.get i) x m) ∨
    (∃ i : Fin m, ∃ B ⊆ Z.get i, ((Z.get i).card : ℝ) / m ≤ B.card ∧
      RP4Early G B (1 / (m : ℝ) ^ 2) m) ∨
    (∃ γ : EHP6.Blockade Y m (W / (2 * (m : ℝ) ^ 4)), γ.m = m ∧ γ.IsComplete G) ∨
    (∃ γ : EHP6.Blockade Y r (W / (2 * (m : ℝ) ^ 3 * r)), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G τ (γ.B j) (γ.B i)) := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hZY : ∀ i : Fin m, Z.get i ⊆ Y := by
    intro i
    exact ((ordered_frontier_properties G U hfront).1 _ (List.get_mem Z i)).trans hSY
  rcases frontier_first_tooth_round G U Y hfront hSY hout hfree hx hx20 hm hkx hlarge with
    early | ⟨B, hBZ, hBc, htypesZ, hdisjB⟩
  · exact Or.inl early
  right
  have hBY : ∀ i, B i ⊆ Y := fun i => (hBZ i).trans (hZY i)
  have hBlarge : ∀ i, 16 * (m : ℝ) ^ 6 ≤ (B i).card := by
    intro i
    have hh : 16 * (m : ℝ) ^ 6 ≤ ((Z.get i).card : ℝ) / m := by
      apply (le_div_iff₀ hm0).mpr
      convert hlarge' i using 1 <;> ring
    exact hh.trans (hBc i)
  have htypesB : ∀ i j, i < j → ∀ v ∈ B j,
      (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < (x / 4) * (B i).card := by
    intro i j hij v hv
    rcases htypesZ i j hij v (hBZ j hv) with h | h
    · exact Or.inl h
    · right; nlinarith
  obtain ⟨R, hR⟩ := recorded_root_families G U Z.get
  have hRU : ∀ i, R i ⊆ U := fun i => (hR i).2.1
  have hRc : ∀ i, (R i).card ≤ m := by intro i; have := (hR i).1; omega
  have hfullB : ∀ j, ∀ u ∈ R j, ∀ v ∈ B j, G.Adj u v := by
    intro j u hu v hv
    exact (hR j).2.2.1 u hu v (hBZ j hv)
  rcases frontier_second_round G B R hm hτ (by positivity) hxτ hBlarge hBY
      hdisjB hRU hRc hfullB hout hfree htypesB with
    ⟨i, early⟩ | ⟨E, hEc, _, hgood, hred⟩
  · exact Or.inl ⟨i, B i, hBZ i, hBc i, early⟩
  right
  have hEB : ∀ i, E i ⊆ B i := fun i => (hEc i).1
  have hEsize : ∀ i, ((B i).card : ℝ) / (2 * m) ≤ (E i).card := fun i => (hEc i).2
  rcases frontier_component_selection G B E (by omega) hEB hEsize hdisjB with
    ⟨i, γ, hγm, hγcomplete⟩ | ⟨C, hC, hdisjC⟩
  · left
    have hEwidth : W / (2 * (m : ℝ) ^ 2) ≤ ((E i).card : ℝ) := by
      have h := div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right (hwidth i) hm0.le).trans (hBc i))
        (show (0 : ℝ) ≤ 2 * m by positivity)
      have heq : W / (m : ℝ) / (2 * m) = W / (2 * (m : ℝ) ^ 2) := by ring
      rw [heq] at h
      exact h.trans (hEsize i)
    have hw' : W / (2 * (m : ℝ) ^ 4) ≤ (E i).card / (m : ℝ) ^ 2 := by
      have h := div_le_div_of_nonneg_right hEwidth (show (0 : ℝ) ≤ (m : ℝ) ^ 2 by positivity)
      convert h using 1 <;> ring
    exact ⟨γ.mono ((hEB i).trans (hBY i)) le_rfl hw', hγm, hγcomplete⟩
  right
  have hCE : ∀ i, C i ⊆ E i := fun i => (hC i).1.1
  have hCB : ∀ i, C i ⊆ B i := fun i => (hC i).2.1
  have hCsize : ∀ i, ((B i).card : ℝ) / (2 * (m : ℝ) ^ 2) ≤ (C i).card := fun i => (hC i).2.2
  have hCY : ∀ i, C i ⊆ Y := fun i => (hCB i).trans (hBY i)
  have hCZ : ∀ i, C i ⊆ Z.get i := fun i => (hCB i).trans (hBZ i)
  have hconn : ∀ i, EHP6.AntiConnected G (C i) := fun i => (hC i).1.2.2.1
  have hCwidth : ∀ i, W / (2 * (m : ℝ) ^ 3) ≤ ((C i).card : ℝ) := by
    intro i
    have h := div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right (hwidth i) hm0.le).trans (hBc i))
      (show (0 : ℝ) ≤ 2 * (m : ℝ) ^ 2 by positivity)
    have heq : W / (m : ℝ) / (2 * (m : ℝ) ^ 2) = W / (2 * (m : ℝ) ^ 3) := by ring
    rw [heq] at h
    exact h.trans (hCsize i)
  have hredC : ∀ i j, i < j → MixedPair G C i j → ∀ u ∈ R j, ∀ v ∈ C i, G.Adj u v := by
    intro i j hij hmix u hu v hv
    have hn := component_mixed_pair_red G B E C R (by omega) (by positivity)
      (by linarith : 2 * (m : ℝ) ^ 2 * (x / 4) ≤ 1) hCE hEB hCsize hgood i j hij hmix
    exact hred i j hij hn u hu v (hCE i hv)
  obtain ⟨γ, hγm, hγtypes⟩ := ordered_frontier_component_blockade G U Y hfront C R hr hcount
    hCZ hCY hdisjC hconn (by positivity) hβ (by positivity) hCwidth hout hfree
    (frontier_component_types G B C (by omega) (by positivity) hCB hCsize htypesB)
    hRU (fun j => (hR j).2.2.2) hredC
  have heq : W / (2 * (m : ℝ) ^ 3) / r = W / (2 * (m : ℝ) ^ 3 * r) := by ring
  let δ := γ.mono (Finset.Subset.refl Y) le_rfl heq.symm.le
  refine ⟨δ, hγm, ?_⟩
  intro i j hij
  rcases hγtypes i j hij with h | h
  · exact Or.inl h
  · right
    intro v hv
    exact (h v hv).trans (mul_le_mul_of_nonneg_right hprecision (by positivity))

#print axioms frontier_pipeline

end Pipeline

end AllPathsLocal
