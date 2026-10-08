import RP5GlobalPurification
import RP5Grouping

/-! Choose actual large anticomponents after purification, and show that a pair
    containing both types must be red. III.3, lines 240--248. -/

namespace AllPathsLocal

def MixedPair {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {m : ℕ} (C : Fin m → Finset V) (i j : Fin m) : Prop :=
  (∃ w ∈ C j, ∀ b ∈ C i, G.Adj w b) ∧
  (∃ v ∈ C j, ¬ ∀ b ∈ C i, G.Adj v b)

/-- Sparse degrees transfer with the exact reciprocal shrinkage factor. -/
theorem sparse_type_restrict {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {B C : Finset V} {v : V} {θ ρ : ℝ}
    (hCB : C ⊆ B) (hθ : 0 ≤ θ) (hsize : (B.card : ℝ) ≤ ρ * C.card)
    (hsmall : ((EHP6.nbrs G v B).card : ℝ) < θ * B.card) :
    ((EHP6.nbrs G v C).card : ℝ) < (ρ * θ) * C.card := by
  have hd : ((EHP6.nbrs G v C).card : ℝ) ≤ (EHP6.nbrs G v B).card := by
    exact_mod_cast Finset.card_le_card (EHP6.nbrs_mono (G := G) hCB)
  have hh := mul_le_mul_of_nonneg_left hsize hθ
  nlinarith

theorem sparse_not_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {v : V} {β : ℝ}
    (hβ : β ≤ 1) (hs : ((EHP6.nbrs G v C).card : ℝ) < β * C.card) :
    ¬ ∀ b ∈ C, G.Adj v b := by
  intro hf
  have heq : EHP6.nbrs G v C = C := by
    ext b
    simp only [EHP6.nbrs, Finset.mem_filter]
    exact ⟨And.left, fun hb => ⟨hb, hf b hb⟩⟩
  rw [heq] at hs
  have hh := mul_le_mul_of_nonneg_right hβ (show (0 : ℝ) ≤ C.card by positivity)
  nlinarith

/-- Every block yields a large actual anticomponent, unless one block provides
    a complete blockade of exactly m blocks. -/
theorem frontier_component_selection {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B E : Fin m → Finset V) (hm : 2 ≤ m)
    (hEB : ∀ i, E i ⊆ B i) (hEc : ∀ i, ((B i).card : ℝ) / (2 * m) ≤ (E i).card)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∃ i, ∃ γ : EHP6.Blockade (E i) m ((E i).card / (m : ℝ) ^ 2),
      γ.m = m ∧ γ.IsComplete G) ∨
      ∃ C : Fin m → Finset V,
        (∀ i, EHP6.IsAnticomponent G (E i) (C i) ∧ C i ⊆ B i ∧
          ((B i).card : ℝ) / (2 * (m : ℝ) ^ 2) ≤ (C i).card) ∧
        Pairwise (fun i j => Disjoint (C i) (C j)) := by
  classical
  by_cases hearly : ∃ i, ∃ γ : EHP6.Blockade (E i) m ((E i).card / (m : ℝ) ^ 2),
      γ.m = m ∧ γ.IsComplete G
  · exact Or.inl hearly
  right
  have hc : ∀ i, ∃ K, EHP6.IsAnticomponent G (E i) K ∧
      ((E i).card : ℝ) / m ≤ K.card := by
    intro i
    exact (large_anticomponent_or_grouping G (E i) m hm).resolve_right (fun h => hearly ⟨i, h⟩)
  choose C hC hCc using hc
  have hCB : ∀ i, C i ⊆ B i := fun i => (hC i).1.trans (hEB i)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨C, ?_, ?_⟩
  · intro i
    refine ⟨hC i, hCB i, ?_⟩
    have hh := div_le_div_of_nonneg_right (hEc i) hm0.le
    have heq : ((B i).card : ℝ) / (2 * m) / m = (B i).card / (2 * (m : ℝ) ^ 2) := by ring
    rw [heq] at hh
    exact hh.trans (hCc i)
  · intro i j hij
    exact Finset.disjoint_left.mpr (fun _ hi hj =>
      Finset.disjoint_left.mp (hdisj hij) (hCB i hi) (hCB j hj))

/-- Both original types remain separated after taking a sufficiently large component. -/
theorem frontier_component_types {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B C : Fin m → Finset V) {θ : ℝ} (hm : 0 < m) (hθ : 0 ≤ θ)
    (hCB : ∀ i, C i ⊆ B i)
    (hCc : ∀ i, ((B i).card : ℝ) / (2 * (m : ℝ) ^ 2) ≤ (C i).card)
    (htypes : ∀ i j, i < j → ∀ v ∈ B j,
      (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) :
    ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨
      ((EHP6.nbrs G v (C i)).card : ℝ) < (2 * (m : ℝ) ^ 2 * θ) * (C i).card := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  intro i j hij v hv
  rcases htypes i j hij v (hCB j hv) with hf | hs
  · exact Or.inl (fun b hb => hf b (hCB i hb))
  · right
    exact sparse_type_restrict G (hCB i) hθ
      (by simpa only [mul_comm] using
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) ^ 2)).mp (hCc i)) hs

/-- Purified good pairs cannot be ambiguous on the chosen components. -/
theorem component_mixed_pair_red {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B E C R : Fin m → Finset V) {θ η : ℝ} (hm : 0 < m) (hθ : 0 ≤ θ)
    (hβ : 2 * (m : ℝ) ^ 2 * θ ≤ 1)
    (hCE : ∀ i, C i ⊆ E i) (hEB : ∀ i, E i ⊆ B i)
    (hCc : ∀ i, ((B i).card : ℝ) / (2 * (m : ℝ) ^ 2) ≤ (C i).card)
    (hgood : ∀ i j, i < j → GoodPair G B R η i j →
      (∀ v ∈ E j, ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) ∨
      (∀ v ∈ E j, ∀ b ∈ B i, G.Adj v b)) :
    ∀ i j, i < j → MixedPair G C i j → ¬ GoodPair G B R η i j := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  intro i j hij hmix hg
  rcases hgood i j hij hg with hs | hf
  · obtain ⟨w, hw, hwfull⟩ := hmix.1
    have hsmall := sparse_type_restrict G (ρ := 2 * (m : ℝ) ^ 2) ((hCE i).trans (hEB i)) hθ
      (by simpa only [mul_comm] using
        (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ) ^ 2)).mp (hCc i))
      (hs w (hCE j hw))
    exact sparse_not_complete G hβ hsmall hwfull
  · obtain ⟨v, hv, hvnot⟩ := hmix.2
    exact hvnot (fun b hb => hf v (hCE j hv) b (hEB i (hCE i hb)))

#print axioms sparse_type_restrict
#print axioms sparse_not_complete
#print axioms frontier_component_selection
#print axioms frontier_component_types
#print axioms component_mixed_pair_red

end AllPathsLocal
