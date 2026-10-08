import AllPathsLocal

/-! Structural steps for the RP5 Tooth proof, P7_from_P6_English_proof.txt
    Sections III.1--III.3. The full quantitative Tooth theorem is not yet proved. -/

namespace AllPathsLocal

def RootedP5Free {V : Type} (G : SimpleGraph V) (Y : Finset V) (r : V) : Prop :=
  ¬ ∃ p : Fin 5 → V, IsInducedPath Gᶜ p ∧ p 0 = r ∧
    ∀ i, i ≠ 0 → p i ∈ Y

/-- The root extension used both by the frontier and by representative purification. -/
theorem rp5_to_rp4 {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {Y T : Finset V} {r z : V}
    (hr : r ∉ Y) (hz : z ∈ Y) (hT : T ⊆ Y)
    (hfree : RootedP5Free G Y r) (hrz : ¬ G.Adj r z)
    (hrT : ∀ t ∈ T, G.Adj r t) : RootedP4Free G T z := by
  rintro ⟨p, hp, hp0, htail⟩
  have hpY : ∀ i, p i ∈ Y := by
    intro i
    by_cases hi : i = 0
    · simpa [hi, hp0] using hz
    · exact hT (htail i hi)
  have hnew : ∀ i, r ≠ p i := by
    intro i heq
    exact hr (heq ▸ hpY i)
  have hhead : ∀ i, Gᶜ.Adj r (p i) ↔ i = 0 := by
    intro i
    by_cases hi : i = 0
    · have hrz' : r ≠ z := fun heq => hr (heq ▸ hz)
      simp [SimpleGraph.compl_adj, hi, hp0, hrz', hrz]
    · simp [SimpleGraph.compl_adj, hi, hrT (p i) (htail i hi)]
  apply hfree
  refine ⟨Fin.cases r p, prefix_inducedPath Gᶜ p r hp hnew hhead, rfl, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    exact False.elim (hi rfl)
  · intro _
    exact hpY j

/-- Two sets of fewer than beta |A| neighbors cannot cover A when 2 beta ≤ 1. -/
theorem common_nonneighbor_of_two_sparse {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (z v : V) (β : ℝ)
    (hβ : 2 * β ≤ 1)
    (hz : ((EHP6.nbrs G z A).card : ℝ) < β * A.card)
    (hv : ((EHP6.nbrs G v A).card : ℝ) < β * A.card) :
    ∃ b ∈ A, ¬ G.Adj z b ∧ ¬ G.Adj v b := by
  classical
  by_contra h
  have hsub : A ⊆ EHP6.nbrs G z A ∪ EHP6.nbrs G v A := by
    intro b hb
    by_cases hzb : G.Adj z b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, hzb⟩)
    · have hvb : G.Adj v b := by
        by_contra hvb
        exact h ⟨b, hb, hzb, hvb⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, hvb⟩)
  have hc := (Finset.card_le_card hsub).trans
    (Finset.card_union_le (EHP6.nbrs G z A) (EHP6.nbrs G v A))
  have hcR : (A.card : ℝ) ≤ (EHP6.nbrs G z A).card + (EHP6.nbrs G v A).card := by
    exact_mod_cast hc
  have hbound := mul_le_mul_of_nonneg_right hβ (show (0 : ℝ) ≤ A.card by positivity)
  nlinarith

/-- The quantitative five-vertex obstruction in Section III.3, lines 264--273.
    A later vertex cannot be sparse on I and complete on a connected block J
    which has both types toward I, when the separating root is exact on I and J. -/
theorem rp5_forcing_no_reversal {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y I J : Finset V} {r z : V} {β : ℝ}
    (hI : I ⊆ Y) (hJ : J ⊆ Y) (hIJ : Disjoint I J)
    (hrY : r ∉ Y) (hzY : z ∈ Y) (hzI : z ∉ I)
    (hfree : RootedP5Free G Y r)
    (hrI : ∀ b ∈ I, G.Adj r b) (hrJ : ∀ v ∈ J, G.Adj r v)
    (hrz : ¬ G.Adj r z) (hzJ : ∀ v ∈ J, G.Adj z v)
    (hconn : EHP6.AntiConnected G J) (hβ : 2 * β ≤ 1)
    (hzsmall : ((EHP6.nbrs G z I).card : ℝ) < β * I.card)
    (htypes : ∀ v ∈ J, (∀ b ∈ I, G.Adj v b) ∨
       ((EHP6.nbrs G v I).card : ℝ) < β * I.card)
    (hfull : ∃ w ∈ J, ∀ b ∈ I, G.Adj w b)
    (hnotfull : ∃ v ∈ J, ¬ ∀ b ∈ I, G.Adj v b) : False := by
  classical
  let P := J.filter (fun v => ∀ b ∈ I, G.Adj v b)
  obtain ⟨w₀, hw₀J, hw₀⟩ := hfull
  obtain ⟨v₀, hv₀J, hv₀⟩ := hnotfull
  obtain ⟨w, hwP, v, hvP, hwv⟩ := hconn P (Finset.filter_subset _ _)
    ⟨w₀, Finset.mem_filter.mpr ⟨hw₀J, hw₀⟩⟩
    ⟨v₀, Finset.mem_sdiff.mpr ⟨hv₀J, fun h => hv₀ (Finset.mem_filter.mp h).2⟩⟩
  obtain ⟨hwJ, hwfull⟩ := Finset.mem_filter.mp hwP
  obtain ⟨hvJ, hvnotP⟩ := Finset.mem_sdiff.mp hvP
  have hvnotfull : ¬ ∀ b ∈ I, G.Adj v b :=
    fun h => hvnotP (Finset.mem_filter.mpr ⟨hvJ, h⟩)
  have hvsmall := (htypes v hvJ).resolve_left hvnotfull
  obtain ⟨b, hbI, hzb, hvb⟩ := common_nonneighbor_of_two_sparse G I z v β hβ hzsmall hvsmall
  have hrb := hrI b hbI
  have hrv := hrJ v hvJ
  have hrw := hrJ w hwJ
  have hzv := hzJ v hvJ
  have hzw := hzJ w hwJ
  have hwb := hwfull b hbI
  have drb := G.ne_of_adj hrb
  have drv := G.ne_of_adj hrv
  have drw := G.ne_of_adj hrw
  have drz : r ≠ z := fun h => hrY (h ▸ hzY)
  have dzb : z ≠ b := fun h => hzI (h ▸ hbI)
  have dzv := G.ne_of_adj hzv
  have dzw := G.ne_of_adj hzw
  have dbv : b ≠ v := by
    intro h
    subst v
    exact Finset.disjoint_left.mp hIJ hbI hvJ
  have dbw := (G.ne_of_adj hwb).symm
  have dvw : v ≠ w := by
    intro h
    subst v
    exact hvnotfull hwfull
  have hbv : ¬ G.Adj b v := fun h => hvb (G.adj_symm h)
  have hvw : ¬ G.Adj v w := fun h => hwv (G.adj_symm h)
  apply hfree
  refine ⟨![r, z, b, v, w], ?_, rfl, ?_⟩
  · constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
    · intro i j
      have hzr : ¬ G.Adj z r := fun h => hrz (G.adj_symm h)
      have hbz : ¬ G.Adj b z := fun h => hzb (G.adj_symm h)
      have hbr := G.adj_symm hrb
      have hvr := G.adj_symm hrv
      have hwr := G.adj_symm hrw
      have hvz := G.adj_symm hzv
      have hwz := G.adj_symm hzw
      have hbw := G.adj_symm hwb
      fin_cases i <;> fin_cases j <;>
        simp [SimpleGraph.compl_adj, drz, drb, drv, drw, dzb, dzv, dzw,
          dbv, dbw, dvw, Ne.symm drz, Ne.symm drb, Ne.symm drv, Ne.symm drw,
          Ne.symm dzb, Ne.symm dzv, Ne.symm dzw, Ne.symm dbv, Ne.symm dbw,
          Ne.symm dvw, hrz, hzr, hzb, hbz, hvb, hbv, hwv, hvw,
          hrb, hrv, hrw, hzv, hzw, hwb, hbr, hvr, hwr, hvz, hwz, hbw]
  · intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · exact hzY
    · exact hI hbI
    · exact hJ hvJ
    · exact hJ hwJ

/-- Preserve all four actual early Tooth outputs, including their integer lengths. -/
def RP4Early {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (x : ℝ) (k : ℕ) : Prop :=
  (∃ K : ℕ, (k : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ 1 / x ∧
    ∃ β : EHP6.Blockade Y K (Y.card / (K : ℝ) ^ 4), β.IsPure G) ∨
  (∃ L : ℕ, (k : ℝ) ^ 3 ≤ (9 * (L : ℝ)) ^ 4 ∧ (8 * (L : ℝ)) ^ 4 ≤ (k : ℝ) ^ 3 ∧
    ∃ β : EHP6.Blockade Y L (Y.card / (2 * k)), β.IsPure G) ∨
  (∃ β : EHP6.Blockade Y ⌊1 / x⌋₊ (x ^ 2 * Y.card / k),
    β.IsComplete G ∨ β.IsAnticomplete G) ∨
  (∃ β : EHP6.Blockade Y ⌊1 / (x * k)⌋₊ (x ^ 3 * Y.card / 4), β.IsComplete G)

/-- Apply one simultaneous Tooth call to all RP5 representatives; no common separating
    root is assumed, and the sparse degree is measured against the returned core. -/
theorem rp5_representative_tooth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y B P : Finset V} {x : ℝ} {k : ℕ}
    (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20)
    (hk : 2 ^ 16 ≤ k) (hkx : (k : ℝ) ≤ 2 / Real.sqrt x)
    (hn : 16 / x ^ 3 ≤ (B.card : ℝ))
    (hB : B ⊆ Y) (hP : P ⊆ Y) (hout : ∀ p ∈ P, p ∉ B)
    (hsep : ∀ p ∈ P, ∃ r, r ∉ Y ∧ RootedP5Free G Y r ∧
      ¬ G.Adj r p ∧ ∀ b ∈ B, G.Adj r b) :
    RP4Early G B x k ∨
      ∃ D ⊆ B, (B.card : ℝ) / k ≤ D.card ∧
        ∀ p ∈ P, (∀ v ∈ D, G.Adj p v) ∨
          ((EHP6.nbrs G p D).card : ℝ) < x * D.card / 4 := by
  have hroots : ∀ p ∈ P, RootedP4Free G B p := by
    intro p hp
    obtain ⟨r, hrY, hrfree, hrp, hrB⟩ := hsep p hp
    exact rp5_to_rp4 G hrY (hP hp) hB hrfree hrp hrB
  rcases rp4_tooth G hx hx20 hk hkx B P hn hout hroots with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr h

#print axioms rp5_to_rp4
#print axioms common_nonneighbor_of_two_sparse
#print axioms rp5_forcing_no_reversal
#print axioms rp5_representative_tooth

end AllPathsLocal
