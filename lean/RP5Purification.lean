import AllPathsLocal
import RP5Structure
import EHP6.CombExtract

/-! Simultaneous purification for Section III.2 of P7_from_P6_English_proof.txt.
    Budgets are measured on the original core; roots are quantified universally. -/

namespace AllPathsLocal

open scoped BigOperators

/-- The averaging step chooses a representative among a root's nonneighbors. -/
theorem good_pair_representative {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B S : Finset V) (r : V) (θ η : ℝ)
    (hA : A.Nonempty) (hSB : S ⊆ B) (hθ : 0 ≤ θ) (hη : 0 < η)
    (hgood : η * A.card ≤ ((A \ EHP6.nbrs G r A).card : ℝ))
    (hsparse : ∀ v ∈ S, ((EHP6.nbrs G v A).card : ℝ) ≤ θ * A.card) :
    ∃ p ∈ A, ¬ G.Adj r p ∧
      ((EHP6.nbrs G p S).card : ℝ) ≤ θ * B.card / η := by
  classical
  let M := A \ EHP6.nbrs G r A
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hMc : (0 : ℝ) < M.card := lt_of_lt_of_le (mul_pos hη hAc) hgood
  have hM : M.Nonempty := Finset.card_pos.mp (by exact_mod_cast hMc)
  have hsum : (∑ p ∈ M, ((EHP6.nbrs G p S).card : ℝ)) ≤
      (S.card : ℝ) * (θ * A.card) := by
    rw [EHP6.sum_nbrs_comm]
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro v hv
    apply le_trans ?_ (hsparse v hv)
    exact_mod_cast Finset.card_le_card (EHP6.nbrs_mono (G := G) (Finset.sdiff_subset : M ⊆ A))
  have hcard : (S.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hSB
  have hedge : (∑ p ∈ M, ((EHP6.nbrs G p S).card : ℝ)) ≤
      (B.card : ℝ) * (θ * A.card) :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg hθ hAc.le))
  have hbudget : 0 ≤ θ * (B.card : ℝ) / η := by positivity
  have hmul := mul_le_mul_of_nonneg_right hgood hbudget
  have hcancel : η * (A.card : ℝ) * (θ * B.card / η) =
      (B.card : ℝ) * (θ * A.card) := by field_simp
  rw [hcancel] at hmul
  have hsum' : (∑ p ∈ M, ((EHP6.nbrs G p S).card : ℝ)) ≤
      ∑ _p ∈ M, θ * (B.card : ℝ) / η := by
    simpa using hedge.trans hmul
  obtain ⟨p, hpM, hp⟩ := Finset.exists_le_of_sum_le hM hsum'
  have hmem := Finset.mem_sdiff.mp hpM
  refine ⟨p, hmem.1, ?_, hp⟩
  intro hrp
  exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1, hrp⟩)

theorem delete_family_budget {V ι : Type} [DecidableEq V] [DecidableEq ι]
    (D : Finset V) (s : Finset ι) (bad : ι → Finset V) (cost : ι → ℝ)
    (hcost : ∀ i ∈ s, ((bad i).card : ℝ) ≤ cost i) :
    ∃ E ⊆ D, (D.card : ℝ) - ∑ i ∈ s, cost i ≤ E.card ∧
      ∀ i ∈ s, Disjoint E (bad i) := by
  classical
  let deleted := s.biUnion bad
  refine ⟨D \ deleted, Finset.sdiff_subset, ?_, ?_⟩
  · have hu : (deleted.card : ℝ) ≤ ∑ i ∈ s, ((bad i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := s) (t := bad))
    have hs := Finset.sum_le_sum hcost
    have hd : (D.card : ℝ) ≤ (D \ deleted).card + (deleted.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := D) (t := deleted))
    linarith
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro v hv hb
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩)

/-- Union all good-pair deletions at once and preserve the original type sets. -/
theorem purify_good_core {V ι : Type} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (s : Finset ι) (p : ι → V) (S : ι → Finset V)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsmall : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤ δ * D.card)
    (hcompleteType : ∀ i ∈ s, ∀ v ∈ D \ S i, G.Adj (p i) v)
    (hcore : ∀ i ∈ s, (∀ v ∈ D, G.Adj (p i) v) ∨
      ((EHP6.nbrs G (p i) D).card : ℝ) ≤ ε * D.card) :
    ∃ E ⊆ D, (1 - s.card * (δ + ε)) * D.card ≤ E.card ∧
      ∀ i ∈ s, E ⊆ S i ∨ Disjoint E (S i) := by
  classical
  let full : ι → Prop := fun i => ∀ v ∈ D, G.Adj (p i) v
  let bad : ι → Finset V := fun i => if full i then D ∩ S i else D \ S i
  have hbad : ∀ i ∈ s, ((bad i).card : ℝ) ≤ (δ + ε) * D.card := by
    intro i hi
    by_cases hf : full i
    · have hsub : bad i ⊆ EHP6.nbrs G (p i) (S i) := by
        intro v hv
        have hv' : v ∈ D ∩ S i := by simpa [bad, hf] using hv
        have hmem := Finset.mem_inter.mp hv'
        exact Finset.mem_filter.mpr ⟨hmem.2, hf v hmem.1⟩
      have hc : ((bad i).card : ℝ) ≤ (EHP6.nbrs G (p i) (S i)).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hh := hsmall i hi
      have hn : (0 : ℝ) ≤ D.card := by positivity
      nlinarith
    · have hsub : bad i ⊆ EHP6.nbrs G (p i) D := by
        intro v hv
        have hv' : v ∈ D \ S i := by simpa [bad, hf] using hv
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv').1, hcompleteType i hi v hv'⟩
      have hc : ((bad i).card : ℝ) ≤ (EHP6.nbrs G (p i) D).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hh := (hcore i hi).resolve_left hf
      have hn : (0 : ℝ) ≤ D.card := by positivity
      nlinarith
  obtain ⟨E, hED, hsize, havoid⟩ := delete_family_budget D s bad
    (fun _ => (δ + ε) * D.card) hbad
  refine ⟨E, hED, ?_, ?_⟩
  · have heq : (∑ _i ∈ s, (δ + ε) * (D.card : ℝ)) =
        (s.card : ℝ) * ((δ + ε) * D.card) := by simp
    rw [heq] at hsize
    nlinarith
  · intro i hi
    by_cases hf : full i
    · right
      apply Finset.disjoint_left.mpr
      intro v hvE hvS
      apply Finset.disjoint_left.mp (havoid i hi) hvE
      simpa [bad, hf] using Finset.mem_inter.mpr ⟨hED hvE, hvS⟩
    · left
      intro v hvE
      by_contra hvS
      apply Finset.disjoint_left.mp (havoid i hi) hvE
      simpa [bad, hf] using Finset.mem_sdiff.mpr ⟨hED hvE, hvS⟩

/-- Red-pair exactification quantifies over every recorded root, not one witness. -/
theorem exactify_red_roots {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B D R : Finset V) (η : ℝ) (hD : D ⊆ B)
    (hred : ∀ r ∈ R, ((B \ EHP6.nbrs G r B).card : ℝ) ≤ η * B.card) :
    ∃ E ⊆ D, (D.card : ℝ) - R.card * η * B.card ≤ E.card ∧
      ∀ r ∈ R, ∀ v ∈ E, G.Adj r v := by
  obtain ⟨E, hED, hsize, havoid⟩ := delete_family_budget D R
    (fun r => B \ EHP6.nbrs G r B) (fun _ => η * B.card) hred
  refine ⟨E, hED, ?_, ?_⟩
  · have heq : (∑ _r ∈ R, η * (B.card : ℝ)) = (R.card : ℝ) * (η * B.card) := by simp
    rw [heq] at hsize
    nlinarith
  · intro r hr v hv
    by_contra hrv
    apply Finset.disjoint_left.mp (havoid r hr) hv
    apply Finset.mem_sdiff.mpr
    refine ⟨hD (hED hv), ?_⟩
    intro hmem
    exact hrv (Finset.mem_filter.mp hmem).2

/-- The two deletion families can be imposed together without repeated core intersections. -/
theorem purify_and_exactify {V ι : Type} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B D R : Finset V) (s : Finset ι) (p : ι → V) (S : ι → Finset V)
    (δ ε η : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hD : D ⊆ B)
    (hsmall : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤ δ * D.card)
    (hcompleteType : ∀ i ∈ s, ∀ v ∈ D \ S i, G.Adj (p i) v)
    (hcore : ∀ i ∈ s, (∀ v ∈ D, G.Adj (p i) v) ∨
      ((EHP6.nbrs G (p i) D).card : ℝ) ≤ ε * D.card)
    (hred : ∀ r ∈ R, ((B \ EHP6.nbrs G r B).card : ℝ) ≤ η * B.card)
    (hgoodBudget : (s.card : ℝ) * (δ + ε) ≤ 1 / 8)
    (hredBudget : (R.card : ℝ) * η * B.card ≤ (D.card : ℝ) / 16) :
    ∃ E ⊆ D, 13 * (D.card : ℝ) / 16 ≤ E.card ∧
      (∀ i ∈ s, E ⊆ S i ∨ Disjoint E (S i)) ∧
      ∀ r ∈ R, ∀ v ∈ E, G.Adj r v := by
  obtain ⟨D', hD'D, hsizeD', htypes⟩ :=
    purify_good_core G D s p S δ ε hδ hε hsmall hcompleteType hcore
  obtain ⟨E, hED', hsizeE, hroots⟩ :=
    exactify_red_roots G B D' R η (hD'D.trans hD) hred
  refine ⟨E, hED'.trans hD'D, ?_, ?_, hroots⟩
  · have hc : (0 : ℝ) ≤ D.card := by positivity
    have hg := mul_le_mul_of_nonneg_right hgoodBudget hc
    nlinarith
  · intro i hi
    rcases htypes i hi with h | h
    · exact Or.inl (hED'.trans h)
    · exact Or.inr (Finset.disjoint_left.mpr
        (fun _ hv hs => Finset.disjoint_left.mp h (hED' hv) hs))

/-- The paper's simultaneous deletion constants; its m ≥ 2^16 is stronger than needed here. -/
theorem rp5_deletion_constants (m τ θ : ℝ) (hm : 4 ≤ m) (hτ : τ ≤ 1)
    (hθ : θ ≤ τ / (256 * m ^ 5)) :
    m * (1 / (4 * m ^ 2) + θ * m / (1 / (16 * m ^ 3))) ≤ 1 / 8 ∧
      m ^ 2 * (1 / (16 * m ^ 3)) * m ≤ 1 / 16 := by
  have hm0 : 0 < m := by linarith
  have hmp : 0 < 256 * m ^ 5 := by positivity
  have hθ' := (le_div_iff₀ hmp).mp hθ
  have hfrac : 1 / (4 * m) ≤ (1 : ℝ) / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * m)).mpr
    linarith
  have heq : m * (1 / (4 * m ^ 2) + θ * m / (1 / (16 * m ^ 3))) =
      1 / (4 * m) + 16 * θ * m ^ 5 := by field_simp
  have heq' : m ^ 2 * (1 / (16 * m ^ 3)) * m = (1 : ℝ) / 16 := by
    field_simp
  constructor
  · rw [heq]
    nlinarith
  · exact heq'.le

/-- The simultaneous root-family purification in III.2, with explicit numeric budgets.
    This makes exactly one Tooth call on the representative set and preserves all early outputs.
    The representative's separating root may depend on its index. -/
theorem rp5_simultaneous_purification {V ι : Type} [Fintype V] [DecidableEq V]
    [DecidableEq ι] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y B R : Finset V} (s : Finset ι) (p : ι → V) (S : ι → Finset V)
    {x a η : ℝ} {k : ℕ}
    (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20) (ha : 0 ≤ a) (hη : 0 ≤ η)
    (hk : 2 ^ 16 ≤ k) (hkx : (k : ℝ) ≤ 2 / Real.sqrt x)
    (hn : 16 / x ^ 3 ≤ (B.card : ℝ)) (hB : B ⊆ Y)
    (hpY : ∀ i ∈ s, p i ∈ Y) (hpout : ∀ i ∈ s, p i ∉ B)
    (hsep : ∀ i ∈ s, ∃ r, r ∉ Y ∧ RootedP5Free G Y r ∧
      ¬ G.Adj r (p i) ∧ ∀ b ∈ B, G.Adj r b)
    (hsmall : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤ a * B.card)
    (hcompleteType : ∀ i ∈ s, ∀ v ∈ B \ S i, G.Adj (p i) v)
    (hred : ∀ r ∈ R, ((B \ EHP6.nbrs G r B).card : ℝ) ≤ η * B.card)
    (hgoodBudget : (s.card : ℝ) * (a * k + x / 4) ≤ 1 / 8)
    (hredBudget : (R.card : ℝ) * η * k ≤ 1 / 16) :
    RP4Early G B x k ∨
      ∃ E ⊆ B, (B.card : ℝ) / (2 * k) ≤ E.card ∧
        (∀ i ∈ s, E ⊆ S i ∨ Disjoint E (S i)) ∧
        ∀ r ∈ R, ∀ v ∈ E, G.Adj r v := by
  classical
  let P := s.image p
  have hP : P ⊆ Y := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hpY i hi
  have hout : ∀ v ∈ P, v ∉ B := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hpout i hi
  have hsepP : ∀ v ∈ P, ∃ r, r ∉ Y ∧ RootedP5Free G Y r ∧
      ¬ G.Adj r v ∧ ∀ b ∈ B, G.Adj r b := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hsep i hi
  rcases rp5_representative_tooth G hx hx20 hk hkx hn hB hP hout hsepP with
      early | ⟨D, hDB, hDsize, hDcore⟩
  · exact Or.inl early
  right
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hBk : (B.card : ℝ) ≤ k * D.card := by
    have h := (div_le_iff₀ hkpos).mp hDsize
    nlinarith
  have hsmallD : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤
      (a * k) * D.card := by
    intro i hi
    have h := (hsmall i hi).trans (mul_le_mul_of_nonneg_left hBk ha)
    nlinarith
  have hcompleteD : ∀ i ∈ s, ∀ v ∈ D \ S i, G.Adj (p i) v := by
    intro i hi v hv
    have hmem := Finset.mem_sdiff.mp hv
    exact hcompleteType i hi v (Finset.mem_sdiff.mpr ⟨hDB hmem.1, hmem.2⟩)
  have hcoreD : ∀ i ∈ s, (∀ v ∈ D, G.Adj (p i) v) ∨
      ((EHP6.nbrs G (p i) D).card : ℝ) ≤ (x / 4) * D.card := by
    intro i hi
    rcases hDcore (p i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩) with h | h
    · exact Or.inl h
    · right
      nlinarith
  have hredD : (R.card : ℝ) * η * B.card ≤ (D.card : ℝ) / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hBk
      (mul_nonneg (show (0 : ℝ) ≤ R.card by positivity) hη)
    have h2 := mul_le_mul_of_nonneg_right hredBudget (show (0 : ℝ) ≤ D.card by positivity)
    nlinarith
  obtain ⟨E, hED, hEsize, htypes, hroots⟩ :=
    purify_and_exactify G B D R s p S (a * k) (x / 4) η
      (mul_nonneg ha hkpos.le) (by positivity) hDB
      hsmallD hcompleteD hcoreD hred hgoodBudget hredD
  refine ⟨E, hED.trans hDB, ?_, htypes, hroots⟩
  have hnonneg : (0 : ℝ) ≤ D.card := by positivity
  have heq : (B.card : ℝ) / (2 * k) = (B.card : ℝ) / k / 2 := by ring
  rw [heq]
  nlinarith

/-- Instantiate III.2 with xi=m^-2, eta=1/(16m^3), and the paper's theta bound. -/
theorem rp5_simultaneous_purification_at_paper_parameters
    {V ι : Type} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y B R : Finset V} (s : Finset ι) (p : ι → V) (S : ι → Finset V)
    {m : ℕ} {τ θ : ℝ}
    (hm : 2 ^ 16 ≤ m) (hτ : τ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ τ / (256 * (m : ℝ) ^ 5))
    (hsize : 16 * (m : ℝ) ^ 6 ≤ B.card) (hB : B ⊆ Y)
    (hs : s.card ≤ m) (hR : R.card ≤ m ^ 2)
    (hpY : ∀ i ∈ s, p i ∈ Y) (hpout : ∀ i ∈ s, p i ∉ B)
    (hsep : ∀ i ∈ s, ∃ r, r ∉ Y ∧ RootedP5Free G Y r ∧
      ¬ G.Adj r (p i) ∧ ∀ b ∈ B, G.Adj r b)
    (hsmall : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤
      θ * B.card / (1 / (16 * (m : ℝ) ^ 3)))
    (hcompleteType : ∀ i ∈ s, ∀ v ∈ B \ S i, G.Adj (p i) v)
    (hred : ∀ r ∈ R, ((B \ EHP6.nbrs G r B).card : ℝ) ≤
      (1 / (16 * (m : ℝ) ^ 3)) * B.card) :
    RP4Early G B (1 / (m : ℝ) ^ 2) m ∨
      ∃ E ⊆ B, (B.card : ℝ) / (2 * m) ≤ E.card ∧
        (∀ i ∈ s, E ⊆ S i ∨ Disjoint E (S i)) ∧
        ∀ r ∈ R, ∀ v ∈ E, G.Adj r v := by
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm4 : (4 : ℝ) ≤ m := by linarith
  have hη : (0 : ℝ) < 1 / (16 * (m : ℝ) ^ 3) := by positivity
  have hx : (0 : ℝ) < 1 / (m : ℝ) ^ 2 := by positivity
  have hx20 : 1 / (m : ℝ) ^ 2 ≤ (1 : ℝ) / 2 ^ 20 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)).mpr
    norm_num
    nlinarith
  have hsqrt : Real.sqrt (1 / (m : ℝ) ^ 2) = 1 / (m : ℝ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_sq_eq_abs, abs_of_pos hm0]
  have hkx : (m : ℝ) ≤ 2 / Real.sqrt (1 / (m : ℝ) ^ 2) := by
    rw [hsqrt]
    have h : 2 / (1 / (m : ℝ)) = 2 * m := by field_simp
    rw [h]
    linarith
  have hn : 16 / (1 / (m : ℝ) ^ 2) ^ 3 ≤ (B.card : ℝ) := by
    have h : 16 / (1 / (m : ℝ) ^ 2) ^ 3 = 16 * (m : ℝ) ^ 6 := by field_simp
    rwa [h]
  have hsmall' : ∀ i ∈ s, ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤
      (θ / (1 / (16 * (m : ℝ) ^ 3))) * B.card := by
    intro i hi
    have hh := hsmall i hi
    convert hh using 1 <;> ring
  have hgoodBudget : (s.card : ℝ) *
      (θ / (1 / (16 * (m : ℝ) ^ 3)) * m + (1 / (m : ℝ) ^ 2) / 4) ≤ 1 / 8 := by
    have hsR : (s.card : ℝ) ≤ m := by exact_mod_cast hs
    have hc := mul_le_mul_of_nonneg_right hsR
      (show 0 ≤ θ / (1 / (16 * (m : ℝ) ^ 3)) * m + (1 / (m : ℝ) ^ 2) / 4 by positivity)
    have hb := (rp5_deletion_constants (m : ℝ) τ θ hm4 hτ hθ).1
    have heq : (m : ℝ) * (θ / (1 / (16 * (m : ℝ) ^ 3)) * m + (1 / (m : ℝ) ^ 2) / 4) =
        m * (1 / (4 * (m : ℝ) ^ 2) + θ * m / (1 / (16 * (m : ℝ) ^ 3))) := by ring
    rw [heq] at hc
    exact hc.trans hb
  have hredBudget : (R.card : ℝ) * (1 / (16 * (m : ℝ) ^ 3)) * m ≤ 1 / 16 := by
    have hRR : (R.card : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast hR
    have hc := mul_le_mul_of_nonneg_right hRR
      (show 0 ≤ (1 / (16 * (m : ℝ) ^ 3)) * m by positivity)
    have hb := (rp5_deletion_constants (m : ℝ) τ θ hm4 hτ hθ).2
    nlinarith
  exact rp5_simultaneous_purification G s p S hx hx20 (by positivity) hη.le
    hm hkx hn hB hpY hpout hsep hsmall' hcompleteType hred hgoodBudget hredBudget

#print axioms good_pair_representative
#print axioms delete_family_budget
#print axioms purify_good_core
#print axioms exactify_red_roots
#print axioms purify_and_exactify
#print axioms rp5_deletion_constants
#print axioms rp5_simultaneous_purification
#print axioms rp5_simultaneous_purification_at_paper_parameters

end AllPathsLocal
