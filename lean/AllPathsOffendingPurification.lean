import AllPathsOffendingRepresentative

namespace AllPathsLocal

/-- The full third RP6 purification at explicit general-Tooth parameters.
    Representatives are selected from ORIGINAL offending witnesses, one actual
    RP4 Tooth call is made, all four early outputs are preserved, and one union
    deletion makes every offending pair uniform in its ORIGINAL frozen type.
    The RP6 frontier's specific scalar parameter substitution remains separate. -/
theorem rp6_offending_purification {V ι : Type} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y J : Finset V) (I S : ι → Finset V) (r z : ι → V)
    (beta xi : ℝ) (k : ℕ)
    (hI : ∀ i, (I i).Nonempty) (hIY : ∀ i, I i ⊆ Y) (hJY : J ⊆ Y)
    (hIJ : ∀ i, Disjoint (I i) J) (hSJ : ∀ i, S i ⊆ J)
    (hr : ∀ i, r i ∉ Y) (hz : ∀ i, z i ∈ Y)
    (hzI : ∀ i, z i ∉ I i) (hzJ : ∀ i, z i ∉ J)
    (hfree : ∀ i, RootedPathFree G 6 Y (r i)) (hrz : ∀ i, ¬ G.Adj (r i) (z i))
    (hrI : ∀ i, ∀ a ∈ I i, G.Adj (r i) a) (hrJ : ∀ i, ∀ a ∈ J, G.Adj (r i) a)
    (hzFull : ∀ i, ∀ a ∈ J, G.Adj (z i) a)
    (hbeta : 0 ≤ beta) (hbetaSmall : beta ≤ 1/2)
    (hzSparse : ∀ i, ((EHP6.nbrs G (z i) (I i)).card : ℝ) ≤ beta*(I i).card)
    (hSparseType : ∀ i, ∀ v ∈ S i, ((EHP6.nbrs G v (I i)).card : ℝ) ≤ beta*(I i).card)
    (hFullType : ∀ i, ∀ v ∈ J \ S i, ∀ a ∈ I i, G.Adj a v)
    (hxi : 0 < xi) (hxiSmall : xi ≤ 1/2^20) (hk : 2^16 ≤ k)
    (hkxi : (k : ℝ) ≤ 2/Real.sqrt xi) (hn : 16/xi^3 ≤ (J.card : ℝ))
    (hbudget : (Fintype.card ι : ℝ)*(2*beta*k+xi/4) ≤ 1/2) :
    RP4Early G J xi k ∨ ∃ E ⊆ J, (J.card : ℝ)/(2*k) ≤ E.card ∧
      ∀ i, E ⊆ S i ∨ Disjoint E (S i) := by
  classical
  have hrep : ∀ i, ∃ p ∈ I i, ¬ G.Adj (z i) p ∧ RootedPathFree G 4 J p ∧
      ((EHP6.nbrs G p (S i)).card : ℝ) ≤ 2*beta*J.card := by
    intro i
    exact offending_pair_representative G 3 Y (I i) J (S i) (r i) (z i) beta
      (hI i) (hIY i) hJY (hSJ i) (hr i) (hz i) (hzI i) (hzJ i)
      (hfree i) (hrz i) (hrI i) (hrJ i) (hzFull i) hbeta hbetaSmall
      (hzSparse i) (hSparseType i)
  choose p hpI hpz hpFree hpDegree using hrep
  let P := Finset.univ.image p
  have hpOut : ∀ a ∈ P, a ∉ J := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact fun hj => Finset.disjoint_left.mp (hIJ i) (hpI i) hj
  have hpRoot : ∀ a ∈ P, RootedP4Free G J a := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (rooted_path_free_four G J (p i)).mp (hpFree i)
  have result : RP4Early G J xi k ∨ ∃ D ⊆ J, (J.card : ℝ)/k ≤ D.card ∧
      ∀ a ∈ P, (∀ v ∈ D, G.Adj a v) ∨ ((EHP6.nbrs G a D).card : ℝ) < xi*D.card/4 := by
    rcases rp4_tooth G hxi hxiSmall hk hkxi J P hn hpOut hpRoot with h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr h
  rcases result with early | ⟨D, hDJ, hDsize, hcore⟩
  · exact Or.inl early
  right
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hJk : (J.card : ℝ) ≤ k*D.card := by
    have hh := (div_le_iff₀ hk0).mp hDsize
    nlinarith
  have hsmallD : ∀ i ∈ (Finset.univ : Finset ι),
      ((EHP6.nbrs G (p i) (S i)).card : ℝ) ≤ (2*beta*k)*D.card := by
    intro i _
    have hh := (hpDegree i).trans (mul_le_mul_of_nonneg_left hJk (by positivity : 0 ≤ 2*beta))
    nlinarith
  have hfullD : ∀ i ∈ (Finset.univ : Finset ι), ∀ v ∈ D \ S i, G.Adj (p i) v := by
    intro i _ v hv
    obtain ⟨hvD, hvS⟩ := Finset.mem_sdiff.mp hv
    exact hFullType i v (Finset.mem_sdiff.mpr ⟨hDJ hvD, hvS⟩) (p i) (hpI i)
  have hcoreD : ∀ i ∈ (Finset.univ : Finset ι), (∀ v ∈ D, G.Adj (p i) v) ∨
      ((EHP6.nbrs G (p i) D).card : ℝ) ≤ (xi/4)*D.card := by
    intro i _
    rcases hcore (p i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (by nlinarith)
  obtain ⟨E, hED, hsize, htypes⟩ := purify_good_core G D Finset.univ p S (2*beta*k) (xi/4)
    (by positivity) (by positivity) hsmallD hfullD hcoreD
  have hsizeE : (D.card : ℝ)/2 ≤ E.card := by
    simp only [Finset.card_univ] at hsize
    have hh := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg D.card : (0 : ℝ) ≤ D.card)
    nlinarith
  have hfinal : (J.card : ℝ)/(2*k) ≤ E.card := by
    have hh := div_le_div_of_nonneg_right hDsize (by norm_num : (0 : ℝ) ≤ 2)
    have he : ((J.card : ℝ)/k)/2 = (J.card : ℝ)/(2*k) := by ring
    rw [he] at hh
    exact hh.trans hsizeE
  exact ⟨E, hED.trans hDJ, hfinal, fun i => htypes i (Finset.mem_univ _)⟩

#print axioms rp6_offending_purification
end AllPathsLocal
