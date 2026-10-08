import AllPathsEHThinLayer

namespace AllPathsLocal

/-- The actual offending-pair representative for the third RPq purification.
    Averaging chooses a nonneighbour of the fixed original witness z; the
    ORIGINAL root r then supplies the two-prefix RP(q-2) exclusion. For n=3
    this is exactly the RP6-to-RP4 representative required by the general Tooth. -/
theorem offending_pair_representative {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (Y I J S : Finset V) (r z : V) (beta : ℝ)
    (hI : I.Nonempty) (hIY : I ⊆ Y) (hJY : J ⊆ Y) (hSJ : S ⊆ J)
    (hr : r ∉ Y) (hz : z ∈ Y) (hzI : z ∉ I) (hzJ : z ∉ J)
    (hfree : RootedPathFree G (n+3) Y r) (hrz : ¬ G.Adj r z)
    (hrI : ∀ a ∈ I, G.Adj r a) (hrJ : ∀ a ∈ J, G.Adj r a)
    (hzFull : ∀ a ∈ J, G.Adj z a)
    (hbeta : 0 ≤ beta) (hbetaSmall : beta ≤ 1/2)
    (hzSparse : ((EHP6.nbrs G z I).card : ℝ) ≤ beta*I.card)
    (hSparseType : ∀ v ∈ S, ((EHP6.nbrs G v I).card : ℝ) ≤ beta*I.card) :
    ∃ p ∈ I, ¬ G.Adj z p ∧ RootedPathFree G (n+1) J p ∧
      ((EHP6.nbrs G p S).card : ℝ) ≤ 2*beta*J.card := by
  classical
  have hmass : (I.card : ℝ) ≤ (I \ EHP6.nbrs G z I).card + (EHP6.nbrs G z I).card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := I) (t := EHP6.nbrs G z I))
  have hgood : (1/2 : ℝ)*I.card ≤ (I \ EHP6.nbrs G z I).card := by
    have hb := mul_le_mul_of_nonneg_right hbetaSmall (Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)
    nlinarith
  obtain ⟨p, hpI, hzp, hdegree⟩ := good_pair_representative G I J S z beta (1/2)
    hI hSJ hbeta (by norm_num) hgood hSparseType
  have hzpNe : z ≠ p := fun he => hzI (he ▸ hpI)
  have hpFree := rooted_path_free_two_prefix G n hr hz (hIY hpI) hJY hzJ hzpNe
    hfree hrz hzp (hrI p hpI) hrJ hzFull
  refine ⟨p, hpI, hzp, hpFree, ?_⟩
  convert hdegree using 1 <;> ring

#print axioms offending_pair_representative
end AllPathsLocal
