import RP5Structure
import EHP6.NSSL41

/-! Exact grouping interfaces for P7_from_P6_English_proof.txt III.3 and III.5.
    The original NSSL41 theorem already proves the sharp grouping bound. -/

namespace AllPathsLocal

/-- A length lower bound may be truncated to exactly k blocks without reducing width. -/
theorem exact_length_complete_blockade {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y : Finset V} {k : ℕ} {w : ℝ} (β : EHP6.Blockade Y k w)
    (hβ : β.IsComplete G) :
    ∃ γ : EHP6.Blockade Y k w, γ.m = k ∧ γ.IsComplete G := by
  have hkm : k ≤ β.m := by exact_mod_cast β.len
  let e : Fin k → Fin β.m := Fin.castLE hkm
  have he : Function.Injective e := Fin.castLE_injective hkm
  refine ⟨⟨k, fun i => β.B (e i), le_rfl, fun i => β.sub (e i),
    fun i => β.wid (e i), fun i j hij => β.disj (e i) (e j) (fun h => hij (he h))⟩,
    rfl, ?_⟩
  intro i j hij
  exact hβ (e i) (e j) (fun h => hij (he h))

/-- The connected-component choice in III.3: a large anticomponent, or an exact length-k
    complete blockade of width |Y|/k^2. -/
theorem large_anticomponent_or_grouping {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Y : Finset V) (k : ℕ) (hk : 2 ≤ k) :
    (∃ K, EHP6.IsAnticomponent G Y K ∧ (Y.card : ℝ) / k ≤ K.card) ∨
      (∃ γ : EHP6.Blockade Y k (Y.card / (k : ℝ) ^ 2), γ.m = k ∧ γ.IsComplete G) := by
  by_cases h : ∃ K, EHP6.IsAnticomponent G Y K ∧ (Y.card : ℝ) / k ≤ K.card
  · exact Or.inl h
  right
  have hsmall : ∀ K, EHP6.IsAnticomponent G Y K → (K.card : ℝ) < Y.card / k := by
    intro K hK
    by_contra! hge
    exact h ⟨K, hK, hge⟩
  obtain ⟨β, hβ⟩ := EHP6.nss_L41_proof (G := G) Y k hk hsmall
  exact exact_length_complete_blockade G β hβ

/-- An anticonnected set cannot straddle two members of a pairwise-complete cover. -/
theorem anticonnected_subset_complete_cover {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y K : Finset V) (𝒜 : Finset (Finset V))
    (hKY : K ⊆ Y) (hKne : K.Nonempty) (hKconn : EHP6.AntiConnected G K)
    (hcover : 𝒜.biUnion id = Y)
    (hcomp : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → EHP6.Complete G A B) :
    ∃ A ∈ 𝒜, K ⊆ A := by
  classical
  obtain ⟨v, hvK⟩ := hKne
  have hvY := hKY hvK
  rw [← hcover] at hvY
  obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hvY
  refine ⟨A, hA, ?_⟩
  by_contra hsub
  obtain ⟨w, hwK, hwA⟩ := Finset.not_subset.mp hsub
  obtain ⟨p, hp, q, hq, hpq⟩ := hKconn (K ∩ A) Finset.inter_subset_left
    ⟨v, Finset.mem_inter.mpr ⟨hvK, hvA⟩⟩
    ⟨w, Finset.mem_sdiff.mpr ⟨hwK, fun hh => hwA (Finset.mem_inter.mp hh).2⟩⟩
  have hpA := (Finset.mem_inter.mp hp).2
  obtain ⟨hqK, hqn⟩ := Finset.mem_sdiff.mp hq
  have hqA : q ∉ A := fun hh => hqn (Finset.mem_inter.mpr ⟨hqK, hh⟩)
  have hqY := hKY hqK
  rw [← hcover] at hqY
  obtain ⟨B, hB, hqB⟩ := Finset.mem_biUnion.mp hqY
  have hAB : A ≠ B := fun heq => hqA (heq ▸ hqB)
  exact hpq (hcomp A hA B hB hAB p hpA q hqB)

/-- The arbitrary small-C-sibling grouping used in III.5; no component enumeration
    or rounding assumption is added. Actual output length is exactly k. -/
theorem complete_small_atoms_grouping {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (𝒜 : Finset (Finset V)) (k : ℕ) (hk : 2 ≤ k)
    (hcover : 𝒜.biUnion id = Y)
    (hcomp : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, A ≠ B → EHP6.Complete G A B)
    (hsmall : ∀ A ∈ 𝒜, (A.card : ℝ) < (Y.card : ℝ) / k) :
    ∃ γ : EHP6.Blockade Y k (Y.card / (k : ℝ) ^ 2), γ.m = k ∧ γ.IsComplete G := by
  have hKsmall : ∀ K, EHP6.IsAnticomponent G Y K → (K.card : ℝ) < Y.card / k := by
    intro K hK
    obtain ⟨A, hA, hKA⟩ := anticonnected_subset_complete_cover G Y K 𝒜
      hK.1 hK.2.1 hK.2.2.1 hcover hcomp
    have hc : (K.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hKA
    exact hc.trans_lt (hsmall A hA)
  obtain ⟨β, hβ⟩ := EHP6.nss_L41_proof (G := G) Y k hk hKsmall
  exact exact_length_complete_blockade G β hβ

#print axioms exact_length_complete_blockade
#print axioms large_anticomponent_or_grouping
#print axioms anticonnected_subset_complete_cover
#print axioms complete_small_atoms_grouping

end AllPathsLocal
