import RP5Purification
import RP5RootFamilies

/-! Assemble III.2 on an entire first-round frontier. Good pairs and type sets
    refer to the ORIGINAL first-round blocks throughout both deletion families. -/

namespace AllPathsLocal

open scoped BigOperators

def GoodPair {V : Type} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℕ} (B R : Fin m → Finset V) (η : ℝ)
    (i j : Fin m) : Prop :=
  ∃ r ∈ R j, η * (B i).card ≤ (((B i) \ EHP6.nbrs G r (B i)).card : ℝ)

noncomputable def SparseType {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) : Finset V := by
  classical
  exact B.filter (fun v => ¬ ∀ b ∈ A, G.Adj v b)

@[simp] theorem mem_sparseType {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} {v : V} :
    v ∈ SparseType G A B ↔ v ∈ B ∧ ¬ ∀ b ∈ A, G.Adj v b := by
  classical
  simp [SparseType]

/-- Every root of every red later pair enters one union with quadratic size. -/
theorem red_root_union {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B R : Fin m → Finset V) (η : ℝ) (j : Fin m)
    (hR : ∀ l, (R l).card ≤ m) :
    ∃ T : Finset V, T.card ≤ m ^ 2 ∧
      (∀ r ∈ T, (((B j) \ EHP6.nbrs G r (B j)).card : ℝ) ≤ η * (B j).card) ∧
      ∀ l, j < l → ¬ GoodPair G B R η j l → R l ⊆ T := by
  classical
  let L := Finset.univ.filter (fun l : Fin m => j < l ∧ ¬ GoodPair G B R η j l)
  let T := L.biUnion R
  have hLc : L.card ≤ m := by
    simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin m)))
  refine ⟨T, ?_, ?_, ?_⟩
  · calc
      T.card ≤ ∑ l ∈ L, (R l).card := Finset.card_biUnion_le
      _ ≤ ∑ _l ∈ L, m := Finset.sum_le_sum (fun l _ => hR l)
      _ = L.card * m := by simp
      _ ≤ m ^ 2 := by nlinarith
  · intro r hr
    obtain ⟨l, hl, hr⟩ := Finset.mem_biUnion.mp hr
    have hn := (Finset.mem_filter.mp hl).2.2
    by_contra h
    exact hn ⟨r, hr, (lt_of_not_ge h).le⟩
  · intro l hjl hn r hr
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjl, hn⟩, hr⟩

/-- A whole column is purified with one representative Tooth call. No representative
    or separating-root existence is an extra hypothesis: they are chosen from GoodPair. -/
theorem frontier_column_purification {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B R : Fin m → Finset V) {U Y : Finset V} {τ θ : ℝ}
    (hm : 2 ^ 16 ≤ m) (hτ : τ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ τ / (256 * (m : ℝ) ^ 5))
    (hsize : ∀ i, 16 * (m : ℝ) ^ 6 ≤ (B i).card)
    (hBY : ∀ i, B i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hRU : ∀ i, R i ⊆ U) (hRc : ∀ i, (R i).card ≤ m)
    (hrootfull : ∀ j, ∀ r ∈ R j, ∀ v ∈ B j, G.Adj r v)
    (hout : ∀ r ∈ U, r ∉ Y) (hP5 : ∀ r ∈ U, RootedP5Free G Y r)
    (htypes : ∀ i j, i < j → ∀ v ∈ B j,
      (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card)
    (j : Fin m) :
    RP4Early G (B j) (1 / (m : ℝ) ^ 2) m ∨
      ∃ E ⊆ B j, ((B j).card : ℝ) / (2 * m) ≤ E.card ∧
        (∀ i, i < j → GoodPair G B R (1 / (16 * (m : ℝ) ^ 3)) i j →
          (∀ v ∈ E, ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) ∨
          (∀ v ∈ E, ∀ b ∈ B i, G.Adj v b)) ∧
        ∀ l, j < l → ¬ GoodPair G B R (1 / (16 * (m : ℝ) ^ 3)) j l →
          ∀ r ∈ R l, ∀ v ∈ E, G.Adj r v := by
  classical
  let η : ℝ := 1 / (16 * (m : ℝ) ^ 3)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hη : 0 < η := by dsimp [η]; positivity
  let I := Finset.univ.filter (fun i : Fin m => i < j ∧ GoodPair G B R η i j)
  have hI : I.card ≤ m := by
    simpa using Finset.card_le_card (Finset.filter_subset _ (Finset.univ : Finset (Fin m)))
  have hrep : ∀ i : I, ∃ p ∈ B i.val, ∃ r ∈ R j, ¬ G.Adj r p ∧
      ((EHP6.nbrs G p (SparseType G (B i.val) (B j))).card : ℝ) ≤ θ * (B j).card / η := by
    intro i
    have hi := (Finset.mem_filter.mp i.prop).2
    obtain ⟨r, hr, hgood⟩ := hi.2
    have hA : (B i.val).Nonempty := by
      apply Finset.card_pos.mp
      have hpos : (0 : ℝ) < (B i.val).card := lt_of_lt_of_le (by positivity) (hsize i.val)
      exact_mod_cast hpos
    have hSB : SparseType G (B i.val) (B j) ⊆ B j := by
      intro v hv
      exact (mem_sparseType G |>.mp hv).1
    have hsparse : ∀ v ∈ SparseType G (B i.val) (B j),
        ((EHP6.nbrs G v (B i.val)).card : ℝ) ≤ θ * (B i.val).card := by
      intro v hv
      have hv' := (mem_sparseType G).mp hv
      exact ((htypes i.val j hi.1 v hv'.1).resolve_left hv'.2).le
    obtain ⟨p, hp, hnot, hsmall⟩ :=
      good_pair_representative G (B i.val) (B j) (SparseType G (B i.val) (B j)) r θ η
        hA hSB hθ0 hη hgood hsparse
    exact ⟨p, hp, r, hr, hnot, hsmall⟩
  choose p hp r hr hnot hsmall using hrep
  obtain ⟨T, hTc, hTsmall, hTcover⟩ := red_root_union G B R η j hRc
  have hpY : ∀ i ∈ (Finset.univ : Finset I), p i ∈ Y := by
    intro i _
    exact hBY i.val (hp i)
  have hpout : ∀ i ∈ (Finset.univ : Finset I), p i ∉ B j := by
    intro i _ hj
    exact Finset.disjoint_left.mp (hdisj (ne_of_lt (Finset.mem_filter.mp i.prop).2.1)) (hp i) hj
  have hsep : ∀ i ∈ (Finset.univ : Finset I), ∃ u, u ∉ Y ∧ RootedP5Free G Y u ∧
      ¬ G.Adj u (p i) ∧ ∀ b ∈ B j, G.Adj u b := by
    intro i _
    have hu := hRU j (hr i)
    exact ⟨r i, hout _ hu, hP5 _ hu, hnot i, hrootfull j (r i) (hr i)⟩
  have hcomplete : ∀ i ∈ (Finset.univ : Finset I),
      ∀ v ∈ B j \ SparseType G (B i.val) (B j), G.Adj (p i) v := by
    intro i _ v hv
    have hv' := Finset.mem_sdiff.mp hv
    have hf : ∀ b ∈ B i.val, G.Adj v b := by
      by_contra hn
      exact hv'.2 ((mem_sparseType G).mpr ⟨hv'.1, hn⟩)
    exact (hf _ (hp i)).symm
  have hs : (Finset.univ : Finset I).card ≤ m := by simpa using hI
  rcases rp5_simultaneous_purification_at_paper_parameters G
      (Finset.univ : Finset I) p (fun i => SparseType G (B i.val) (B j))
      hm hτ hθ0 hθ (hsize j) (hBY j) hs hTc hpY hpout hsep
      (fun i _ => hsmall i) hcomplete hTsmall with early | ⟨E, hEB, hEc, hEt, hEr⟩
  · exact Or.inl early
  right
  refine ⟨E, hEB, hEc, ?_, ?_⟩
  · intro i hij hg
    have hi : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hg⟩
    rcases hEt ⟨i, hi⟩ (Finset.mem_univ _) with hsub | hnon
    · left
      intro v hv
      have hv' := (mem_sparseType G).mp (hsub hv)
      exact (htypes i j hij v hv'.1).resolve_left hv'.2
    · right
      intro v hv
      by_contra hn
      exact Finset.disjoint_left.mp hnon hv ((mem_sparseType G).mpr ⟨hEB hv, hn⟩)
  · intro l hjl hn u hu v hv
    exact hEr u (hTcover l hjl hn hu) v hv

/-- Purify every frontier block, keeping a genuine early output whenever any Tooth
    invocation returns one. Uniform types always refer to the original B_i. -/
theorem frontier_second_round {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (B R : Fin m → Finset V) {U Y : Finset V} {τ θ : ℝ}
    (hm : 2 ^ 16 ≤ m) (hτ : τ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ τ / (256 * (m : ℝ) ^ 5))
    (hsize : ∀ i, 16 * (m : ℝ) ^ 6 ≤ (B i).card)
    (hBY : ∀ i, B i ⊆ Y) (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hRU : ∀ i, R i ⊆ U) (hRc : ∀ i, (R i).card ≤ m)
    (hrootfull : ∀ j, ∀ r ∈ R j, ∀ v ∈ B j, G.Adj r v)
    (hout : ∀ r ∈ U, r ∉ Y) (hP5 : ∀ r ∈ U, RootedP5Free G Y r)
    (htypes : ∀ i j, i < j → ∀ v ∈ B j,
      (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) :
    (∃ j, RP4Early G (B j) (1 / (m : ℝ) ^ 2) m) ∨
      ∃ E : Fin m → Finset V,
        (∀ i, E i ⊆ B i ∧ ((B i).card : ℝ) / (2 * m) ≤ (E i).card) ∧
        Pairwise (fun i j => Disjoint (E i) (E j)) ∧
        (∀ i j, i < j → GoodPair G B R (1 / (16 * (m : ℝ) ^ 3)) i j →
          (∀ v ∈ E j, ((EHP6.nbrs G v (B i)).card : ℝ) < θ * (B i).card) ∨
          (∀ v ∈ E j, ∀ b ∈ B i, G.Adj v b)) ∧
        ∀ i j, i < j → ¬ GoodPair G B R (1 / (16 * (m : ℝ) ^ 3)) i j →
          ∀ r ∈ R j, ∀ v ∈ E i, G.Adj r v := by
  classical
  by_cases hearly : ∃ j, RP4Early G (B j) (1 / (m : ℝ) ^ 2) m
  · exact Or.inl hearly
  right
  have hc := fun j => (frontier_column_purification G B R hm hτ hθ0 hθ hsize
    hBY hdisj hRU hRc hrootfull hout hP5 htypes j).resolve_left (fun h => hearly ⟨j, h⟩)
  choose E hEB hEc hEt hEr using hc
  refine ⟨E, fun i => ⟨hEB i, hEc i⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact Finset.disjoint_left.mpr (fun _ hi hj =>
      Finset.disjoint_left.mp (hdisj hij) (hEB i hi) (hEB j hj))
  · intro i j hij hg
    exact hEt j i hij hg
  · intro i j hij hn
    exact hEr i j hij hn

#print axioms red_root_union
#print axioms mem_sparseType
#print axioms frontier_column_purification
#print axioms frontier_second_round

end AllPathsLocal
