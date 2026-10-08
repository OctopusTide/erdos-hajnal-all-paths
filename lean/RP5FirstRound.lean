import RP5Frontier

/-! Apply the original checked Tooth theorem to every actual ordered-frontier block,
    simultaneously against all later ORIGINAL blocks, as required by III.4. -/

namespace AllPathsLocal

theorem frontier_first_tooth_round {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
    {S : Finset V} {Z : List (Finset V)} (hfront : OrderedCutFrontier G U S Z)
    (hSY : S ⊆ Y) (houtside : ∀ u ∈ U, u ∉ Y)
    (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20)
    (hk : 2 ^ 16 ≤ k) (hkx : (k : ℝ) ≤ 2 / Real.sqrt x)
    (hlarge : ∀ i : Fin Z.length, 16 / x ^ 3 ≤ ((Z.get i).card : ℝ)) :
    (∃ i : Fin Z.length, RP4Early G (Z.get i) x k) ∨
      ∃ B : Fin Z.length → Finset V,
        (∀ i, B i ⊆ Z.get i) ∧
        (∀ i, ((Z.get i).card : ℝ) / k ≤ (B i).card) ∧
        (∀ i j, i < j → ∀ v ∈ Z.get j,
          (∀ b ∈ B i, G.Adj v b) ∨ ((EHP6.nbrs G v (B i)).card : ℝ) < x * (B i).card / 4) ∧
        ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
  classical
  have hroot := ordered_frontier_root_law G U Y hfront hSY houtside hfree
  have hpair (i j : Fin Z.length) (hij : i < j) :
      Disjoint (Z.get i) (Z.get j) ∧ ∀ v ∈ Z.get j, RootedP4Free G (Z.get i) v := by
    exact List.Pairwise.rel_getElem_of_lt i.isLt j.isLt hroot hij
  have hstep : ∀ i : Fin Z.length,
      RP4Early G (Z.get i) x k ∨ ∃ D ⊆ Z.get i,
        ((Z.get i).card : ℝ) / k ≤ D.card ∧
        ∀ j, i < j → ∀ v ∈ Z.get j,
          (∀ b ∈ D, G.Adj v b) ∨ ((EHP6.nbrs G v D).card : ℝ) < x * D.card / 4 := by
    intro i
    let later := Finset.univ.filter (fun j : Fin Z.length => i < j)
    let R : Finset V := later.biUnion (fun j => Z.get j)
    have hRout : ∀ v ∈ R, v ∉ Z.get i := by
      intro v hv hvI
      obtain ⟨j, hj, hvJ⟩ := Finset.mem_biUnion.mp hv
      have hij := (Finset.mem_filter.mp hj).2
      exact Finset.disjoint_left.mp (hpair i j hij).1 hvI hvJ
    have hRfree : ∀ v ∈ R, RootedP4Free G (Z.get i) v := by
      intro v hv
      obtain ⟨j, hj, hvJ⟩ := Finset.mem_biUnion.mp hv
      exact (hpair i j (Finset.mem_filter.mp hj).2).2 v hvJ
    rcases rp4_tooth G hx hx20 hk hkx (Z.get i) R (hlarge i) hRout hRfree with
      early | early | early | early | ⟨D, hD, hsize, htypes⟩
    · exact Or.inl (Or.inl early)
    · exact Or.inl (Or.inr (Or.inl early))
    · exact Or.inl (Or.inr (Or.inr (Or.inl early)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr early)))
    · right
      refine ⟨D, hD, hsize, ?_⟩
      intro j hij v hv
      apply htypes v
      exact Finset.mem_biUnion.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hv⟩
  by_cases hearly : ∃ i : Fin Z.length, RP4Early G (Z.get i) x k
  · exact Or.inl hearly
  right
  have hcores : ∀ i : Fin Z.length, ∃ D ⊆ Z.get i,
      ((Z.get i).card : ℝ) / k ≤ D.card ∧
      ∀ j, i < j → ∀ v ∈ Z.get j,
        (∀ b ∈ D, G.Adj v b) ∨ ((EHP6.nbrs G v D).card : ℝ) < x * D.card / 4 := by
    intro i
    exact (hstep i).resolve_left (fun h => hearly ⟨i, h⟩)
  choose B hsub hsize htypes using hcores
  refine ⟨B, hsub, hsize, htypes, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hpair i j h).1.mono (hsub i) (hsub j)
  · exact (hpair j i h).1.symm.mono (hsub i) (hsub j)

#print axioms frontier_first_tooth_round

end AllPathsLocal
