import RP5FrontierPipeline

namespace AllPathsLocal

theorem ordered_family_first_tooth_round {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
    {Z : List (Finset V)}
    (hroot : Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v)) (houtside : ∀ u ∈ U, u ∉ Y)
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


theorem separated_family_recorded_root_law {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
    {Z : List (Finset V)}
    (hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j))
    (C R : Fin Z.length → Finset V) (hCZ : ∀ i, C i ⊆ Z.get i)
    (hRU : ∀ i, R i ⊆ U)
    (hrecord : ∀ j l, j < l → (∃ u ∈ U, RootSeparates G u (Z.get j) (Z.get l)) →
      ∃ u ∈ R j, RootSeparates G u (Z.get j) (Z.get l))
    (hred : ∀ i j, i < j → MixedPair G C i j → ∀ u ∈ R j, ∀ v ∈ C i, G.Adj u v)
    {n : ℕ} (f : Fin n → Fin Z.length) (hf : StrictMono f)
    (hlinks : ∀ a b : Fin n, a.val + 1 = b.val → MixedPair G C (f a) (f b)) :
    ∀ a b c : Fin n, a.val + 1 = b.val → b < c →
      ∃ u ∈ U, (∀ v ∈ C (f a), G.Adj u v) ∧
        (∀ v ∈ C (f b), G.Adj u v) ∧ ∀ v ∈ C (f c), ¬ G.Adj u v := by
  intro a b c hab hbc
  obtain ⟨u, huR, hsep⟩ := hrecord (f b) (f c) (hf hbc) (hseparator (f b) (f c) (hf hbc))
  have hab' : a < b := by show a.val < b.val; omega
  exact ⟨u, hRU (f b) huR, hred (f a) (f b) (hf hab') (hlinks a b hab) u huR,
    fun v hv => hsep.1 v (hCZ (f b) hv), fun v hv => hsep.2 v (hCZ (f c) hv)⟩


theorem separated_family_component_blockade {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
    {Z : List (Finset V)}
    (hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j))
    (C R : Fin Z.length → Finset V) {r : ℕ} {β w : ℝ}
    (hr : 2 ≤ r) (hcount : r * (r - 1) ≤ Z.length)
    (hCZ : ∀ i, C i ⊆ Z.get i) (hCY : ∀ i, C i ⊆ Y)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hconn : ∀ i, EHP6.AntiConnected G (C i))
    (hβ0 : 0 ≤ β) (hβ : 2 * β ≤ 1) (hw : 0 ≤ w)
    (hwidth : ∀ i, w ≤ ((C i).card : ℝ))
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (htypes : ∀ i j, i < j → ∀ v ∈ C j,
      (∀ b ∈ C i, G.Adj v b) ∨ ((EHP6.nbrs G v (C i)).card : ℝ) < β * (C i).card)
    (hRU : ∀ i, R i ⊆ U)
    (hrecord : ∀ j l, j < l → (∃ u ∈ U, RootSeparates G u (Z.get j) (Z.get l)) →
      ∃ u ∈ R j, RootSeparates G u (Z.get j) (Z.get l))
    (hred : ∀ i j, i < j → MixedPair G C i j → ∀ u ∈ R j, ∀ v ∈ C i, G.Adj u v) :
    ∃ γ : EHP6.Blockade Y r (w / r), γ.m = r ∧
      ∀ i j, i < j → EHP6.Complete G (γ.B i) (γ.B j) ∨
        EHP6.SparseTo G (r * β) (γ.B j) (γ.B i) := by
  rcases increasing_path_or_large_independent_level (MixedPair G C) hr with
    ⟨last, hp⟩ | ⟨I, hIc, hIind⟩
  · obtain ⟨_, f, hf, _, _, hlinks⟩ := increasingQPath_sequence hp
    exact mixed_path_blockade G Y U C (by omega) hCY hdisj hconn hβ0 hβ hwidth
      hout hfree htypes f hf hlinks
      (separated_family_recorded_root_law G U hseparator C R hCZ hRU hrecord hred f hf hlinks)
  · have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hcountR : (r : ℝ) * (r - 1) ≤ Z.length := by
      simpa only [Nat.cast_mul, hcast] using (show ((r * (r - 1) : ℕ) : ℝ) ≤ Z.length by exact_mod_cast hcount)
    have hrI : (r : ℝ) ≤ I.card :=
      ((le_div_iff₀ (by linarith : (0 : ℝ) < r - 1)).mpr hcountR).trans hIc
    exact independent_level_blockade G Y C (by omega) hβ0 hw hCY hdisj hwidth htypes
      I (by exact_mod_cast hrI) hIind


#print axioms ordered_family_first_tooth_round
#print axioms separated_family_recorded_root_law
#print axioms separated_family_component_blockade

section Pipeline

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (U Y : Finset V)
variable {Z : List (Finset V)}

local notation "m" => Z.length

/-- Actual two-Tooth frontier construction, including all early branches. Scalar
    bounds are exposed explicitly so the subsequent paper-parameter instantiation
    can be checked independently. No graph-theoretic result is assumed. -/
theorem separated_family_pipeline
    (hsub : ∀ K ∈ Z, K ⊆ Y)
    (hroot : Z.Pairwise (fun A B => Disjoint A B ∧ ∀ v ∈ B, RootedP4Free G A v))
    (hseparator : ∀ i j : Fin Z.length, i < j → ∃ u ∈ U, RootSeparates G u (Z.get i) (Z.get j))
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
    exact hsub _ (List.get_mem Z i)
  rcases ordered_family_first_tooth_round G U Y hroot hout hfree hx hx20 hm hkx hlarge with
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
  obtain ⟨γ, hγm, hγtypes⟩ := separated_family_component_blockade G U Y hseparator C R hr hcount
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

#print axioms separated_family_pipeline

end Pipeline

end AllPathsLocal
