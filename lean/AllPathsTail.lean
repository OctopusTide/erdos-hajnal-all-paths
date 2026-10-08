import AllPathsCombGen
import AllPathsNegativeBridge

/-!
# Ordered tails: from the contract `T_(n+1)` to EH of the ordered class

Main paper, Sections "Ordered-tail transfer without circularity" and "Ordered tails
and the relative ordered-class EH interface". A graph `G` whose complement has no
induced `P_s` and carries an order in which the first vertex of every induced
`P_(n+1)` is not an endpoint: the last `⌈y|S|⌉` vertices of a `y^3`-sparse set `S`
are the target of the contract `T_(n+1)`, all earlier vertices are its roots, and the
three outcomes are the variable-scale local oracle. The bootstrap then gives
generalized niceness and, with Rödl's theorem for the complement of `P_s` and an
EH exponent of `P_(s-1)`, the EH property of the ordered class — the hypothesis
`OrderedClassEH` of the negative branch of the next rooted order.
-/

namespace AllPathsLocal

open Finset Classical

/-- The `m` largest elements of a finite set in a linear order. -/
theorem exists_upper_subset {W : Type} (ord : LinearOrder W) :
    ∀ (m : ℕ) (S : Finset W), m ≤ S.card →
      ∃ Y ⊆ S, Y.card = m ∧ ∀ u ∈ S, u ∉ Y → ∀ v ∈ Y, @LT.lt W ord.toLT u v := by
  letI := ord
  intro m
  induction m with
  | zero =>
    intro S _
    exact ⟨∅, empty_subset _, card_empty, fun u _ _ v hv => absurd hv (notMem_empty v)⟩
  | succ m ih =>
    intro S hS
    have hne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨M, hM⟩ : ∃ M, M = S.max' hne := ⟨_, rfl⟩
    have hMS : M ∈ S := by rw [hM]; exact max'_mem S hne
    obtain ⟨Y', hY'S, hY'c, hup⟩ := ih (S.erase M) (by rw [card_erase_of_mem hMS]; omega)
    have hMY' : M ∉ Y' := fun h => (mem_erase.mp (hY'S h)).1 rfl
    refine ⟨insert M Y', insert_subset hMS (hY'S.trans (erase_subset _ _)), ?_, ?_⟩
    · rw [card_insert_of_notMem hMY', hY'c]
    · intro u huS huY v hv
      have huM : u ≠ M := fun h => huY (h ▸ mem_insert_self _ _)
      have huY' : u ∉ Y' := fun h => huY (mem_insert_of_mem h)
      rcases mem_insert.mp hv with rfl | hv'
      · exact lt_of_le_of_ne (by rw [hM]; exact le_max' S u huS) huM
      · exact hup u (mem_erase.mpr ⟨huM, huS⟩) huY' v hv'

/-- The relative ordered class: no induced `P_s` in the complement, and an order of
    the complement in which the first vertex of every induced `P_(n+1)` is not an
    endpoint (`co(E_(n+1) ∩ Forb(P_s))`). -/
def TailCls (n s : ℕ) (W : Type) (G : SimpleGraph W) : Prop :=
  CoPathFree s G ∧ ∃ ord : LinearOrder W, @OrderedFirstEndpointFree W ord.toLT Gᶜ n

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 800000 in
/-- **The ordered-tail local oracle.** -/
theorem tail_oracle (n : ℕ) (ord : LinearOrder V)
    (hord : @OrderedFirstEndpointFree V ord.toLT Gᶜ n)
    {A e c k d E : ℕ} {η : ℝ} (hT : LowerTooth G (n + 1) A e c k d E η) :
    LocalOracle G (min η (1 / 4)) (A + 1) (c + k) (d + 1) (e + 1) (E + 1) := by
  intro x y hx hxy hyy S hsp hS
  have hyη : y ≤ η := hyy.trans (min_le_left _ _)
  have hy4 : y ≤ 1 / 4 := hyy.trans (min_le_right _ _)
  have hy0 : 0 < y := hx.trans_le hxy
  have hy1 : y ≤ 1 := hy4.trans (by norm_num)
  have hx1 : x ≤ 1 := hxy.trans hy1
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS
  have hS1 : 1 ≤ (S.card : ℝ) * x ^ (E + 1) := (div_le_iff₀ (by positivity)).mp hS
  -- x * |S| ≥ 1 / x^E
  have hxS : 1 / x ^ E ≤ x * S.card := by
    rw [div_le_iff₀ (pow_pos hx _)]
    have e1 : (S.card : ℝ) * x ^ (E + 1) = x * S.card * x ^ E := by ring
    linarith
  have hxS1 : 1 ≤ x * S.card := by
    have : (1 : ℝ) ≤ 1 / x ^ E := by
      rw [le_div_iff₀ (pow_pos hx _), one_mul]
      exact pow_le_one₀ hx.le hx1
    linarith
  have hyS : x * (S.card : ℝ) ≤ y * S.card := mul_le_mul_of_nonneg_right hxy hSpos.le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈y * (S.card : ℝ)⌉₊ := ⟨_, rfl⟩
  have hm1 : y * (S.card : ℝ) ≤ m := by rw [hm]; exact Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ 2 * (y * S.card) := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ y * S.card)
    rw [← hm] at this
    linarith
  have hmS : m ≤ S.card := by
    rw [hm]
    apply Nat.ceil_le.mpr
    have : y * (S.card : ℝ) ≤ 1 * S.card := mul_le_mul_of_nonneg_right hy1 hSpos.le
    linarith
  obtain ⟨Y, hYS, hYc, hup⟩ := exists_upper_subset ord m S hmS
  obtain ⟨U, hUdef⟩ : ∃ U : Finset V, U = S \ Y := ⟨_, rfl⟩
  have hUS : U ⊆ S := by rw [hUdef]; exact sdiff_subset
  have hout : ∀ u ∈ U, u ∉ Y := by
    intro u hu
    rw [hUdef] at hu
    exact (mem_sdiff.mp hu).2
  have hroot : ∀ u ∈ U, RootedPathFree G (n + 1) Y u := by
    rintro u hu ⟨p, i, hi, hp, hpi, htail⟩
    have he : i = 0 := Fin.ext hi
    subst he
    apply hord p hp
    intro j hj
    rw [hpi]
    exact hup u (hUS hu) (hout u hu) (p j) (htail j hj)
  have hYcard : (Y.card : ℝ) = m := by rw [hYc]
  have horder : 1 / x ^ E ≤ (Y.card : ℝ) := by rw [hYcard]; linarith
  rcases hT U Y x y hout hroot hx hxy hyη horder with ⟨X, hXY, hXsize, hfull⟩ |
      ⟨z, hz1, hz2, W, hWY, hsize, hres⟩ | ⟨K, hK1, hK2, γ, _, hγ⟩
  · -- clean core: a directed sparse pair
    right; left
    rw [hYcard] at hXsize
    have hXpos : (0 : ℝ) < X.card := by
      have : 0 < y ^ A * (m : ℝ) := by
        have : (0 : ℝ) < m := by linarith
        positivity
      linarith
    obtain ⟨v, hv⟩ : X.Nonempty := card_pos.mp (by exact_mod_cast hXpos)
    obtain ⟨Full, hFull⟩ : ∃ Full : Finset V, Full = U.filter (fun u => ∀ w ∈ X, G.Adj u w) :=
      ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ Z : Finset V, Z = U \ Full := ⟨_, rfl⟩
    have hFullU : Full ⊆ U := by rw [hFull]; exact filter_subset _ _
    have hFullc : (Full.card : ℝ) ≤ y ^ 3 * S.card := by
      have hsub : Full ⊆ EHP6.nbrs G v S := by
        intro u hu
        rw [hFull] at hu
        obtain ⟨huU, hadj⟩ := mem_filter.mp hu
        exact mem_filter.mpr ⟨hUS huU, G.adj_symm (hadj v hv)⟩
      have h1 : (Full.card : ℝ) ≤ (EHP6.nbrs G v S).card := by exact_mod_cast card_le_card hsub
      exact h1.trans (hsp v (hYS (hXY hv)))
    have hUc : (U.card : ℝ) = (S.card : ℝ) - m := by
      rw [hUdef, card_sdiff_of_subset hYS, Nat.cast_sub (card_le_card hYS), hYc]
    have hZc : (Z.card : ℝ) = (U.card : ℝ) - Full.card := by
      rw [hZdef, card_sdiff_of_subset hFullU, Nat.cast_sub (card_le_card hFullU)]
    refine ⟨X, hXY.trans hYS, Z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hZdef]; exact sdiff_subset.trans hUS
    · rw [disjoint_left]
      intro w hwX hwZ
      rw [hZdef] at hwZ
      exact hout w (mem_sdiff.mp hwZ).1 (hXY hwX)
    · refine le_trans ?_ hXsize
      have e1 : y ^ (A + 1) * (S.card : ℝ) = y ^ A * (y * S.card) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_left hm1 (by positivity)
    · rw [hZc, hUc]
      have h3 : y ^ 3 ≤ y := by
        calc y ^ 3 ≤ y ^ 1 := pow_le_pow_of_le_one hy0.le hy1 (by norm_num)
          _ = y := pow_one y
      have h4 : y ^ 3 * (S.card : ℝ) ≤ y * S.card := mul_le_mul_of_nonneg_right h3 hSpos.le
      nlinarith
    · intro u hu
      rw [hZdef] at hu
      obtain ⟨huU, huF⟩ := mem_sdiff.mp hu
      rcases hfull u huU with h | h
      · exact absurd (by rw [hFull]; exact mem_filter.mpr ⟨huU, h⟩) huF
      · have hXnn : (0 : ℝ) ≤ x * X.card := by positivity
        linarith
  · -- restricted at its actual scale
    right; right; right
    have hz0 : 0 < z := lt_of_lt_of_le (pow_pos hx _) hz1
    rw [hYcard] at hsize
    refine ⟨z, le_trans (pow_le_pow_of_le_one hx.le hx1 (by omega)) hz1, hz2, W,
      hWY.trans hYS, le_trans ?_ hsize, hres⟩
    have e1 : z ^ (e + 1) * (S.card : ℝ) = z ^ e * (z * S.card) := by ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : z * (S.card : ℝ) ≤ y * S.card := mul_le_mul_of_nonneg_right hz2 hSpos.le
    linarith
  · -- blockade
    right; right; left
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) hK1
    have hKy : 1 ≤ y * K := by
      have := (div_le_iff₀ hy0).mp hK1
      linarith
    have hw : (S.card : ℝ) / (K : ℝ) ^ (d + 1) ≤ (Y.card : ℝ) / (K : ℝ) ^ d := by
      rw [hYcard, div_le_div_iff₀ (pow_pos hK0 _) (pow_pos hK0 _)]
      have h1 : (S.card : ℝ) * 1 ≤ S.card * (y * K) := mul_le_mul_of_nonneg_left hKy hSpos.le
      have h2 : (S.card : ℝ) * (y * K) ≤ m * K := by
        have := mul_le_mul_of_nonneg_right hm1 hK0.le
        linarith [show y * (S.card : ℝ) * K = S.card * (y * K) by ring]
      have h3 : (S.card : ℝ) * (K : ℝ) ^ d ≤ (m : ℝ) * K * (K : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hK0.le _)
      have e1 : (m : ℝ) * (K : ℝ) ^ (d + 1) = m * K * (K : ℝ) ^ d := by ring
      linarith
    refine ⟨K, hK1, hK2.trans ?_, γ.mono hYS le_rfl hw, fun a b hab => ?_⟩
    · exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hx _)
        (pow_le_pow_of_le_one hx.le hx1 (by omega))
    · rcases lt_or_gt_of_ne hab with hlt | hlt
      · rcases hγ a b hlt with h | h
        · exact Or.inl h
        · exact Or.inr (EHP6.weaklySparse_of_sparseTo h)
      · rcases hγ b a hlt with h | h
        · exact Or.inl (fun p hp q hq => G.adj_symm (h q hq p hp))
        · exact Or.inr (EHP6.weaklySparse_symm (EHP6.weaklySparse_of_sparseTo h))

/-- The ambient property "no induced path on `s` vertices". -/
def PathFreeAmb (s : ℕ) (W : Type) (H : SimpleGraph W) : Prop :=
  ¬ ∃ p : Fin s → W, IsInducedPath H p

/-- **EH of the ordered class `E_(n+1) ∩ Forb(P_(h+1))`** from the contract
    `T_(n+1)` in complement-`P_(h+1)`-free hosts, Rödl's theorem for the complement
    of `P_(h+1)`, and an EH exponent of `P_h`. -/
theorem orderedClassEH_of_tooth (n h : ℕ) (hh : 1 ≤ h) (hR : RodlCo (h + 1))
    (hE : ∃ γ : ℝ, 0 < γ ∧ EHOn (EHP6.pathGraph' h) Finset.univ γ)
    {A e c k d E : ℕ} {η : ℝ} (hη : 0 < η) (hc : 1 ≤ c)
    (hT : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      CoPathFree (h + 1) H → LowerTooth H (n + 1) A e c k d E η) :
    ∃ κ : ℝ, 0 < κ ∧ OrderedClassEH (PathFreeAmb (h + 1)) n κ := by
  have hCls : ∀ (W : Type) (H : SimpleGraph W), TailCls n (h + 1) W H → CoPathFree (h + 1) H :=
    fun W H hc => hc.1
  have horacle : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], TailCls n (h + 1) W H →
      LocalOracle H (min η (1 / 4)) (A + 1) (c + k) (d + 1) (e + 1) (E + 1) := by
    intro W _ _ H _ hcls
    obtain ⟨hfree, ord, hord⟩ := hcls
    exact tail_oracle n ord hord (hT W H hfree)
  obtain ⟨d', hd', hnice⟩ := nice_of_oracle (h + 1) (by omega) (TailCls n (h + 1)) hCls hR
    (y₁ := min η (1 / 4)) (lt_min hη (by norm_num)) (show 1 ≤ c + k by omega) horacle
  obtain ⟨τ, hτ, hEH⟩ := classEH_of_nice h hh (TailCls n (h + 1)) hCls hR hE hd' hnice
  refine ⟨τ, hτ, ?_⟩
  intro W _ H ord hAmb hordH
  have hcls : TailCls n (h + 1) W Hᶜ := by
    refine ⟨?_, ord, ?_⟩
    · unfold CoPathFree
      rw [compl_compl]
      exact hAmb
    · rw [compl_compl]
      exact hordH
  obtain ⟨T, hT', hTc⟩ := hEH W H hcls
  refine ⟨T, ?_, hTc⟩
  rcases hT' with hc' | hs
  · exact Or.inl hc'
  · right
    intro u hu v hv
    by_cases huv : u = v
    · subst huv
      exact H.irrefl
    · exact hs u hu v hv huv

#print axioms exists_upper_subset
#print axioms tail_oracle
#print axioms orderedClassEH_of_tooth
end AllPathsLocal
