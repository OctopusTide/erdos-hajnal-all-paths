import AllPathsRecurrence
import AllPathsTail

/-!
# The Erdős–Hajnal property of every path, from its displayed inputs

Main paper, Part II and the final induction. For a fixed target `s = h + 1`:

* `tooth_all`: by induction on the rooted order, the contracts `T_(n+5)` and
  `T_(n+4)` hold with common constants in every host whose complement has no
  induced `P_s`. The base is the verified RP5 Tooth (a root excluding rooted `P_4`
  excludes rooted `P_5`). The step applies the ordered-tail transfer
  `orderedClassEH_of_tooth` to `T_(q-1)` and then the recurrence `rpq_tooth`.
  At `q = 6` the offending-pair pass therefore uses the RP5 contract on RP4 roots,
  not the specialised RP4 Tooth of the paper's RP6 appendix; this is a simplification
  of the proof route, not a change of any statement.
* `eh_path_step`: `T_(s-2)` gives the final comb oracle, generalized niceness, and
  EH(`P_s`).
* `eh_all_paths`: induction on the path length.

Displayed hypotheses: Rödl's theorem for the complement of each path `P_s`, `s ≥ 7`
(`RodlCo s`), the comb lemma `EHP6.NssComb`, and EH(`P_6`) (`EHforPath 6`).
-/

namespace AllPathsLocal

open EHP6 Finset Classical

theorem pathFreeAmb_induce {V : Type} (s : ℕ) {G : SimpleGraph V} (h : CoPathFree s G)
    (S : Finset V) : PathFreeAmb s ↥(S : Set V) (Gᶜ.induce (S : Set V)) := by
  rintro ⟨p, hp⟩
  exact h ⟨fun i => (p i).val, fun i j hij => hp.1 (Subtype.ext hij), fun i j => hp.2 i j⟩

/-- EH(`P_(m+3)`) from the contract `T_(m+1)` in complement-`P_(m+3)`-free hosts. -/
theorem eh_path_step (hcomb : NssComb) (m : ℕ) (hR : RodlCo (m + 3))
    (hE : EHforPath (m + 2)) {A e c k d E : ℕ} {η : ℝ} (hη : 0 < η)
    (hT : ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      CoPathFree (m + 3) G → LowerTooth G (m + 1) A e c k d E η) :
    EHforPath (m + 3) := by
  have hCls : ∀ (W : Type) (H : SimpleGraph W), CoPathFree (m + 3) H → CoPathFree (m + 3) H :=
    fun _ _ h => h
  obtain ⟨d', hd', hnice⟩ := nice_of_oracle (m + 3) (by omega)
    (fun W G => CoPathFree (m + 3) G) hCls hR
    (y₁ := min η (1 / 2 ^ 64)) (lt_min hη (by norm_num)) (c := 2 * c + 2 * k + 2) (by omega)
    (fun W _ _ H _ hcls => comb_oracle_gen hcomb m hcls (hT W H hcls))
  obtain ⟨τ, hτ, hEH⟩ := classEH_of_nice (m + 2) (by omega)
    (fun W G => CoPathFree (m + 3) G) hCls hR (ehOn_of_EHforPath (m + 2) hE) hd' hnice
  refine ⟨τ, hτ, fun V _ _ G _ hfree => ?_⟩
  exact hEH V G (coPathFree_of_free (m + 3) Gᶜ (compl_free_path (m + 3) hfree))

/-- **All rooted Tooth contracts for a fixed target path.** -/
theorem tooth_all (h : ℕ) (hh : 1 ≤ h) (hR : RodlCo (h + 1))
    (hE : ∃ γ : ℝ, 0 < γ ∧ EHOn (pathGraph' h) Finset.univ γ) :
    ∀ n : ℕ, ∃ (A e c k d E : ℕ) (η : ℝ), 0 < η ∧ η ≤ 1 / 2 ^ 16 ∧ 1 ≤ c ∧ 1 ≤ k ∧ 1 ≤ E ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
        CoPathFree (h + 1) G →
          LowerTooth G (n + 5) A e c k d E η ∧ LowerTooth G (n + 4) A e c k d E η := by
  intro n
  induction n with
  | zero =>
    refine ⟨26, 18, 1, 140, 64, 600, 1 / 2 ^ 16, by norm_num, le_rfl, le_rfl, by norm_num,
      by norm_num, ?_⟩
    intro W _ _ G _ _
    exact ⟨lowerTooth_five G, lowerTooth_pred (by norm_num) (lowerTooth_five G)⟩
  | succ n ih =>
    obtain ⟨A, e, c, k, d, E, η, hη0, hη16, hc, hk, hE1, hT⟩ := ih
    obtain ⟨κ, hκ, hEHcls⟩ := orderedClassEH_of_tooth (n + 4) h hh hR hE hη0 hc
      (fun W _ _ G _ hfree => (hT W G hfree).1)
    obtain ⟨H, hHdef⟩ : ∃ H : ℕ, H = max 2 ⌈1 / κ⌉₊ := ⟨_, rfl⟩
    have hH2 : 2 ≤ H := by rw [hHdef]; exact le_max_left _ _
    have hHκ : 1 ≤ (H : ℝ) * κ := by
      have h1 : 1 / κ ≤ (H : ℝ) := by
        have : (⌈1 / κ⌉₊ : ℝ) ≤ H := by
          rw [hHdef]; exact_mod_cast le_max_right 2 ⌈1 / κ⌉₊
        exact (Nat.le_ceil _).trans this
      have := mul_le_mul_of_nonneg_right h1 hκ.le
      rwa [one_div, inv_mul_cancel₀ hκ.ne'] at this
    have hηpos : 0 < min η ((2 : ℝ) ^ (-((H : ℝ) + 10))) :=
      lt_min hη0 (Real.rpow_pos_of_pos (by norm_num) _)
    have hη1 : η ≤ 1 := hη16.trans (by norm_num)
    refine ⟨6 * (4 * H + 5) + 2 + A, e + 2 * A + 7 + 8 * H + (4 * H + 5) + 10 + e,
      c * (4 * A + 11) * (6 * (4 * H + 5) + 3) + c,
      k * (4 * A + 11) * (6 * (4 * H + 5) + 3) + k, 9 * A + d + 21 + d,
      (6 * (4 * H + 5) + 3) * (E * (4 * A + 11)) + 36 * (4 * H + 5) + 12 + E,
      min η ((2 : ℝ) ^ (-((H : ℝ) + 10))), hηpos, (min_le_left _ _).trans hη16,
      by omega, by omega, by omega, ?_⟩
    intro W _ _ G _ hfree
    obtain ⟨hT5, hT4⟩ := hT W G hfree
    have hnew := rpq_tooth (n + 3) hE1 hk hc hη16 hT5 hT4 (PathFreeAmb (h + 1))
      (pathFreeAmb_induce (h + 1) hfree) κ H hκ.le hH2 hHκ hEHcls
    constructor
    · exact lowerTooth_mono hnew le_rfl ((min_le_left _ _).trans hη1) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact lowerTooth_mono hT5 (min_le_left _ _) hη1 (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)

/-- **The fixed-target implication**: for `h ≥ 6`, EH(`P_h`), Rödl's theorem for the
    complement of `P_(h+1)` and the comb lemma give EH(`P_(h+1)`). -/
theorem eh_path_succ (hcomb : NssComb) (h : ℕ) (hh : 6 ≤ h) (hR : RodlCo (h + 1))
    (hE : EHforPath h) : EHforPath (h + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 6 := ⟨h - 6, by omega⟩
  obtain ⟨A, e, c, k, d, E, η, hη0, -, -, -, -, hT⟩ :=
    tooth_all (m + 6) (by omega) hR (ehOn_of_EHforPath (m + 6) hE) m
  exact eh_path_step hcomb (m + 4) hR hE hη0 (fun W _ _ G _ hfree => (hT W G hfree).1)

/-- A graph with no induced `P_s` has no induced `P_t` for `t ≥ s`. -/
theorem free_path_mono {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {s t : ℕ} (hst : s ≤ t) (hfree : Free G (pathGraph' s)) :
    Free G (pathGraph' t) := by
  rintro ⟨f, hinj, -, hadj⟩
  apply hfree
  refine ⟨fun i => f (Fin.castLE hst i), fun i j hij => Fin.castLE_injective hst (hinj hij),
    fun i => mem_univ _, fun i j => ?_⟩
  rw [hadj]
  simp only [pathGraph', SimpleGraph.fromRel_adj, Fin.val_castLE, ne_eq]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun e => hne (by rw [e]), h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun e => hne (Fin.castLE_injective hst e), h⟩

/-- **The Erdős–Hajnal property of every path**, from Rödl's theorem for the
    complement of each path on at least seven vertices, the comb lemma, and
    EH(`P_6`). The exponent depends on the path. -/
theorem eh_all_paths (hRodl : ∀ s : ℕ, 7 ≤ s → RodlCo s) (hcomb : NssComb)
    (hE6 : EHforPath 6) : ∀ s : ℕ, EHforPath s := by
  have hge : ∀ j : ℕ, EHforPath (j + 6) := by
    intro j
    induction j with
    | zero => exact hE6
    | succ j ih => exact eh_path_succ hcomb (j + 6) (by omega) (hRodl (j + 7) (by omega)) ih
  intro s
  by_cases hs : 6 ≤ s
  · obtain ⟨j, rfl⟩ : ∃ j, s = j + 6 := ⟨s - 6, by omega⟩
    exact hge j
  · obtain ⟨τ, hτ, h6⟩ := hE6
    exact ⟨τ, hτ, fun V _ _ G _ hfree => h6 V G (free_path_mono G (by omega) hfree)⟩

/-- EH(`P_6`) of the base project in the `EHforPath` form. -/
theorem ehforPath_six_of_EHforP6 (h : EHforP6) : EHforPath 6 := h

/-- **All paths, with EH(`P_6`) supplied by the base project.** Besides the displayed
    Rödl hypothesis this uses the three literature axioms of the P6 project
    (`rodl_coP6`, `eh_P5`, `nss_comb`). -/
theorem eh_all_paths_of_rodl (hRodl : ∀ s : ℕ, 7 ≤ s → RodlCo s) : ∀ s : ℕ, EHforPath s :=
  eh_all_paths hRodl nss_comb (ehforPath_six_of_EHforP6 erdos_hajnal_P6)

#print axioms eh_path_step
#print axioms tooth_all
#print axioms eh_path_succ
#print axioms eh_all_paths
#print axioms eh_all_paths_of_rodl
end AllPathsLocal
