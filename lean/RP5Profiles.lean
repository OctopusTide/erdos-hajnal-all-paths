import RP5Structure
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Fin.Basic

/-! Prefix profiles in III.3 are formed against original blocks, before choosing any cells. -/

namespace AllPathsLocal

theorem antitone_predicate_prefix (n : ℕ) :
    ∀ P : Fin n → Prop, Antitone P →
      ∃ c : Fin (n + 1), ∀ i, P i ↔ i.val < c.val := by
  induction n with
  | zero =>
    intro P _
    exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro P hP
    by_cases hp0 : P 0
    · have htail : Antitone (fun i : Fin n => P i.succ) := by
        intro i j hij
        exact hP (Fin.succ_le_succ_iff.mpr hij)
      obtain ⟨c, hc⟩ := ih (fun i => P i.succ) htail
      refine ⟨c.succ, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hp0]
      · simpa using hc j
    · refine ⟨0, ?_⟩
      intro i
      have hfalse : ¬ P i := fun hi => hp0 (hP (Fin.zero_le i) hi)
      simp [hfalse]

/-- Local no-reversal along consecutive path edges gives one initial interval of complete types. -/
theorem no_reversal_prefix {n : ℕ} (P : Fin (n + 1) → Prop)
    (hstep : ∀ i : Fin n, P i.succ → P i.castSucc) :
    ∃ c : Fin (n + 2), ∀ i, P i ↔ i.val < c.val := by
  exact antitone_predicate_prefix (n + 1) P (Fin.antitone_iff_succ_le.mpr hstep)

/-- Choose one profile cell of at least |D|/(n+1), with all types still measured on
    the original n earlier blocks. This requires no sequential intersections. -/
theorem large_uniform_prefix_cell {V : Type} [DecidableEq V]
    (D : Finset V) (n : ℕ) (P : V → Fin n → Prop)
    (hP : ∀ v ∈ D, Antitone (P v)) :
    ∃ c : Fin (n + 1), ∃ E ⊆ D, (D.card : ℝ) / (n + 1) ≤ E.card ∧
      ∀ v ∈ E, ∀ i, P v i ↔ i.val < c.val := by
  classical
  let c : V → Fin (n + 1) := fun v =>
    if hv : v ∈ D then Classical.choose (antitone_predicate_prefix n (P v) (hP v hv)) else 0
  have hc : ∀ v ∈ D, ∀ i, P v i ↔ i.val < (c v).val := by
    intro v hv
    simpa only [c, dite_eq_left hv] using
      Classical.choose_spec (antitone_predicate_prefix n (P v) (hP v hv))
  have hbudget : (Finset.univ : Finset (Fin (n + 1))).card •
      ((D.card : ℝ) / (n + 1)) ≤ (D.card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : (0 : ℝ) < n + 1 := by positivity
    field_simp
    simp [Nat.cast_add, mul_comm]
  obtain ⟨cut, _, hsize⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := D) (t := (Finset.univ : Finset (Fin (n + 1)))) (f := c)
    (b := (D.card : ℝ) / (n + 1)) (fun _ _ => Finset.mem_univ _)
    Finset.univ_nonempty hbudget
  refine ⟨cut, D.filter (fun v => c v = cut), Finset.filter_subset _ _, hsize, ?_⟩
  intro v hv i
  obtain ⟨hvD, heq⟩ := Finset.mem_filter.mp hv
  simpa only [heq] using hc v hvD i

/-- Connect the actual RP5 forcing obstruction to the large-cell choice along a Q-path.
    All classifications refer to the original C_i, so cell choices are independent. -/
theorem rp5_path_profile_cell {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (Y D : Finset V) (C : Fin (n + 1) → Finset V) (β : ℝ)
    (hD : D ⊆ Y) (hC : ∀ i, C i ⊆ Y)
    (hDC : ∀ i, Disjoint D (C i))
    (hdisj : ∀ i : Fin n, Disjoint (C i.castSucc) (C i.succ))
    (hconn : ∀ i : Fin n, EHP6.AntiConnected G (C i.succ)) (hβ : 2 * β ≤ 1)
    (hedgeTypes : ∀ i : Fin n, ∀ v ∈ C i.succ,
      (∀ b ∈ C i.castSucc, G.Adj v b) ∨
      ((EHP6.nbrs G v (C i.castSucc)).card : ℝ) < β * (C i.castSucc).card)
    (hedgeMixed : ∀ i : Fin n,
      (∃ w ∈ C i.succ, ∀ b ∈ C i.castSucc, G.Adj w b) ∧
      (∃ v ∈ C i.succ, ¬ ∀ b ∈ C i.castSucc, G.Adj v b))
    (hsep : ∀ i : Fin n, ∃ r, r ∉ Y ∧ RootedP5Free G Y r ∧
      (∀ b ∈ C i.castSucc, G.Adj r b) ∧ (∀ v ∈ C i.succ, G.Adj r v) ∧
      ∀ z ∈ D, ¬ G.Adj r z)
    (hlaterTypes : ∀ z ∈ D, ∀ i,
      (∀ b ∈ C i, G.Adj z b) ∨ ((EHP6.nbrs G z (C i)).card : ℝ) < β * (C i).card) :
    ∃ c : Fin (n + 2), ∃ E ⊆ D, (D.card : ℝ) / (n + 2) ≤ E.card ∧
      ∀ z ∈ E, ∀ i, (∀ b ∈ C i, G.Adj z b) ↔ i.val < c.val := by
  let P : V → Fin (n + 1) → Prop := fun z i => ∀ b ∈ C i, G.Adj z b
  have hmon : ∀ z ∈ D, Antitone (P z) := by
    intro z hz
    apply Fin.antitone_iff_succ_le.mpr
    intro i hcomplete
    rcases hlaterTypes z hz i.castSucc with hfull | hsparse
    · exact hfull
    obtain ⟨r, hrY, hrfree, hrI, hrJ, hrz⟩ := hsep i
    have hzI : z ∉ C i.castSucc := fun h => Finset.disjoint_left.mp (hDC i.castSucc) hz h
    exact False.elim (rp5_forcing_no_reversal G (hC i.castSucc) (hC i.succ)
      (hdisj i) hrY (hD hz) hzI hrfree hrI hrJ (hrz z hz) hcomplete
      (hconn i) hβ hsparse (hedgeTypes i) (hedgeMixed i).1 (hedgeMixed i).2)
  obtain ⟨c, E, hED, hsize, huniform⟩ := large_uniform_prefix_cell D (n + 1) P hmon
  refine ⟨c, E, hED, ?_, huniform⟩
  have heq : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [heq] at hsize
  exact hsize

#print axioms antitone_predicate_prefix
#print axioms no_reversal_prefix
#print axioms large_uniform_prefix_cell
#print axioms rp5_path_profile_cell

end AllPathsLocal
