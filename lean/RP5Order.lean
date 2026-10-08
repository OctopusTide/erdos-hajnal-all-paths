import RP5Structure
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Max

/-! The increasing-path/independent-level dichotomy from Section III.3. -/

namespace AllPathsLocal

/-- Paths use strictly increasing original block indices, so no vertex can repeat. -/
inductive IncreasingQPath {m : ℕ} (Q : Fin m → Fin m → Prop) : ℕ → Fin m → Prop
  | single (i : Fin m) : IncreasingQPath Q 1 i
  | extend {n : ℕ} {i j : Fin m} : IncreasingQPath Q n i → i < j → Q i j →
      IncreasingQPath Q (n + 1) j

/-- The inductive path certificate yields a concrete strictly increasing vertex sequence
    with every consecutive Q-edge. This checks the meaning of the path used below. -/
theorem increasingQPath_sequence {m n : ℕ} {Q : Fin m → Fin m → Prop} {i : Fin m}
    (hp : IncreasingQPath Q n i) :
    0 < n ∧ ∃ f : Fin n → Fin m, StrictMono f ∧ (∀ a, f a ≤ i) ∧
      (∀ a, a.val + 1 = n → f a = i) ∧
      ∀ a b, a.val + 1 = b.val → Q (f a) (f b) := by
  induction hp with
  | single i =>
    refine ⟨by omega, fun _ => i, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      omega
    · intro _
      exact le_rfl
    · intro _ _
      rfl
    · intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      omega
  | @extend n i j hp hij hQ ih =>
    obtain ⟨hn, f, hf, hbound, hlast, hlinks⟩ := ih
    let g : Fin (n + 1) → Fin m := Fin.lastCases j f
    have hcast : ∀ a, g a.castSucc = f a := fun a => by simp [g]
    have hend : g (Fin.last n) = j := by simp [g]
    have hmono : StrictMono g := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro a
      rw [hcast]
      by_cases ha : a.val + 1 = n
      · have heq : a.succ = Fin.last n := by apply Fin.ext; simpa using ha
        rw [heq, hend]
        exact lt_of_le_of_lt (hbound a) hij
      · let b : Fin n := ⟨a.val + 1, by have := a.isLt; omega⟩
        have heq : a.succ = b.castSucc := by apply Fin.ext; rfl
        rw [heq, hcast]
        exact hf (show a < b by show a.val < a.val + 1; omega)
    refine ⟨by omega, g, hmono, ?_, ?_, ?_⟩
    · intro a
      refine Fin.lastCases ?_ (fun b => ?_) a
      · rw [hend]
      · rw [hcast]
        exact (hbound b).trans hij.le
    · intro a
      refine Fin.lastCases ?_ (fun b => ?_) a
      · intro _
        exact hend
      · intro hb
        have hlt := b.isLt
        simp only [Fin.val_castSucc] at hb
        omega
    · intro a b hab
      have ha : a.val < n := by have := b.isLt; omega
      let a' : Fin n := ⟨a.val, ha⟩
      have hae : a = a'.castSucc := by apply Fin.ext; rfl
      rw [hae, hcast]
      by_cases hb : b.val = n
      · have hbe : b = Fin.last n := Fin.ext hb
        have ha' : a'.val + 1 = n := by simpa [a'] using hab.trans hb
        rw [hbe, hend, hlast a' ha']
        exact hQ
      · let b' : Fin n := ⟨b.val, by have := b.isLt; omega⟩
        have hbe : b = b'.castSucc := by apply Fin.ext; rfl
        rw [hbe, hcast]
        exact hlinks a' b' hab

theorem height_coloring_of_no_increasing_path {m r : ℕ}
    (Q : Fin m → Fin m → Prop) (hr : 2 ≤ r)
    (hno : ∀ i, ¬ IncreasingQPath Q r i) :
    ∃ color : Fin m → Fin (r - 1), ∀ i j, i < j → Q i j → color i < color j := by
  classical
  let lengths : Fin m → Finset ℕ := fun i =>
    (Finset.range (r - 1)).filter (fun n => IncreasingQPath Q (n + 1) i)
  have hne : ∀ i, (lengths i).Nonempty := by
    intro i
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact IncreasingQPath.single i
  let height : Fin m → ℕ := fun i => (lengths i).max' (hne i)
  have hmem : ∀ i, height i ∈ lengths i := fun i => Finset.max'_mem _ _
  have hlt : ∀ i, height i < r - 1 := by
    intro i
    exact Finset.mem_range.mp (Finset.mem_filter.mp (hmem i)).1
  have hp : ∀ i, IncreasingQPath Q (height i + 1) i := by
    intro i
    exact (Finset.mem_filter.mp (hmem i)).2
  refine ⟨fun i => ⟨height i, hlt i⟩, ?_⟩
  intro i j hij hQ
  have hpath := IncreasingQPath.extend (hp i) hij hQ
  have hb : height i + 1 < r - 1 := by
    by_contra h
    have heq : (height i + 1) + 1 = r := by have := hlt i; omega
    rw [heq] at hpath
    exact hno j hpath
  have hins : height i + 1 ∈ lengths j :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hpath⟩
  have hle : height i + 1 ≤ height j := Finset.le_max' _ _ hins
  show height i < height j
  omega

/-- Either an r-vertex increasing Q-path exists, or one independent level has
    at least m/(r-1) original indices. The bound is real, so there is no rounding loss. -/
theorem increasing_path_or_large_independent_level {m r : ℕ}
    (Q : Fin m → Fin m → Prop) (hr : 2 ≤ r) :
    (∃ i, IncreasingQPath Q r i) ∨
      ∃ I : Finset (Fin m), (m : ℝ) / (r - 1) ≤ I.card ∧
        ∀ i ∈ I, ∀ j ∈ I, i < j → ¬ Q i j := by
  classical
  by_cases hpath : ∃ i, IncreasingQPath Q r i
  · exact Or.inl hpath
  right
  have hno : ∀ i, ¬ IncreasingQPath Q r i := by simpa using hpath
  obtain ⟨color, hcolor⟩ := height_coloring_of_no_increasing_path Q hr hno
  have hr0 : (0 : ℝ) < r - 1 := by
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbudget : (Finset.univ : Finset (Fin (r - 1))).card •
      ((m : ℝ) / (r - 1)) ≤ ((Finset.univ : Finset (Fin m)).card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcast]
    field_simp
    exact le_rfl
  have ht : (Finset.univ : Finset (Fin (r - 1))).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin (r - 1)))) (f := color)
    (b := (m : ℝ) / (r - 1)) (fun _ _ => Finset.mem_univ _) ht hbudget
  refine ⟨Finset.univ.filter (fun i => color i = c), hc, ?_⟩
  intro i hi j hj hij hQ
  have hci := (Finset.mem_filter.mp hi).2
  have hcj := (Finset.mem_filter.mp hj).2
  have hlt := hcolor i j hij hQ
  rw [hci, hcj] at hlt
  exact lt_irrefl _ hlt

#print axioms height_coloring_of_no_increasing_path
#print axioms increasingQPath_sequence
#print axioms increasing_path_or_large_independent_level

end AllPathsLocal
