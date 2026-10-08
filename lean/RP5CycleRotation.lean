import RP5CycleEndpoints
import Mathlib.Algebra.Group.Fin.Basic

namespace AllPathsLocal

theorem cyclic_consecutive_iff_add {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i j : Fin n) :
    CyclicConsecutive n i j ↔ i + 1 = j ∨ j + 1 = i := by
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc (k : Fin n) : (k + 1).val =
      if n ≤ k.val + 1 then k.val + 1 - n else k.val + 1 := by
    rw [Fin.val_add_eq_ite, hone]
  simp only [CyclicConsecutive, Fin.ext_iff, hsucc]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> omega

theorem cyclic_consecutive_rotate {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i j k : Fin n) :
    CyclicConsecutive n (i + k) (j + k) ↔ CyclicConsecutive n i j := by
  rw [cyclic_consecutive_iff_add hn, cyclic_consecutive_iff_add hn]
  have hi : (i + k) + 1 = (i + 1) + k := by ac_rfl
  have hj : (j + k) + 1 = (j + 1) + k := by ac_rfl
  rw [hi, hj]
  constructor
  · rintro (h | h)
    · exact Or.inl (add_right_cancel h)
    · exact Or.inr (add_right_cancel h)
  · rintro (h | h)
    · exact Or.inl (congrArg (fun z : Fin n => z + k) h)
    · exact Or.inr (congrArg (fun z : Fin n => z + k) h)

theorem induced_cycle_rotate {V : Type} (G : SimpleGraph V) {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (p : Fin n → V) (hp : IsInducedCycle G p) (k : Fin n) :
    IsInducedCycle G (fun i => p (i + k)) := by
  constructor
  · intro i j h
    exact add_right_cancel (hp.1 h)
  · intro i j
    rw [hp.2, cyclic_consecutive_rotate hn]

#print axioms cyclic_consecutive_iff_add
#print axioms cyclic_consecutive_rotate
#print axioms induced_cycle_rotate

end AllPathsLocal
