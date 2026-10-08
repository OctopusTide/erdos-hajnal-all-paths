import RP5ContainerCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace AllPathsLocal

theorem container_power_exp_bound (epsilon : ℝ) (he : epsilon ≤ 1) (r : ℕ) :
    (1-epsilon)^r ≤ Real.exp (-epsilon * r) := by
  have hb : 1-epsilon ≤ Real.exp (-epsilon) := by
    linarith [Real.add_one_le_exp (-epsilon)]
  have ha : 0 ≤ 1-epsilon := by linarith
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        _ = (1-epsilon)^r * (1-epsilon) := pow_succ _ _
        _ ≤ Real.exp (-epsilon * r) * Real.exp (-epsilon) :=
          mul_le_mul ih hb ha (Real.exp_nonneg _)
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- The logarithmic recording budget of the paper, with all real quantities
    and the integer r visible. It feeds the actual container-count theorem. -/
theorem container_log_budget (epsilon delta M u : ℝ) (r : ℕ)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) (hd : 0 < delta) (hM : 0 ≤ M)
    (hr : Real.log (1/delta) / epsilon ≤ r) (hu : delta*M ≤ u) :
    (1-epsilon)^r * M ≤ u := by
  have hreq : Real.log (1/delta) ≤ epsilon * (r : ℝ) := by
    have h := (div_le_iff₀ he).mp hr
    simpa only [mul_comm] using h
  have hlog : -epsilon * (r : ℝ) ≤ Real.log delta := by
    rw [one_div, Real.log_inv] at hreq
    linarith
  have heq := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hd] at heq
  exact (mul_le_mul_of_nonneg_right
    ((container_power_exp_bound epsilon he1 r).trans heq) hM).trans hu

theorem container_ceil_log_budget (epsilon delta M u : ℝ)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) (hd : 0 < delta) (hM : 0 ≤ M)
    (hu : delta*M ≤ u) :
    (1-epsilon)^(Nat.ceil (Real.log (1/delta) / epsilon)) * M ≤ u := by
  exact container_log_budget epsilon delta M u _ he he1 hd hM (Nat.le_ceil _) hu

#print axioms container_power_exp_bound
#print axioms container_log_budget
#print axioms container_ceil_log_budget
end AllPathsLocal
