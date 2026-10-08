import RP5ContainerPowerBound

namespace AllPathsLocal

theorem recorded_power_three_bound (q r : ℕ) (hq : 1 ≤ q)
    (herror : (r : ℝ)/(q : ℝ)*Real.log (128*(q : ℝ)) < 1) :
    (128*(q : ℝ))^r < (3 : ℝ)^q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hrlog : (r : ℝ)*Real.log (128*(q : ℝ)) < (q : ℝ) := by
    have hh : ((r : ℝ)*Real.log (128*(q : ℝ)))/(q : ℝ) < 1 := by
      convert herror using 1 <;> ring
    simpa only [one_mul] using (div_lt_iff₀ hq0).mp hh
  have hh : (128*(q : ℝ))^r < Real.exp (q : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (show 0 < (128*(q : ℝ))^r by positivity)).mp
    rwa [Real.log_pow]
  have heq : (Real.exp 1)^q = Real.exp (q : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  have h3 : Real.exp (q : ℝ) < (3 : ℝ)^q := by
    rw [← heq]
    exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by omega)
  exact hh.trans h3

/-- The paper's counting comparison is impossible at the proved logarithmic
    error. Integer powers suffice; no informal q-th-root step is needed. -/
theorem thin_scalar_power_inconsistent (q r : ℕ) (hq : 2 ≤ q) (hrq : r ≤ q)
    (herror : (r : ℝ)/(q : ℝ)*Real.log (128*(q : ℝ)) < 1)
    (hcompare : (128*(q : ℝ))^(q-r) ≤ 4*(12*(q : ℝ))^q) : False := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hp := recorded_power_three_bound q r (by omega) herror
  have hm := mul_le_mul_of_nonneg_right hcompare (show 0 ≤ (128*(q : ℝ))^r by positivity)
  have hlt := mul_lt_mul_of_pos_left hp (show 0 < 4*(12*(q : ℝ))^q by positivity)
  have heq : (128*(q : ℝ))^(q-r) * (128*(q : ℝ))^r = (128*(q : ℝ))^q := by
    rw [← pow_add, Nat.sub_add_cancel hrq]
  have heq3 : 4*(12*(q : ℝ))^q * (3 : ℝ)^q = 4*(36*(q : ℝ))^q := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    ring
  have hfour : (4 : ℝ) ≤ 3^q := by
    exact (show (4 : ℝ) ≤ 3^2 by norm_num).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hq)
  have hm4 := mul_le_mul_of_nonneg_right hfour (show 0 ≤ (36*(q : ℝ))^q by positivity)
  have heq108 : (3 : ℝ)^q * (36*(q : ℝ))^q = (108*(q : ℝ))^q := by
    rw [← mul_pow]
    congr 1
    ring
  have hlast : (108*(q : ℝ))^q ≤ (128*(q : ℝ))^q :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) q
  rw [heq] at hm
  rw [heq3] at hlt
  rw [heq108] at hm4
  exact (lt_irrefl _ ((hm.trans_lt hlt).trans_le (hm4.trans hlast)))

#print axioms recorded_power_three_bound
#print axioms thin_scalar_power_inconsistent
end AllPathsLocal
