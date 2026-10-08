import RP5ContainerLogBudget
import Mathlib.Data.Nat.Factorial.BigOperators

namespace AllPathsLocal
open scoped BigOperators

/-- Exact without-replacement ratio bound. The subtraction is natural and
    justified separately for every descending-product factor. -/
theorem choose_cross_power_lower (M k q : ℕ) (hqk : q ≤ k) (hkM : k ≤ M) :
    (k.choose q : ℝ) * (M : ℝ)^q ≤ (M.choose q : ℝ) * (k : ℝ)^q := by
  have hp : (∏ i ∈ Finset.range q, ((k-i : ℕ) : ℝ) * (M : ℝ)) ≤
      ∏ i ∈ Finset.range q, ((M-i : ℕ) : ℝ) * (k : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i hi
      have hik : i ≤ k := by have hh := Finset.mem_range.mp hi; omega
      have hiM : i ≤ M := hik.trans hkM
      rw [Nat.cast_sub hik, Nat.cast_sub hiM]
      have hMk : (k : ℝ) ≤ M := by exact_mod_cast hkM
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
      nlinarith
  have hd (n : ℕ) : (∏ i ∈ Finset.range q, ((n-i : ℕ) : ℝ)) =
      (q.factorial : ℝ) * (n.choose q : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_prod_range n q).symm.trans
      (Nat.descFactorial_eq_factorial_mul_choose n q)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hp
  rw [hd k, hd M] at hp
  have hf : (0 : ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos q
  nlinarith

theorem uniform_subset_choose_ratio_lower (M k q : ℕ) (hqk : q ≤ k) (hkM : k ≤ M) :
    (M : ℝ)^q * ((M-q).choose (k-q) : ℝ) ≤
      (k : ℝ)^q * (M.choose k : ℝ) := by
  have h := choose_cross_power_lower M k q hqk hkM
  have hi : (M.choose k : ℝ) * (k.choose q : ℝ) =
      (M.choose q : ℝ) * ((M-q).choose (k-q) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := M) hqk
  have hm := mul_le_mul_of_nonneg_right h
    (show (0 : ℝ) ≤ ((M-q).choose (k-q) : ℝ) by positivity)
  have hc : (0 : ℝ) < k.choose q := by exact_mod_cast Nat.choose_pos hqk
  have hiPow := congrArg (fun z : ℝ => z * (k : ℝ)^q) hi
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hm, hiPow]

/-- Natural-count comparison converted to the paper's quantitative homogeneous
    count, with no division or floating-point approximation. -/
theorem homogeneous_count_power_lower (M k q H : ℕ) (hqk : q ≤ k) (hkM : k ≤ M)
    (hcount : M.choose k ≤ 2 * H * (M-q).choose (k-q)) :
    (M : ℝ)^q ≤ 2 * (H : ℝ) * (k : ℝ)^q := by
  have hc : (0 : ℝ) < (M-q).choose (k-q) := by
    exact_mod_cast Nat.choose_pos (show k-q ≤ M-q by omega)
  have h := uniform_subset_choose_ratio_lower M k q hqk hkM
  have hcountR : (M.choose k : ℝ) ≤ 2 * (H : ℝ) * ((M-q).choose (k-q) : ℝ) := by
    exact_mod_cast hcount
  have hm := mul_le_mul_of_nonneg_left hcountR (show 0 ≤ (k : ℝ)^q by positivity)
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith

#print axioms choose_cross_power_lower
#print axioms uniform_subset_choose_ratio_lower
#print axioms homogeneous_count_power_lower
end AllPathsLocal
