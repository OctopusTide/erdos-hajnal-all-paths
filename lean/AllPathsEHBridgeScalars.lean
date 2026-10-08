import AllPathsEHThinLayer

namespace AllPathsLocal

/-- Bernoulli: `1 + h ≤ 2^h` for real `h ≥ 1`. -/
theorem one_add_le_two_rpow (h : ℝ) (hh : 1 ≤ h) : 1 + h ≤ (2 : ℝ)^h := by
  have hb := one_add_mul_self_le_rpow_one_add (s := 1) (by norm_num) hh
  norm_num at hb
  linarith

/-- The logarithmic error of the EH-transversal bridge, with the real
    parameter `h` kept symbolic. `w` stands for `2^h`; the smallness
    hypothesis is `epsilon ≤ 2^(-4(h+10))` in polynomial form. -/
theorem bridge_log_error (ε h w : ℝ) (he : 0 < ε) (hh : 2 ≤ h) (hw : 1 + h ≤ w)
    (hsmall : ε * w^4 * 2^40 ≤ 1) :
    4*h^2*ε*(Real.log (1/ε))^2 + 2*h*ε^2*Real.log (1/ε) < 1 := by
  have hw0 : 0 < w := by linarith
  have hhw : h ≤ w := by linarith
  have hw3 : 3 ≤ w := by linarith
  set X : ℝ := 1/ε with hX
  have hX0 : 0 < X := by positivity
  have hXbig : w^4*2^40 ≤ X := by
    rw [hX, le_div_iff₀ he]
    linarith
  have hw4 : (81 : ℝ) ≤ w^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hw3 4]
  have hX1 : 1 ≤ X := by nlinarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  set s : ℝ := Real.sqrt (Real.sqrt X) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hsX
  have hs2 : s^2 = Real.sqrt X := Real.sq_sqrt hsX.le
  have hs4 : (Real.sqrt X)^2 = X := Real.sq_sqrt hX0.le
  have hXs : X = s^4 := by
    rw [show s^4 = (s^2)^2 by ring, hs2, hs4]
  have hlog : Real.log X = 4*Real.log s := by
    rw [hXs, Real.log_pow]
    norm_num
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hL0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hL : Real.log X ≤ 4*s := by linarith
  have hL2 : (Real.log X)^2 ≤ 16*Real.sqrt X := by
    have hp := pow_le_pow_left₀ hL0 hL 2
    rw [← hs2]
    nlinarith
  have hsqrt : w^2*2^20 ≤ Real.sqrt X := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hLX : Real.log X ≤ X := (Real.log_le_sub_one_of_pos hX0).trans (by linarith)
  have hh2 : h^2 ≤ w^2 := pow_le_pow_left₀ (by linarith) hhw 2
  have hfirst : 4*h^2*(Real.log X)^2 ≤ X/2 := by
    have h1 : 128*h^2 ≤ Real.sqrt X := by nlinarith
    have h2 : 4*h^2*(Real.log X)^2 ≤ 64*h^2*Real.sqrt X := by
      have := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 4*h^2 by positivity)
      linarith
    have h3 : 64*h^2*Real.sqrt X ≤ Real.sqrt X * Real.sqrt X / 2 := by
      have := mul_le_mul_of_nonneg_right h1 hsX.le
      linarith
    have h4 : Real.sqrt X * Real.sqrt X = X := by rw [← pow_two, hs4]
    linarith
  have hsecond : 2*h*Real.log X ≤ X^2/4 := by
    have h1 : 8*h ≤ X := by
      have hw14 : w ≤ w^4 := le_self_pow₀ (by linarith) (by norm_num)
      have hbig : w^4*8 ≤ w^4*2^40 := mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      linarith
    have h2 : 2*h*Real.log X ≤ 2*h*X :=
      mul_le_mul_of_nonneg_left hLX (by linarith)
    nlinarith
  have heq : ε = 1/X := by
    rw [hX]
    field_simp
  have hεX : ε*X = 1 := by
    rw [hX]
    field_simp
  have ht1 : 4*h^2*ε*(Real.log X)^2 ≤ 1/2 := by
    have := mul_le_mul_of_nonneg_left hfirst he.le
    nlinarith
  have ht2 : 2*h*ε^2*Real.log X ≤ 1/4 := by
    have := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ ε^2 by positivity)
    have hx2 : ε^2*X^2 = 1 := by
      rw [← mul_pow, hεX]
      norm_num
    nlinarith
  linarith

set_option maxHeartbeats 1600000 in
/-- All rounding, logarithmic and exponent conditions of the EH-transversal
    bridge at the paper's actual parameters
    `q = ceil(epsilon^-2)`, `t = ceil(q^h)`, `delta = q/(512 t)`,
    `r = ceil(epsilon^-1 ln(1/delta))`, for every real `h ≥ 2`. -/
theorem eh_bridge_parameters (ε h : ℝ) (he : 0 < ε) (hh : 2 ≤ h)
    (heSmall : ε ≤ (2 : ℝ)^(-(4*(h+10)))) (q t r : ℕ)
    (hqdef : q = Nat.ceil (1/ε^2)) (htdef : t = Nat.ceil ((q : ℝ)^h))
    (hrdef : r = Nat.ceil (Real.log (1/((q : ℝ)/(512*(t : ℝ))))/ε)) :
    8 ≤ q ∧ q ≤ t ∧ (q : ℝ)^h ≤ (t : ℝ) ∧ 32*(t : ℝ)*ε^(4*h+4) ≤ 1 ∧
      ε^(2*h+2) ≤ (q : ℝ)/(512*(t : ℝ)) ∧
      (r : ℝ)/(q : ℝ)*Real.log (256*(t : ℝ)/(q : ℝ)) < 1 ∧ r < q := by
  have hh0 : 0 ≤ h := by linarith
  have hh1 : 1 ≤ h := by linarith
  set w : ℝ := (2 : ℝ)^h with hwdef
  set p : ℝ := ε^h with hpdef
  have hw : 1 + h ≤ w := one_add_le_two_rpow h hh1
  have hw0 : 0 < w := by linarith
  have hw3 : 3 ≤ w := by linarith
  have hpow2 : (2 : ℝ)^(4*(h+10)) = w^4*2^40 := by
    rw [show 4*(h+10) = h*((4 : ℕ) : ℝ) + ((40 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast,
      Real.rpow_natCast]
  have hsmall : ε*w^4*2^40 ≤ 1 := by
    rw [Real.rpow_neg (by norm_num), hpow2] at heSmall
    have hpos : (0 : ℝ) < w^4*2^40 := by positivity
    have := mul_le_mul_of_nonneg_right heSmall hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  have hw4 : (81 : ℝ) ≤ w^4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hw3 4]
  have hεw : ε*w^4 ≤ 1/2^40 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hεsmall : ε ≤ 1/2^40 := by
    have h1 : ε*1 ≤ ε*w^4 := mul_le_mul_of_nonneg_left (by linarith) he.le
    linarith
  have he1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hp0 : 0 < p := Real.rpow_pos_of_pos he h
  have hp1 : p ≤ 1 := Real.rpow_le_one he.le he1 hh0
  have hpow4 : ε^(4*h+4) = p^4*ε^4 := by
    rw [show 4*h+4 = h*((4 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add he, Real.rpow_mul he.le, Real.rpow_natCast, Real.rpow_natCast]
  have hpow22 : ε^(2*h+2) = p^2*ε^2 := by
    rw [show 2*h+2 = h*((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add he, Real.rpow_mul he.le, Real.rpow_natCast, Real.rpow_natCast]
  have he2pos : 0 < ε^2 := by positivity
  have hbig : (4 : ℝ) ≤ 1/ε^2 := by
    rw [le_div_iff₀ he2pos]
    nlinarith
  have hqLower : 1/ε^2 ≤ (q : ℝ) := by
    rw [hqdef]
    exact Nat.le_ceil _
  have hqUpper : (q : ℝ) ≤ 2/ε^2 := by
    rw [hqdef]
    have hc := Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 4).trans hbig)
    convert hc using 1
    ring
  have hbig8 : (8 : ℝ) ≤ 1/ε^2 := by
    rw [le_div_iff₀ he2pos]
    nlinarith
  have hq8R : (8 : ℝ) ≤ q := hbig8.trans hqLower
  have hq8 : 8 ≤ q := by exact_mod_cast hq8R
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hqh_lower : (q : ℝ) ≤ (q : ℝ)^h := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 hh1
    simpa using this
  have hsq : (ε^2)^h = p^2 := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul he.le, mul_comm, Real.rpow_mul he.le,
      Real.rpow_natCast]
  have hqh_upper : (q : ℝ)^h ≤ w/p^2 := by
    have h1 := Real.rpow_le_rpow hq0.le hqUpper hh0
    rw [Real.div_rpow (by norm_num) he2pos.le, hsq] at h1
    exact h1
  have htLower : (q : ℝ)^h ≤ (t : ℝ) := by
    rw [htdef]
    exact Nat.le_ceil _
  have htUpper : (t : ℝ) ≤ 2*(q : ℝ)^h := by
    rw [htdef]
    apply Nat.ceil_le_two_mul
    linarith
  have hqt : q ≤ t := by exact_mod_cast hqh_lower.trans htLower
  have ht0 : (0 : ℝ) < t := by linarith
  have hp2 : 0 < p^2 := by positivity
  have htw : (t : ℝ)*p^2 ≤ 2*w := by
    have h1 := htUpper.trans (mul_le_mul_of_nonneg_left hqh_upper (by norm_num : (0:ℝ) ≤ 2))
    have h2 := mul_le_mul_of_nonneg_right h1 hp2.le
    have h3 : 2*(w/p^2)*p^2 = 2*w := by field_simp
    linarith
  have hεw1 : ε*w ≤ 1/2^40 := by
    have hw14 : w ≤ w^4 := le_self_pow₀ (by linarith) (by norm_num)
    have h1 : ε*w ≤ ε*w^4 := mul_le_mul_of_nonneg_left hw14 he.le
    linarith
  have hεw0 : 0 ≤ ε*w := mul_nonneg he.le hw0.le
  have hε4w : ε^4*w ≤ 1/2^40 := by
    have hε3 : ε^3 ≤ 1 := pow_le_one₀ he.le he1
    have h1 : ε^3*(ε*w) ≤ 1*(ε*w) := mul_le_mul_of_nonneg_right hε3 hεw0
    have e : ε^4*w = ε^3*(ε*w) := by ring
    linarith
  have hε2w : ε^2*w ≤ 1/2^40 := by
    have h1 : ε*(ε*w) ≤ 1*(ε*w) := mul_le_mul_of_nonneg_right he1 hεw0
    have e : ε^2*w = ε*(ε*w) := by ring
    linarith
  -- sampling scale
  have hthin : 32*(t : ℝ)*ε^(4*h+4) ≤ 1 := by
    rw [hpow4]
    have h1 : 32*(t : ℝ)*(p^4*ε^4) = 32*((t : ℝ)*p^2)*(p^2*ε^4) := by ring
    rw [h1]
    have h2 : p^2*ε^4 ≤ ε^4 := by
      have : p^2 ≤ 1 := pow_le_one₀ hp0.le hp1
      nlinarith [pow_pos he 4]
    have h3 : 32*((t : ℝ)*p^2)*(p^2*ε^4) ≤ 32*(2*w)*ε^4 := by
      apply mul_le_mul _ h2 (by positivity) (by positivity)
      linarith
    nlinarith
  -- output size
  have hdelta : ε^(2*h+2) ≤ (q : ℝ)/(512*(t : ℝ)) := by
    rw [hpow22, le_div_iff₀ (by positivity)]
    have hq' : 1 ≤ (q : ℝ)*ε^2 := by
      have := (div_le_iff₀ he2pos).mp hqLower
      linarith
    have h1 : p^2*ε^2*(512*(t : ℝ)) = 512*((t : ℝ)*p^2)*ε^2 := by ring
    rw [h1]
    have h2 : 512*((t : ℝ)*p^2)*ε^2 ≤ 1024*(ε^2*w) := by nlinarith
    have h3 : 1024*(ε^2*w) ≤ 1 := by
      have : (1024 : ℝ)*(1/2^40) ≤ 1 := by norm_num
      linarith
    linarith
  -- logarithms
  set L : ℝ := Real.log (1/ε) with hLdef
  have hlogp : Real.log p = -(h*L) := by
    rw [hpdef, Real.log_rpow he, hLdef, one_div, Real.log_inv]
    ring
  have hXbig : (2 : ℝ)^40 ≤ 1/ε := by
    rw [le_div_iff₀ he]
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^40)).mp hεsmall
    linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 2^40).trans hXbig)
  set δ : ℝ := (q : ℝ)/(512*(t : ℝ)) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hinvδ : 1/δ = 512*(t : ℝ)/(q : ℝ) := by
    rw [hδdef]
    field_simp
  have hD512 : (512 : ℝ) ≤ 1/δ := by
    rw [hinvδ, le_div_iff₀ hq0]
    have : (q : ℝ) ≤ t := by exact_mod_cast hqt
    linarith
  set A : ℝ := Real.log (1/δ) with hAdef
  have hA0 : 0 ≤ A := Real.log_nonneg (by linarith)
  have hA : A ≤ 2*h*L := by
    have hbound : 1/δ ≤ (1024*(ε^2*w))/p^2 := by
      rw [hinvδ, div_le_div_iff₀ hq0 hp2]
      have hq' : 1 ≤ (q : ℝ)*ε^2 := by
        have := (div_le_iff₀ he2pos).mp hqLower
        linarith
      have h1 : 512*(t : ℝ)*p^2 ≤ 1024*w := by linarith
      have h2 : 1024*w ≤ 1024*w*((q : ℝ)*ε^2) := by nlinarith
      nlinarith
    have hpos : 0 < 1024*(ε^2*w) := by positivity
    have h1 := Real.log_le_log (by positivity) hbound
    rw [Real.log_div hpos.ne' hp2.ne', Real.log_pow, hlogp] at h1
    have h2 : Real.log (1024*(ε^2*w)) ≤ 0 := by
      apply Real.log_nonpos hpos.le
      have : (1024 : ℝ)*(1/2^40) ≤ 1 := by norm_num
      linarith
    push_cast at h1
    rw [hAdef]
    linarith
  set D : ℝ := 256*(t : ℝ)/(q : ℝ) with hDdef
  have hD0 : 0 < D := by positivity
  have hDle : D ≤ 1/δ := by
    rw [hinvδ, hDdef]
    apply div_le_div_of_nonneg_right _ hq0.le
    linarith
  have hD1 : 1 ≤ D := by
    rw [hDdef, le_div_iff₀ hq0]
    have : (q : ℝ) ≤ t := by exact_mod_cast hqt
    linarith
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hlogD : Real.log D ≤ A := Real.log_le_log hD0 hDle
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr : (r : ℝ) ≤ A/ε + 1 := by
    rw [hrdef]
    exact (Nat.ceil_lt_add_one (show 0 ≤ A/ε by positivity)).le
  have hqε : 1 ≤ (q : ℝ)*ε^2 := by
    have := (div_le_iff₀ he2pos).mp hqLower
    linarith
  have hRatio : (r : ℝ)/(q : ℝ) ≤ ε*A + ε^2 := by
    rw [div_le_iff₀ hq0]
    have h1 : (A/ε + 1)*ε^2 = ε*A + ε^2 := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_right hr he2pos.le
    rw [h1] at h2
    have h3 : (r : ℝ) ≤ (r : ℝ)*((q : ℝ)*ε^2) := by nlinarith
    nlinarith [mul_nonneg hr0 hq0.le]
  have hErr := bridge_log_error ε h w he hh hw hsmall
  rw [← hLdef] at hErr
  have hB0 : 0 ≤ ε*A + ε^2 := by positivity
  have hRatio0 : 0 ≤ (r : ℝ)/(q : ℝ) := div_nonneg hr0 hq0.le
  have hBA : ε*A + ε^2 ≤ 2*h*ε*L + ε^2 := by nlinarith
  have hprod : (r : ℝ)/(q : ℝ)*Real.log D < 1 := by
    have h1 := mul_le_mul hRatio hlogD hlogD0 hB0
    have h2 : (ε*A + ε^2)*A ≤ (2*h*ε*L + ε^2)*(2*h*L) := by
      apply mul_le_mul hBA hA hA0
      positivity
    have h3 : (2*h*ε*L + ε^2)*(2*h*L) = 4*h^2*ε*L^2 + 2*h*ε^2*L := by ring
    linarith
  have hlt1 : 2*h*ε*L + ε^2 < 1 := by
    have h1 : 2*h*ε*L + ε^2 ≤ (2*h*ε*L + ε^2)*(2*h*L) := by
      have hone : 1 ≤ 2*h*L := by nlinarith
      nlinarith [show 0 ≤ 2*h*ε*L + ε^2 by positivity]
    have h3 : (2*h*ε*L + ε^2)*(2*h*L) = 4*h^2*ε*L^2 + 2*h*ε^2*L := by ring
    linarith
  have hrq : r < q := by
    have h1 := (div_lt_iff₀ hq0).mp (lt_of_le_of_lt (hRatio.trans hBA) hlt1)
    have h2 : (r : ℝ) < (q : ℝ) := by linarith
    exact_mod_cast h2
  exact ⟨hq8, hqt, htLower, hthin, hdelta, hprod, hrq⟩

#print axioms one_add_le_two_rpow
#print axioms bridge_log_error
#print axioms eh_bridge_parameters
end AllPathsLocal
