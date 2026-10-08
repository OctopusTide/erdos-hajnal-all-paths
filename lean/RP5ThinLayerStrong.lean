import RP5ConditionalThinLayer

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- The paper's ORIGINAL epsilon^2 M / 512 thin-layer conclusion, including
    actual ceil parameters. Its sole remaining graph-theoretic dependency is
    the displayed transversal certificate existence, not a hidden axiom. -/
theorem paper_thin_layer_strong_of_certificates {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (lam epsilon : ℝ) (he : 0 < epsilon) (heSmall : epsilon ≤ 1/65536)
    (hlam : lam ≤ epsilon^4/128)
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam*S.card)
    (hcert : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      Nonempty (CliqueColorCertificate (G.induce (T : Set V)))) :
    ∃ W ⊆ S, epsilon^2*(S.card : ℝ)/512 ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1))) := by
  classical
  have he1 : epsilon ≤ 1 := heSmall.trans (by norm_num)
  have hN0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  obtain ⟨w, hw⟩ := hS
  have hw' : w ∈ layers.biUnion id := by rwa [hcover]
  obtain ⟨A, hA, hwA⟩ := Finset.mem_biUnion.mp hw'
  have hA1 : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.one_le_card.mpr ⟨w, hwA⟩
  have hmass : 1 ≤ lam*(S.card : ℝ) := hA1.trans (hsize A hA)
  have hlam0 : 0 < lam := by nlinarith
  let q := Nat.ceil (1/epsilon^2)
  have hehalf : epsilon ≤ 1/2 := heSmall.trans (by norm_num)
  have he2 := pow_le_pow_left₀ he.le hehalf 2
  have hbig : (4 : ℝ) ≤ 1/epsilon^2 := by
    apply (le_div_iff₀ (show 0 < epsilon^2 by positivity)).mpr
    norm_num at he2
    nlinarith
  have hqLower : 1/epsilon^2 ≤ (q : ℝ) := Nat.le_ceil _
  have hq4 : (4 : ℝ) ≤ q := hbig.trans hqLower
  have hqNat : 4 ≤ q := by exact_mod_cast hq4
  have hq0 : (0 : ℝ) < q := by linarith
  have hqUpper : (q : ℝ) ≤ 2/epsilon^2 := by
    have hh := Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 4).trans hbig)
    convert hh using 1 <;> ring
  obtain ⟨hthin, hdelta⟩ := thin_layer_sampling_scale epsilon (q : ℝ) lam he hq0 hqUpper hlam0.le hlam
  have hNinv : 1/lam ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hlam0).mpr
    simpa only [mul_comm] using hmass
  obtain ⟨hOrder, hOrder2⟩ := thin_layer_required_order (q : ℝ) lam (S.card : ℝ) hq0 hlam0 hthin hNinv
  have hN : 2*(q*q) ≤ S.card := by
    have hh : 2*q^2 ≤ S.card := by exact_mod_cast hOrder2
    simpa only [pow_two] using hh
  let delta : ℝ := 1/(256*(q : ℝ))
  let u := Nat.ceil ((S.card : ℝ)/(256*(q : ℝ)))
  let r := Nat.ceil (Real.log (256*(q : ℝ))/epsilon)
  have hhalf : (2 : ℝ)⁻¹ ≤ (S.card : ℝ)/(256*(q : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 256*(q : ℝ) by positivity)).mpr
    norm_num
    nlinarith
  have hu : (u : ℝ) ≤ (S.card : ℝ)/(128*(q : ℝ)) := by
    have hh := Nat.ceil_le_two_mul hhalf
    convert hh using 1 <;> ring
  have huLower : delta*(S.card : ℝ) ≤ u := by
    have hh := Nat.le_ceil ((S.card : ℝ)/(256*(q : ℝ)))
    convert hh using 1 <;> dsimp [delta]; ring
  have hbudget : (1-epsilon)^r*(S.card : ℝ) ≤ u := by
    have hh := container_ceil_log_budget epsilon delta (S.card : ℝ) (u : ℝ)
      he he1 (by dsimp [delta]; positivity) hN0.le huLower
    dsimp [delta] at hh
    simpa only [one_div_one_div] using hh
  obtain ⟨herror, hrq⟩ := thin_parameter_record_error epsilon q he heSmall hqLower hqUpper
  have hthin' : 32*((q*q : ℕ) : ℝ)*lam ≤ 1 := by
    simpa only [Nat.cast_mul, pow_two] using hthin
  obtain ⟨W, hWS, hWcard, hWdegree⟩ := actual_thin_restricted_of_certificates G S layers hcover hdis
    lam epsilon hlam0.le he.le he1 hsize q r u (by omega) hrq.le hN hthin' hu hbudget herror hcert
  have hWcardR : (u : ℝ) < W.card := by exact_mod_cast hWcard
  have hdeltaM := mul_le_mul_of_nonneg_right hdelta hN0.le
  have hsizeW : epsilon^2*(S.card : ℝ)/512 ≤ W.card := by
    dsimp [delta] at huLower
    nlinarith only [hdeltaM, huLower, hWcardR]
  refine ⟨W, hWS, hsizeW, ?_⟩
  rcases hWdegree with hdeg | hdeg
  · left
    intro v hv
    exact hdeg v hv
  · right
    intro v hv
    exact hdeg v hv

#print axioms paper_thin_layer_strong_of_certificates
end AllPathsLocal
