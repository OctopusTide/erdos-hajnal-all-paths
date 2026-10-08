import AllPathsEHBridgeScalars

namespace AllPathsLocal
attribute [local instance] Classical.propDecidable

/-- The polynomial thin-layer bridge from EH transversals, at the paper's
    actual real parameters. `h` is any real with `2 ≤ h` and `1 ≤ h*kappa`;
    the paper's `h = max(2, 1/kappa)` is the special case stated below.
    The EH premise on transversals is displayed, not asserted. The restricted
    output uses the stronger degree convention `epsilon(|W|-1)`. -/
theorem eh_transversal_bridge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (kappa h lam epsilon : ℝ) (hkappa : 0 ≤ kappa) (hh : 2 ≤ h) (hhk : 1 ≤ h*kappa)
    (he : 0 < epsilon) (heSmall : epsilon ≤ (2 : ℝ)^(-(4*(h+10))))
    (hlam : lam ≤ epsilon^(4*h+4))
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam*S.card)
    (hEH : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, IsHomogeneousFinset G A ∧ (T.card : ℝ)^kappa ≤ A.card) :
    ∃ W ⊆ S, epsilon^(2*h+2)*(S.card : ℝ) ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1))) := by
  classical
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, q = Nat.ceil (1/epsilon^2) := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ℕ, t = Nat.ceil ((q : ℝ)^h) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ,
      r = Nat.ceil (Real.log (1/((q : ℝ)/(512*(t : ℝ))))/epsilon) := ⟨_, rfl⟩
  obtain ⟨hq8, hqt, htLower, hthinε, hdelta, herror, hrq⟩ :=
    eh_bridge_parameters epsilon h he hh heSmall q t r hqdef htdef hrdef
  have hh0 : 0 ≤ h := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqtR : (q : ℝ) ≤ t := by exact_mod_cast hqt
  have ht0 : (0 : ℝ) < t := by linarith
  have hN0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  -- every layer is nonempty somewhere, so lam*|S| ≥ 1
  obtain ⟨w, hw⟩ := hS
  have hw' : w ∈ layers.biUnion id := by rwa [hcover]
  obtain ⟨A, hA, hwA⟩ := Finset.mem_biUnion.mp hw'
  have hA1 : (1 : ℝ) ≤ A.card := by exact_mod_cast Finset.one_le_card.mpr ⟨w, hwA⟩
  have hmass : 1 ≤ lam*(S.card : ℝ) := hA1.trans (hsize A hA)
  have hlam0 : 0 < lam := by
    by_contra hneg
    have hle : lam ≤ 0 := not_lt.mp hneg
    have := mul_nonpos_of_nonpos_of_nonneg hle hN0.le
    linarith
  have hsmall40 : epsilon ≤ 1 := by
    have h1 : (2 : ℝ)^(-(4*(h+10))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    exact heSmall.trans h1
  have hthin : 32*(t : ℝ)*lam ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hlam (show (0 : ℝ) ≤ 32*(t : ℝ) by positivity)
    linarith
  have hNbig : 32*(t : ℝ) ≤ S.card := by
    have h1 := mul_le_mul_of_nonneg_right hthin hN0.le
    have h2 := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 32*(t : ℝ) by positivity)
    nlinarith
  have hN : 2*t ≤ S.card := by
    have h1 : ((2*t : ℕ) : ℝ) ≤ S.card := by
      push_cast
      linarith
    exact_mod_cast h1
  set delta : ℝ := (q : ℝ)/(512*(t : ℝ)) with hdeltadef
  have hdelta0 : 0 < delta := by positivity
  set D : ℝ := 256*(t : ℝ)/(q : ℝ) with hDdef
  have hD0 : 0 < D := by positivity
  have hD : 128*(t : ℝ)/(q : ℝ) ≤ D := by
    rw [hDdef]
    apply div_le_div_of_nonneg_right _ hq0.le
    linarith
  have hDdelta : (S.card : ℝ)/D = 2*(delta*(S.card : ℝ)) := by
    rw [hDdef, hdeltadef]
    field_simp
    ring
  let u := Nat.ceil (delta*(S.card : ℝ))
  have hhalf : (2 : ℝ)⁻¹ ≤ delta*(S.card : ℝ) := by
    have h1 : delta*(32*(t : ℝ)) ≤ delta*(S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hNbig hdelta0.le
    have h2 : delta*(32*(t : ℝ)) = (q : ℝ)/16 := by
      rw [hdeltadef]
      field_simp
      ring
    have hq8R : (8 : ℝ) ≤ q := by exact_mod_cast hq8
    linarith
  have hu : (u : ℝ) ≤ (S.card : ℝ)/D := by
    rw [hDdelta]
    exact Nat.ceil_le_two_mul hhalf
  have huLower : delta*(S.card : ℝ) ≤ u := Nat.le_ceil _
  have hbudget : (1-epsilon)^r*(S.card : ℝ) ≤ u := by
    rw [hrdef]
    exact container_ceil_log_budget epsilon delta (S.card : ℝ) (u : ℝ)
      he hsmall40 hdelta0 hN0.le huLower
  have hpower : (q : ℝ) ≤ (t : ℝ)^kappa := by
    have h1 : (q : ℝ) ≤ (q : ℝ)^(h*kappa) := by
      have := Real.rpow_le_rpow_of_exponent_le hq1 hhk
      simpa using this
    have h2 : (q : ℝ)^(h*kappa) = ((q : ℝ)^h)^kappa := Real.rpow_mul hq0.le h kappa
    have h3 : ((q : ℝ)^h)^kappa ≤ (t : ℝ)^kappa :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0.le h) htLower hkappa
    linarith
  obtain ⟨W, hWS, hWcard, hWdegree⟩ := eh_transversal_integer_thin_layer G S layers hcover hdis
    lam epsilon hlam0.le he.le hsmall40 hsize q r u t hqt (by omega) hrq.le hN hthin
    D hD0 hD hu hbudget herror kappa hkappa hpower hEH
  have hWcardR : (u : ℝ) < W.card := by exact_mod_cast hWcard
  refine ⟨W, hWS, ?_, hWdegree⟩
  have h1 := mul_le_mul_of_nonneg_right hdelta hN0.le
  linarith

/-- The same theorem at the paper's literal choice `h = max(2, 1/kappa)`. -/
theorem eh_transversal_bridge_paper {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (layers : Finset (Finset V))
    (hcover : layers.biUnion id = S)
    (hdis : ∀ A ∈ layers, ∀ B ∈ layers, A ≠ B → Disjoint A B)
    (kappa lam epsilon : ℝ) (hkappa : 0 < kappa)
    (he : 0 < epsilon) (heSmall : epsilon ≤ (2 : ℝ)^(-(4*(max 2 (1/kappa)+10))))
    (hlam : lam ≤ epsilon^(4*(max 2 (1/kappa))+4))
    (hsize : ∀ A ∈ layers, (A.card : ℝ) ≤ lam*S.card)
    (hEH : ∀ T : Finset V, T ⊆ S →
      (∀ A ∈ layers, (T ∩ A).card ≤ 1) →
      ∃ A ⊆ T, IsHomogeneousFinset G A ∧ (T.card : ℝ)^kappa ≤ A.card) :
    ∃ W ⊆ S, epsilon^(2*(max 2 (1/kappa))+2)*(S.card : ℝ) ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ epsilon*((W.card : ℝ)-1))) := by
  have hhk : 1 ≤ max 2 (1/kappa)*kappa := by
    have h1 : 1/kappa ≤ max 2 (1/kappa) := le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 hkappa.le
    have h3 : 1/kappa*kappa = 1 := by field_simp
    linarith
  exact eh_transversal_bridge G S hS layers hcover hdis kappa (max 2 (1/kappa)) lam epsilon
    hkappa.le (le_max_left _ _) hhk he heSmall hlam hsize hEH

#print axioms eh_transversal_bridge
#print axioms eh_transversal_bridge_paper
end AllPathsLocal
