import AllPathsEHBridge
import RP5NegativeLayerGeometry

namespace AllPathsLocal

/-- EH exponent `kappa` for the ordered class `E_(n+1)` inside an ambient graph
    property `Amb`: every finite member has a homogeneous set of size at least
    `|W|^kappa`. This is a HYPOTHESIS of the RPq negative branch, displayed
    as a predicate; nothing here asserts it. -/
def OrderedClassEH (Amb : ∀ (W : Type), SimpleGraph W → Prop) (n : ℕ) (kappa : ℝ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W) (ord : LinearOrder W),
    Amb W H → @OrderedFirstEndpointFree W ord.toLT H n →
    ∃ A : Finset W, IsHomogeneousFinset H A ∧ ((Fintype.card W : ℝ))^kappa ≤ A.card

/-- A homogeneous set of the induced complement on `T` is a homogeneous
    subset of `T` in the original graph, of the same cardinality. -/
theorem homogeneous_of_induced_compl {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (T : Finset V) (A : Finset ↥(T : Set V))
    (hA : IsHomogeneousFinset (Gᶜ.induce (T : Set V)) A) :
    ∃ B ⊆ T, B.card = A.card ∧ IsHomogeneousFinset G B := by
  classical
  refine ⟨A.map (Function.Embedding.subtype _), ?_, Finset.card_map _, ?_⟩
  · intro v hv
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
    exact a.property
  · rcases hA with hclique | hstable
    · right
      intro u hu v hv hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      have hne : a ≠ b := by
        intro he
        subst he
        exact G.irrefl hadj
      have hc := hclique a ha b hb hne
      exact ((G.compl_adj _ _).mp hc).2 hadj
    · left
      intro u hu v hv hne
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      by_contra hnot
      exact hstable a ha b hb ((G.compl_adj _ _).mpr ⟨hne, hnot⟩)

/-- All scalar conditions of the RPq negative branch at tree exponent `d`
    (the paper's `d_t = ceil(4h+5)`), tree parameter `1/y^d ≤ t ≤ 2/y^d`,
    target `epsilon = y^4` and negative mass `M ≥ 3N/(8t)`. -/
theorem negative_bridge_scalars (y h : ℝ) (d : ℕ) (t N M : ℝ) (hy : 0 < y) (hh : 2 ≤ h)
    (hySmall : y ≤ (2 : ℝ)^(-(h+10))) (hd : 4*h+5 ≤ (d : ℝ))
    (htLower : 1/y^d ≤ t) (htUpper : t ≤ 2/y^d) (hN : 0 ≤ N) (hM : 3*N/(8*t) ≤ M) :
    y^4 ≤ (2 : ℝ)^(-(4*(h+10))) ∧ 8/(3*t^5) ≤ (y^4)^(4*h+4) ∧
      y^(8*h+(d : ℝ)+10)*N ≤ (y^4)^(2*h+2)*M := by
  have hyd : 0 < y^d := pow_pos hy d
  have ht0 : 0 < t := (show 0 < 1/y^d by positivity).trans_le htLower
  have h12 : (2 : ℝ)^(-(h+10)) ≤ 1/4096 := by
    have h1 : (2 : ℝ)^(-(h+10)) ≤ (2 : ℝ)^((-12 : ℤ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    have e : (2 : ℝ)^((-12 : ℤ) : ℝ) = 1/4096 := by
      rw [Real.rpow_intCast]
      norm_num
    rw [e] at h1
    exact h1
  have hy12 : y ≤ 1/4096 := hySmall.trans h12
  have hy1 : y ≤ 1 := hy12.trans (by norm_num)
  have hpow4 : ∀ a : ℝ, (y^4)^a = y^(4*a) := by
    intro a
    rw [← Real.rpow_natCast y 4, ← Real.rpow_mul hy.le]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · have h1 := pow_le_pow_left₀ hy.le hySmall 4
    have h2 : ((2 : ℝ)^(-(h+10)))^4 = (2 : ℝ)^(-(4*(h+10))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rwa [h2] at h1
  · rw [hpow4]
    have ht5 := pow_le_pow_left₀ (show 0 ≤ 1/y^d by positivity) htLower 5
    have hrec : 1/t^5 ≤ (y^d)^5 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1/y^d)^5*(y^d)^5 = 1 := by
        rw [← mul_pow]
        have : 1/y^d*y^d = 1 := by field_simp
        rw [this]
        norm_num
      nlinarith [pow_pos hyd 5]
    have hnat : (y^d)^5 = y^(((d*5 : ℕ) : ℝ)) := by
      rw [← pow_mul, Real.rpow_natCast]
    have hexp : y^(((d*5 : ℕ) : ℝ)) ≤ y^(4*(4*h+4)+((9 : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hy hy1
      push_cast
      linarith
    have hsplit : y^(4*(4*h+4)+((9 : ℕ) : ℝ)) = y^(4*(4*h+4))*y^9 := by
      rw [Real.rpow_add hy, Real.rpow_natCast]
    have hbase : 0 < y^(4*(4*h+4)) := Real.rpow_pos_of_pos hy _
    have hy9 : (8/3 : ℝ)*y^9 ≤ 1 := by
      have h9 := pow_le_pow_left₀ hy.le hy12 9
      have : ((1 : ℝ)/4096)^9 ≤ 3/8 := by norm_num
      linarith
    have h1 : 8/(3*t^5) = (8/3)*(1/t^5) := by
      field_simp
    rw [h1]
    have h2 : (8/3 : ℝ)*(1/t^5) ≤ (8/3)*(y^(4*(4*h+4))*y^9) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← hsplit]
      exact hrec.trans (hnat.le.trans hexp)
    have h3 : (8/3 : ℝ)*(y^(4*(4*h+4))*y^9) = y^(4*(4*h+4))*((8/3)*y^9) := by ring
    rw [h3] at h2
    exact h2.trans (by nlinarith)
  · rw [hpow4]
    have hsplit : y^(8*h+(d : ℝ)+10) = y^(4*(2*h+2))*(y^d*y^2) := by
      rw [show 8*h+(d : ℝ)+10 = 4*(2*h+2)+((d : ℕ) : ℝ)+((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_add hy, Real.rpow_add hy, Real.rpow_natCast, Real.rpow_natCast]
      ring
    rw [hsplit]
    have hbase : 0 < y^(4*(2*h+2)) := Real.rpow_pos_of_pos hy _
    have hMt := (div_le_iff₀ (show 0 < 8*t by positivity)).mp hM
    have hty : t*y^d ≤ 2 := by
      have := mul_le_mul_of_nonneg_right htUpper hyd.le
      have he : 2/y^d*y^d = 2 := by field_simp
      linarith
    have hM0 : 0 ≤ M := (show 0 ≤ 3*N/(8*t) by positivity).trans hM
    have hMlower : 3*(y^d*N) ≤ 16*M := by
      have h1 : 3*N*y^d ≤ M*(8*t)*y^d := mul_le_mul_of_nonneg_right hMt hyd.le
      have h2 : M*(8*t)*y^d = 8*M*(t*y^d) := by ring
      have h3 : 8*M*(t*y^d) ≤ 8*M*2 := mul_le_mul_of_nonneg_left hty (by positivity)
      linarith
    have hy2 : y^2 ≤ 3/16 := by
      have h2 := pow_le_pow_left₀ hy.le hy12 2
      have : ((1 : ℝ)/4096)^2 ≤ 3/16 := by norm_num
      linarith
    have hfinal : y^d*y^2*N ≤ M := by
      have h1 : y^d*y^2*N = y^2*(y^d*N) := by ring
      rw [h1]
      have h2 : y^2*(y^d*N) ≤ 3/16*(y^d*N) :=
        mul_le_mul_of_nonneg_right hy2 (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left hfinal hbase.le
    calc y^(4*(2*h+2))*(y^d*y^2)*N = y^(4*(2*h+2))*(y^d*y^2*N) := by ring
      _ ≤ y^(4*(2*h+2))*M := this

/-- The RPq negative direction: an actual negative path of large mass yields a
    `y^4`-restricted set of size `y^(8h+d+10)|Y|`. The roots exclude RP(n+2);
    negative transversals are constructed members of `E_(n+1)` in the original
    complement, and the EH exponent of that ordered class inside the ambient
    property is the displayed hypothesis `hEH`. -/
theorem actual_negative_direction_conclusion_eh {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s Y} {P : List (RootCutStage G)}
    (n : ℕ) (hP : ActualRetainedPath T P)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedPathFree G (n+2) Y u)
    (Amb : ∀ (W : Type), SimpleGraph W → Prop)
    (hAmb : ∀ A : Finset V, A ⊆ Y → Amb ↥(A : Set V) (Gᶜ.induce (A : Set V)))
    (kappa h : ℝ) (hkappa : 0 ≤ kappa) (hh : 2 ≤ h) (hhk : 1 ≤ h*kappa)
    (hEH : OrderedClassEH Amb n kappa)
    (y : ℝ) (hy : 0 < y) (hySmall : y ≤ (2 : ℝ)^(-(h+10)))
    (hY : 0 < (Y.card : ℝ)) (d t : ℕ) (hd : 4*h+5 ≤ (d : ℝ))
    (htLower : 1/y^d ≤ (t : ℝ)) (htUpper : (t : ℝ) ≤ 2/y^d)
    (hscale : s = (Y.card : ℝ)/(t : ℝ)^6)
    (hmass : 3*(Y.card : ℝ)/(8*t) ≤
      (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum) :
    ∃ W ⊆ Y, y^(8*h+(d : ℝ)+10)*(Y.card : ℝ) ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1))) := by
  classical
  have ht : (0 : ℝ) < t := (show (0 : ℝ) < 1/y^d by positivity).trans_le htLower
  let layers := (P.map (negativeLayer s)).toFinset
  let Mset := layers.biUnion id
  let M : ℝ := Mset.card
  obtain ⟨hMY, hdis, hcard⟩ := actual_negative_layer_geometry hP
  change Mset ⊆ Y at hMY
  change (Mset.card : ℝ) = _ at hcard
  have hM : 3*(Y.card : ℝ)/(8*t) ≤ M := by simpa only [M, hcard] using hmass
  have hM0 : 0 < M := (show 0 < 3*(Y.card : ℝ)/(8*t) by positivity).trans_le hM
  have hMset : Mset.Nonempty := Finset.card_pos.mp (by
    have hMc : (0 : ℝ) < Mset.card := hM0
    exact_mod_cast hMc)
  have hs : 0 ≤ s := by rw [hscale]; positivity
  obtain ⟨heSmall, hfracY, hout_size⟩ := negative_bridge_scalars y h d (t : ℝ) (Y.card : ℝ) M
    hy hh hySmall hd htLower htUpper hY.le hM
  let lam : ℝ := s/M
  have hlam : lam ≤ (y^4)^(4*h+4) := by
    have hfrac := negative_layer_fraction_bound (Y.card : ℝ) M (t : ℝ) hY.le hM0 ht hM
    have hh' := hfrac.trans hfracY
    simpa only [lam, hscale] using hh'
  have hsize : ∀ L ∈ layers, (L.card : ℝ) ≤ lam*Mset.card := by
    intro L hL
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    have he : lam*Mset.card = s := div_mul_cancel₀ s hM0.ne'
    rw [he]
    exact negative_layer_size_bound s hs a
  have hEH' : ∀ A : Finset V, A ⊆ Mset → (∀ L ∈ layers, (A ∩ L).card ≤ 1) →
      ∃ B ⊆ A, IsHomogeneousFinset G B ∧ (A.card : ℝ)^kappa ≤ B.card := by
    intro A hAM hthin
    obtain ⟨ord, hord⟩ := actual_negative_transversal_ordered_path_free n hP hout hfree A hAM hthin
    obtain ⟨C, hC, hCcard⟩ := hEH ↥(A : Set V) (Gᶜ.induce (A : Set V)) ord
      (hAmb A (hAM.trans hMY)) hord
    obtain ⟨B, hBA, hBcard, hB⟩ := homogeneous_of_induced_compl G A C hC
    refine ⟨B, hBA, hB, ?_⟩
    have hcardA : Fintype.card ↥(A : Set V) = A.card := by simp
    rw [hBcard, ← hcardA]
    exact hCcard
  obtain ⟨W, hWM, hsizeW, hdeg⟩ := eh_transversal_bridge G Mset hMset layers rfl hdis
    kappa h lam (y^4) hkappa hh hhk (by positivity) heSmall hlam hsize hEH'
  exact ⟨W, hWM.trans hMY, hout_size.trans hsizeW,
    by simpa only [filter_card_classical] using hdeg⟩

#print axioms homogeneous_of_induced_compl
#print axioms negative_bridge_scalars
#print axioms actual_negative_direction_conclusion_eh
end AllPathsLocal
