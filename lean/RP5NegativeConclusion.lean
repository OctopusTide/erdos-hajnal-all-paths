import RP5NegativeLayerGeometry

namespace AllPathsLocal

/-- The actual large negative path gives the ORIGINAL y^18 size and stronger
    y^4(|W|-1) restricted-degree conclusion. All transversal certificates are
    constructed from the roots, rather than assumed as an extra premise. -/
theorem actual_negative_direction_conclusion {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s Y} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (y : ℝ) (hy : 0 < y) (hySmall : y ≤ 1 / 2^16)
    (hY : 0 < (Y.card : ℝ)) (t : ℕ) (ht : 0 < (t : ℝ))
    (htLower : 1 / y^4 ≤ (t : ℝ)) (htUpper : (t : ℝ) ≤ 2 / y^4)
    (hscale : s = (Y.card : ℝ) / (t : ℝ)^6)
    (hmass : 3 * (Y.card : ℝ) / (8 * t) ≤
      (P.map (fun a => ((negativeLayer s a).card : ℝ))).sum) :
    ∃ W ⊆ Y, y^18*(Y.card : ℝ) ≤ W.card ∧
      ((∀ v ∈ W, ((W.filter (G.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1)) ∨
       (∀ v ∈ W, ((W.filter (Gᶜ.Adj v)).card : ℝ) ≤ y^4*((W.card : ℝ)-1))) := by
  classical
  let layers := (P.map (negativeLayer s)).toFinset
  let Mset := layers.biUnion id
  let M : ℝ := Mset.card
  obtain ⟨hMY, hdis, hcard⟩ := actual_negative_layer_geometry hP
  change Mset ⊆ Y at hMY
  change (Mset.card : ℝ) = _ at hcard
  have hM : 3 * (Y.card : ℝ) / (8 * t) ≤ M := by simpa only [M, hcard] using hmass
  have hM0 : 0 < M := (show 0 < 3*(Y.card : ℝ)/(8*t) by positivity).trans_le hM
  have hMset : Mset.Nonempty := Finset.card_pos.mp (by
    have hMc : (0 : ℝ) < Mset.card := hM0
    exact_mod_cast hMc)
  have hs : 0 ≤ s := by rw [hscale]; positivity
  let lam : ℝ := s/M
  have hlam : lam ≤ (y^4)^4/128 := by
    have hfrac := negative_layer_fraction_bound (Y.card : ℝ) M (t : ℝ) hY.le hM0 ht hM
    have hh := hfrac.trans (negative_fraction_y_bound y (t : ℝ) hy hySmall htLower)
    simpa only [lam, hscale, show (y^4)^4 = y^16 by ring] using hh
  have hsize : ∀ L ∈ layers, (L.card : ℝ) ≤ lam*Mset.card := by
    intro L hL
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    have he : lam*Mset.card = s := div_mul_cancel₀ s hM0.ne'
    rw [he]
    exact negative_layer_size_bound s hs a
  have heSmall : y^4 ≤ 1/65536 := by
    have h4 := pow_le_pow_left₀ hy.le hySmall 4
    norm_num at h4
    linarith
  obtain ⟨W, hWM, hsizeW, hdeg⟩ := paper_thin_layer_strong_of_certificates Gᶜ Mset hMset layers
    rfl hdis lam (y^4) (by positivity) heSmall hlam hsize
    (fun A hAM hthin => actual_negative_transversal_certificate hP (Finset.Subset.refl Y)
      hout hfree A hAM hthin)
  refine ⟨W, hWM.trans hMY, ?_, ?_⟩
  · apply negative_thin_output_size y (t : ℝ) (Y.card : ℝ) M (W.card : ℝ)
      hy hySmall hY.le ht htUpper hM
    simpa only [show (y^4)^2 = y^8 by ring] using hsizeW
  · simpa only [compl_compl, filter_card_classical] using hdeg.symm

#print axioms actual_negative_direction_conclusion
end AllPathsLocal
