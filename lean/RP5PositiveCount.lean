import RP5PositiveSelection

namespace AllPathsLocal

theorem actual_positive_count_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {U Y S : Finset V} {x s : ℝ}
    {T : RetainedCutTree G U x s S} {P : List (RootCutStage G)}
    (hP : ActualRetainedPath T P) (hSY : S ⊆ Y)
    (hout : ∀ u ∈ U, u ∉ Y) (hfree : ∀ u ∈ U, RootedP5Free G Y u)
    (hx : 0 < x) (t : ℕ) (ht : 1 ≤ t) (hN : 0 < (S.card : ℝ))
    (hscale : s = (S.card : ℝ) / (t : ℝ)^6) :
    ((positiveBlocks s P).length : ℝ) ≤ 4 * (t : ℝ)^6 / x := by
  classical
  let Z := positiveBlocks s P
  have hprops := actual_positive_blocks_properties hP hSY hout hfree
  have hpair : Z.Pairwise Disjoint := hprops.2.imp (fun h => h.1)
  have hsub : Z.toFinset.biUnion id ⊆ S := by
    intro v hv
    obtain ⟨K, hK, hvK⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    exact (actual_path_subsets_and_roots hP a (List.mem_filter.mp ha).1).1
      (positive_layer_subset_source s a hvK)
  have hmass := list_card_mass_lower Z (x * s / 4) (actual_positive_blocks_lower hP hx.le)
  rw [← disjoint_list_card_mass Z hpair] at hmass
  have hcard : ((Z.toFinset.biUnion id).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hsub
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hbound : (Z.length : ℝ) * (x * ((S.card : ℝ) / (t : ℝ)^6) / 4) ≤ S.card := by
    simpa only [hscale] using hmass.trans hcard
  have he : (Z.length : ℝ) * (x * ((S.card : ℝ) / (t : ℝ)^6) / 4) =
      ((S.card : ℝ) * ((Z.length : ℝ) * x)) / (4 * (t : ℝ)^6) := by ring
  rw [he] at hbound
  have hbound' := (div_le_iff₀ (show 0 < 4 * (t : ℝ)^6 by positivity)).mp hbound
  have hcancel : (Z.length : ℝ) * x ≤ 4 * (t : ℝ)^6 :=
    (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm] using hbound')
  exact (le_div_iff₀ hx).mpr hcancel

theorem positive_count_paper_bound (x t : ℝ) (hx : 0 < x) (hxsmall : x ≤ 1 / 2^16)
    (ht0 : 0 ≤ t) (ht : t ≤ 2 / x^4) :
    4 * t^6 / x ≤ 1 / x^27 := by
  have h6 := pow_le_pow_left₀ ht0 ht 6
  have hupper := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 4)) hx.le
  have he : 4 * (2 / x^4)^6 / x = 256 / x^25 := by field_simp; ring
  rw [he] at hupper
  have hx16 : x ≤ 1 / 16 := hxsmall.trans (by norm_num)
  have hx2 : 256 * x^2 ≤ 1 := by nlinarith
  have hratio : 256 / x^25 ≤ 1 / x^27 := by
    apply (div_le_div_iff₀ (by positivity : 0 < x^25) (by positivity : 0 < x^27)).mpr
    have h := mul_le_mul_of_nonneg_left hx2 (show 0 ≤ x^25 by positivity)
    nlinarith [show x^25 * x^2 = x^27 by ring]
  exact hupper.trans hratio

#print axioms actual_positive_count_bound
#print axioms positive_count_paper_bound

end AllPathsLocal
