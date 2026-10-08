import RP5Frontier

/-! Record at most one witness for each later block, retaining ALL roots selected for
    a fixed earlier block. This implements the quantifiers in III.1--III.3. -/

namespace AllPathsLocal

def RootSeparates {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (u : V) (A B : Finset V) : Prop :=
  (∀ a ∈ A, G.Adj u a) ∧ ∀ b ∈ B, ¬ G.Adj u b

theorem recorded_root_families {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) {m : ℕ} (Z : Fin m → Finset V) :
    ∃ R : Fin m → Finset V, ∀ j,
      (R j).card ≤ m - 1 ∧ R j ⊆ U ∧
      (∀ u ∈ R j, ∀ v ∈ Z j, G.Adj u v) ∧
      ∀ l, j < l → (∃ u ∈ U, RootSeparates G u (Z j) (Z l)) →
        ∃ u ∈ R j, RootSeparates G u (Z j) (Z l) := by
  classical
  have hex : ∀ j : Fin m, ∃ R : Finset V,
      R.card ≤ m - 1 ∧ R ⊆ U ∧
      (∀ u ∈ R, ∀ v ∈ Z j, G.Adj u v) ∧
      ∀ l, j < l → (∃ u ∈ U, RootSeparates G u (Z j) (Z l)) →
        ∃ u ∈ R, RootSeparates G u (Z j) (Z l) := by
    intro j
    let T := Finset.univ.filter (fun l : Fin m =>
      j < l ∧ ∃ u ∈ U, RootSeparates G u (Z j) (Z l))
    have hwitness : ∀ l, l ∈ T → ∃ u ∈ U, RootSeparates G u (Z j) (Z l) := by
      intro l hl
      exact (Finset.mem_filter.mp hl).2.2
    choose r hrU hrsep using hwitness
    let R := T.attach.image (fun l => r l.val l.prop)
    have hTsub : T ⊆ Finset.univ.erase j := by
      intro l hl
      exact Finset.mem_erase.mpr ⟨ne_of_gt (Finset.mem_filter.mp hl).2.1, Finset.mem_univ _⟩
    have hTbound : T.card ≤ m - 1 := by
      have hh := Finset.card_le_card hTsub
      simpa using hh
    have hRbound : R.card ≤ T.card := by
      have hh := Finset.card_image_le (s := T.attach) (f := fun l => r l.val l.prop)
      simpa only [Finset.card_attach] using hh
    refine ⟨R, hRbound.trans hTbound, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hu
      exact hrU l.val l.prop
    · intro u hu v hv
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hu
      exact (hrsep l.val l.prop).1 v hv
    · intro l hjl hsep
      have hlT : l ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjl, hsep⟩
      refine ⟨r l hlT, ?_, hrsep l hlT⟩
      exact Finset.mem_image.mpr ⟨⟨l, hlT⟩, Finset.mem_attach _ _, rfl⟩
  choose R hR using hex
  exact ⟨R, hR⟩

/-- Restricting blocks retains every recorded root and its full/empty incidences. -/
theorem rootSeparation_mono {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {u : V} {A B A' B' : Finset V} (h : RootSeparates G u A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B) : RootSeparates G u A' B' := by
  exact ⟨fun a ha => h.1 a (hA ha), fun b hb => h.2 b (hB hb)⟩

#print axioms recorded_root_families
#print axioms rootSeparation_mono

end AllPathsLocal
