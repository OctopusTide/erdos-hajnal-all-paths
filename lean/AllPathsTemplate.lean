import AllPathsForcing
import AllPathsSubstEH

/-!
The forcing template (main paper, Proposition "The forcing template"). From a
positive Erdős–Hajnal exponent for `P_h` we obtain a finite graph `Q` with a
positive Erdős–Hajnal exponent such that every two-labelled lift of `Q` contains an
induced path on `h + 1` vertices.
-/

namespace AllPathsLocal

open Finset

theorem lift_hasArm_zero {V ι : Type} {F : SimpleGraph V} {Q : SimpleGraph ι} (L : Lift F Q)
    (i : ι) : L.HasArm 0 := by
  have hsub : ∀ a b : Fin (0 + 1), a = b := by
    intro a b
    exact Fin.ext (by have := a.isLt; have := b.isLt; omega)
  refine ⟨fun _ => i, fun a b _ => hsub a b, fun a b _ => hsub a b, ?_⟩
  intro a b
  have hab := hsub a b
  subst hab
  constructor
  · intro h
    exact absurd h F.irrefl
  · intro h
    omega

theorem forcing_template_aux (s h : ℕ) (hsh : s ≤ h + 1)
    (hEH : ∃ γ : ℝ, 0 < γ ∧ EHOn (EHP6.pathGraph' h) Finset.univ γ) :
    ∀ n, n + 1 ≤ h → ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Nonempty α)
      (Q : SimpleGraph α), (∃ κ : ℝ, 0 < κ ∧ EHOn Q Finset.univ κ) ∧
      ∀ (V : Type) (F : SimpleGraph V) (L : Lift F Q),
        (∃ p : Fin s → V, IsInducedPath F p) ∨ L.HasArm n := by
  intro n
  induction n with
  | zero =>
    intro hh
    haveI : Nonempty (Fin h) := ⟨⟨0, by omega⟩⟩
    refine ⟨LexT (Fin h) 0, inferInstance, inferInstance, inferInstance,
      lexPow (EHP6.pathGraph' h) 0, ehOn_lexPow _ hEH 0, ?_⟩
    intro V F L
    exact Or.inr (lift_hasArm_zero L PUnit.unit)
  | succ n ih =>
    intro hh
    obtain ⟨α, iF, iD, iN, Q, hQEH, hQ⟩ := ih (by omega)
    haveI : Nonempty (Fin h) := ⟨⟨0, by omega⟩⟩
    refine ⟨TowerV α h, inferInstance, inferInstance,
      ⟨⟨⟨0, by omega⟩, Classical.arbitrary _⟩⟩, towerGraph Q h, ?_, ?_⟩
    · exact ehOn_substGraph (EHP6.pathGraph' h) (fun d => lexPow Q (towerExp α d.val)) hEH
        (fun d => ehOn_lexPow Q hQEH _)
    · exact forcing_step Q s n h (by omega) hsh hQ

/-- **The forcing template.** -/
theorem forcing_template (h : ℕ) (hh : 1 ≤ h)
    (hEH : ∃ γ : ℝ, 0 < γ ∧ EHOn (EHP6.pathGraph' h) Finset.univ γ) :
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (Q : SimpleGraph α),
      (∃ κ : ℝ, 0 < κ ∧ EHOn Q Finset.univ κ) ∧
      ∀ (V : Type) (F : SimpleGraph V) (_ : Lift F Q),
        ∃ p : Fin (h + 1) → V, IsInducedPath F p := by
  obtain ⟨α, iF, iD, -, Q, hQEH, hQ⟩ := forcing_template_aux (h + 1) h le_rfl hEH (h - 1) (by omega)
  refine ⟨α, iF, iD, Q, hQEH, fun V F L => ?_⟩
  rcases hQ V F L with hp | harm
  · exact hp
  · obtain ⟨p, hp⟩ := L.arm_path (h - 1) harm
    exact ⟨_, inducedPath_castLE F (by omega : h + 1 ≤ h - 1 + 2) p hp⟩

#print axioms forcing_template
end AllPathsLocal
