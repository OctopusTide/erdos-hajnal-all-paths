import AllPathsTower

/-!
Two-labelled lifts and arms (main paper, Part I, "Two-labelled lifts and the forcing
invariant"). The diagonal pairs `z i`, `b i` are unconstrained, so every statement
below holds for independent diagonal choices.
-/

namespace AllPathsLocal

theorem inducedPath_rev {V : Type} (G : SimpleGraph V) {n : ℕ} (p : Fin n → V)
    (hp : IsInducedPath G p) : IsInducedPath G (fun i => p (Fin.rev i)) := by
  refine ⟨fun i j h => Fin.rev_injective (hp.1 h), fun i j => ?_⟩
  rw [hp.2]
  simp only [Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem inducedPath_castLE {V : Type} (G : SimpleGraph V) {m n : ℕ} (h : m ≤ n)
    (p : Fin n → V) (hp : IsInducedPath G p) :
    IsInducedPath G (fun i : Fin m => p (Fin.castLE h i)) := by
  refine ⟨fun i j hij => Fin.castLE_injective h (hp.1 hij), fun i j => ?_⟩
  rw [hp.2]
  simp only [Fin.val_castLE]

/-- Concatenation of two induced paths joined by exactly one edge. -/
theorem inducedPath_append {V : Type} (G : SimpleGraph V) {n m : ℕ}
    (p : Fin n → V) (q : Fin m → V) (hp : IsInducedPath G p) (hq : IsInducedPath G q)
    (hne : ∀ i j, p i ≠ q j)
    (hadj : ∀ i j, G.Adj (p i) (q j) ↔ (i.val + 1 = n ∧ j.val = 0)) :
    IsInducedPath G (Fin.append p q) := by
  constructor
  · intro i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · simp only [Fin.append_left]
      intro h
      rw [hp.1 h]
    · simp only [Fin.append_left, Fin.append_right]
      intro h
      exact absurd h (hne a b)
    · simp only [Fin.append_left, Fin.append_right]
      intro h
      exact absurd h.symm (hne b a)
    · simp only [Fin.append_right]
      intro h
      rw [hq.1 h]
  · intro i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · simp only [Fin.append_left, Fin.val_castAdd]
      exact hp.2 a b
    · simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
      rw [hadj]
      have ha := a.isLt
      omega
    · simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
      rw [G.adj_comm, hadj]
      have hb := b.isLt
      omega
    · simp only [Fin.append_right, Fin.val_natAdd]
      rw [hq.2]
      omega

/-- A two-labelled lift of the template `Q` inside `F`: a root `v`, the `z`-labelled
    and the `b`-labelled vertices. `b`-`b` edges form a spanning subgraph of `Q`;
    the diagonal pairs `z i`, `b i` are unconstrained. -/
structure Lift {V ι : Type} (F : SimpleGraph V) (Q : SimpleGraph ι) where
  v : V
  z : ι → V
  b : ι → V
  hvz : ∀ i, F.Adj v (z i)
  hvb : ∀ i, ¬ F.Adj v (b i)
  hvb_ne : ∀ i, v ≠ b i
  hz_inj : Function.Injective z
  hb_inj : Function.Injective b
  hzb_ne : ∀ i j, z i ≠ b j
  hzz : ∀ i j, i ≠ j → (F.Adj (z i) (z j) ↔ Q.Adj i j)
  hzb : ∀ i j, i ≠ j → (F.Adj (z i) (b j) ↔ Q.Adj i j)
  hbb : ∀ i j, F.Adj (b i) (b j) → Q.Adj i j

/-- Restriction of a lift along an induced copy of a smaller template. -/
def Lift.comp {V ι κ : Type} {F : SimpleGraph V} {Q : SimpleGraph ι} {Q' : SimpleGraph κ}
    (L : Lift F Q) (e : κ → ι) (he : Function.Injective e)
    (hadj : ∀ a b, Q.Adj (e a) (e b) ↔ Q'.Adj a b) : Lift F Q' where
  v := L.v
  z := fun a => L.z (e a)
  b := fun a => L.b (e a)
  hvz := fun a => L.hvz (e a)
  hvb := fun a => L.hvb (e a)
  hvb_ne := fun a => L.hvb_ne (e a)
  hz_inj := fun a b h => he (L.hz_inj h)
  hb_inj := fun a b h => he (L.hb_inj h)
  hzb_ne := fun a b => L.hzb_ne (e a) (e b)
  hzz := fun a b hab => (L.hzz (e a) (e b) (fun h => hab (he h))).trans (hadj a b)
  hzb := fun a b hab => (L.hzb (e a) (e b) (fun h => hab (he h))).trans (hadj a b)
  hbb := fun a b h => (hadj a b).mp (L.hbb (e a) (e b) h)

/-- An `(n+1)`-arm: an induced path whose first vertex is `z`-labelled and whose
    other `n` vertices are `b`-labelled, on pairwise distinct indices. -/
def Lift.HasArm {V ι : Type} {F : SimpleGraph V} {Q : SimpleGraph ι} (L : Lift F Q)
    (n : ℕ) : Prop :=
  ∃ idx : Fin (n + 1) → ι, Function.Injective idx ∧
    IsInducedPath F (fun k => if k = 0 then L.z (idx k) else L.b (idx k))

/-- Prepending the root to an `(n+1)`-arm gives an induced path on `n+2` vertices. -/
theorem Lift.arm_path {V ι : Type} {F : SimpleGraph V} {Q : SimpleGraph ι} (L : Lift F Q)
    (n : ℕ) (h : L.HasArm n) : ∃ p : Fin (n + 2) → V, IsInducedPath F p := by
  obtain ⟨idx, _, hp⟩ := h
  refine ⟨_, prefix_inducedPath F _ L.v hp ?_ ?_⟩
  · intro k
    by_cases hk : k = 0
    · simp only [if_pos hk]
      exact F.ne_of_adj (L.hvz _)
    · simp only [if_neg hk]
      exact L.hvb_ne _
  · intro k
    by_cases hk : k = 0
    · simp only [if_pos hk]
      exact ⟨fun _ => hk, fun _ => L.hvz _⟩
    · simp only [if_neg hk]
      exact ⟨fun h => absurd h (L.hvb _), fun h => absurd h hk⟩

/-- An arm of a restricted lift is an arm of the original lift. -/
theorem Lift.comp_arm {V ι κ : Type} {F : SimpleGraph V} {Q : SimpleGraph ι}
    {Q' : SimpleGraph κ} (L : Lift F Q) (e : κ → ι) (he : Function.Injective e)
    (hadj : ∀ a b, Q.Adj (e a) (e b) ↔ Q'.Adj a b) (n : ℕ)
    (h : (L.comp e he hadj).HasArm n) : L.HasArm n := by
  obtain ⟨idx, hinj, hp⟩ := h
  exact ⟨fun k => e (idx k), fun a b hab => hinj (he hab), hp⟩

#print axioms inducedPath_rev
#print axioms inducedPath_castLE
#print axioms inducedPath_append
#print axioms Lift.arm_path
#print axioms Lift.comp_arm
end AllPathsLocal
