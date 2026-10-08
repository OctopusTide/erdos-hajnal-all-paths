import AllPathsSubstitution

/-!
Substitution graphs, lexicographic powers and vertex Ramsey enlargement
(main paper, Part I, "Ramsey enlargement"). Every `c`-colouring of the vertices of
the `c`-fold lexicographic power of `A` has a monochromatic induced copy of `A`,
and substitution preserves a positive Erdős–Hajnal exponent.
-/

namespace AllPathsLocal

open Finset

/-- The substitution `A[B_a : a]`: each vertex `a` of `A` is replaced by `B a`. -/
def substGraph {α : Type} {β : α → Type} (A : SimpleGraph α) (B : ∀ a, SimpleGraph (β a)) :
    SimpleGraph (Σ a, β a) where
  Adj p q := A.Adj p.1 q.1 ∨ ∃ h : p.1 = q.1, (B q.1).Adj (h ▸ p.2) q.2
  symm := ⟨by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    rcases h with h | ⟨h, hh⟩
    · exact Or.inl (A.adj_symm h)
    · dsimp only at h
      subst h
      exact Or.inr ⟨rfl, (B a).adj_symm hh⟩⟩
  loopless := ⟨by
    rintro ⟨a, x⟩ h
    rcases h with h | ⟨h, hh⟩
    · exact A.irrefl h
    · exact (B a).irrefl hh⟩

theorem substGraph_adj_of_ne {α : Type} {β : α → Type} (A : SimpleGraph α)
    (B : ∀ a, SimpleGraph (β a)) {a b : α} (hab : a ≠ b) (x : β a) (y : β b) :
    (substGraph A B).Adj ⟨a, x⟩ ⟨b, y⟩ ↔ A.Adj a b := by
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · exact absurd h hab
  · exact fun h => Or.inl h

theorem substGraph_adj_same {α : Type} {β : α → Type} (A : SimpleGraph α)
    (B : ∀ a, SimpleGraph (β a)) (a : α) (x y : β a) :
    (substGraph A B).Adj ⟨a, x⟩ ⟨a, y⟩ ↔ (B a).Adj x y := by
  constructor
  · rintro (h | ⟨_, hh⟩)
    · exact absurd h A.irrefl
    · exact hh
  · exact fun h => Or.inr ⟨rfl, h⟩

/-- Vertices of the `n`-fold lexicographic power. -/
def LexT (α : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Σ _ : α, LexT α n

/-- The `n`-fold lexicographic power `R(A, n)`; `R(A, 0)` is a single vertex. -/
def lexPow {α : Type} (A : SimpleGraph α) : (n : ℕ) → SimpleGraph (LexT α n)
  | 0 => ⊥
  | n + 1 => substGraph A (fun _ => lexPow A n)

theorem lexT_nonempty (α : Type) [Nonempty α] : ∀ n, Nonempty (LexT α n)
  | 0 => ⟨PUnit.unit⟩
  | n + 1 => by
    obtain ⟨x⟩ := lexT_nonempty α n
    exact ⟨⟨Classical.arbitrary α, x⟩⟩

/-- **Vertex Ramsey enlargement.** Every colouring of `R(A, n)` using at most `n`
    colours has a monochromatic induced copy of `A`. -/
theorem lexPow_ramsey {α κ : Type} [DecidableEq κ] (A : SimpleGraph α) :
    ∀ (n : ℕ) (col : LexT α n → κ) (C : Finset κ), (∀ x, col x ∈ C) → C.card ≤ n →
      ∃ f : α → LexT α n, Function.Injective f ∧
        (∀ a b, (lexPow A n).Adj (f a) (f b) ↔ A.Adj a b) ∧ ∀ a b, col (f a) = col (f b)
  | 0, col, C, hC, hcard => by
    exfalso
    have h0 : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have := hC PUnit.unit
    rw [h0] at this
    simp at this
  | n + 1, col, C, hC, hcard => by
    classical
    by_cases hmiss : ∃ a : α, ∃ c ∈ C, ∀ x : LexT α n, col ⟨a, x⟩ ≠ c
    · obtain ⟨a, c, hc, hne⟩ := hmiss
      obtain ⟨f, hinj, hadj, hmono⟩ := lexPow_ramsey A n (fun x => col ⟨a, x⟩) (C.erase c)
        (fun x => Finset.mem_erase.mpr ⟨hne x, hC _⟩)
        (by rw [Finset.card_erase_of_mem hc]; omega)
      refine ⟨fun b => ⟨a, f b⟩, ?_, ?_, ?_⟩
      · intro b b' h
        have h2 : f b = f b' := by
          have := Sigma.mk.inj_iff.mp h
          exact eq_of_heq this.2
        exact hinj h2
      · intro b b'
        show (substGraph A (fun _ => lexPow A n)).Adj ⟨a, f b⟩ ⟨a, f b'⟩ ↔ A.Adj b b'
        rw [substGraph_adj_same]
        exact hadj b b'
      · intro b b'
        exact hmono b b'
    · push Not at hmiss
      by_cases hα : IsEmpty α
      · exact ⟨fun a => (hα.false a).elim, fun a => (hα.false a).elim,
          fun a => (hα.false a).elim, fun a => (hα.false a).elim⟩
      · rw [not_isEmpty_iff] at hα
        obtain ⟨x0⟩ := lexT_nonempty α n
        obtain ⟨a0⟩ := hα
        have hc0 : col ⟨a0, x0⟩ ∈ C := hC _
        have hpick : ∀ a : α, ∃ x : LexT α n, col ⟨a, x⟩ = col ⟨a0, x0⟩ := fun a =>
          hmiss a _ hc0
        choose g hg using hpick
        refine ⟨fun a => ⟨a, g a⟩, ?_, ?_, ?_⟩
        · intro a b h
          exact (Sigma.mk.inj_iff.mp h).1
        · intro a b
          show (substGraph A (fun _ => lexPow A n)).Adj ⟨a, g a⟩ ⟨b, g b⟩ ↔ A.Adj a b
          by_cases hab : a = b
          · subst hab
            constructor
            · intro h
              exact absurd h (SimpleGraph.irrefl _)
            · intro h
              exact absurd h A.irrefl
          · exact substGraph_adj_of_ne A _ hab _ _
        · intro a b
          rw [hg a, hg b]

#print axioms substGraph_adj_of_ne
#print axioms substGraph_adj_same
#print axioms lexPow_ramsey
end AllPathsLocal
