import AllPathsLexPower

/-!
Substitution preserves a positive Erdős–Hajnal exponent (main paper, Part I,
"positive substitution exponents"), by iterating the module-replacement theorem
once for every vertex of the base graph. Lexicographic powers follow.
-/

namespace AllPathsLocal

open Finset

instance lexT_fintype (α : Type) [Fintype α] : ∀ n, Fintype (LexT α n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    haveI := lexT_fintype α n
    exact inferInstanceAs (Fintype (Σ _ : α, LexT α n))

instance lexT_decEq (α : Type) [DecidableEq α] : ∀ n, DecidableEq (LexT α n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n + 1 => by
    haveI := lexT_decEq α n
    exact inferInstanceAs (DecidableEq (Σ _ : α, LexT α n))

instance lexT_nonempty_inst (α : Type) [Nonempty α] (n : ℕ) : Nonempty (LexT α n) :=
  lexT_nonempty α n

theorem substGraph_adj_of_fst {α : Type} {β : α → Type} (A : SimpleGraph α)
    (B : ∀ a, SimpleGraph (β a)) (p q : Σ a, β a) (h : p.1 = q.1 → p = q) :
    (substGraph A B).Adj p q ↔ A.Adj p.1 q.1 := by
  by_cases hpq : p.1 = q.1
  · have e := h hpq
    subst e
    constructor
    · intro hh
      exact absurd hh (SimpleGraph.irrefl _)
    · intro hh
      exact absurd hh A.irrefl
  · obtain ⟨a, x⟩ := p
    obtain ⟨b, y⟩ := q
    exact substGraph_adj_of_ne A B hpq x y

/-- Substitution into every vertex preserves a positive EH exponent. -/
theorem ehOn_substGraph {α : Type} [Fintype α] [DecidableEq α] {β : α → Type}
    [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
    (A : SimpleGraph α) (B : ∀ a, SimpleGraph (β a))
    (hA : ∃ γ : ℝ, 0 < γ ∧ EHOn A Finset.univ γ)
    (hB : ∀ a, ∃ δ : ℝ, 0 < δ ∧ EHOn (B a) Finset.univ δ) :
    ∃ κ : ℝ, 0 < κ ∧ EHOn (substGraph A B) Finset.univ κ := by
  classical
  obtain ⟨γ, hγ, hAγ⟩ := hA
  choose δ hδ hBδ using hB
  let base : ∀ a, β a := fun a => Classical.arbitrary (β a)
  let X : Finset α → Finset (Σ a, β a) := fun T =>
    Finset.univ.filter (fun p => p.1 ∈ T ∨ p.2 = base p.1)
  have hXmem : ∀ T p, p ∈ X T ↔ (p.1 ∈ T ∨ p.2 = base p.1) := by
    intro T p
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
  have key : ∀ T : Finset α, ∃ κ : ℝ, 0 < κ ∧ EHOn (substGraph A B) (X T) κ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨γ, hγ, ?_⟩
      intro V _ G S hno
      apply hAγ V G S
      rintro ⟨f, hinj, hmem, hadj⟩
      apply hno
      have hbase : ∀ p ∈ X ∅, p.2 = base p.1 := by
        intro p hp
        rcases (hXmem ∅ p).mp hp with h | h
        · exact absurd h (Finset.notMem_empty _)
        · exact h
      have hext : ∀ p ∈ X ∅, ∀ q ∈ X ∅, p.1 = q.1 → p = q := by
        intro p hp q hq h
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := q
        have hx := hbase _ hp
        have hy := hbase _ hq
        dsimp only at h hx hy
        subst h
        rw [hx, hy]
      refine ⟨fun p => f p.1, ?_, ?_, ?_⟩
      · intro p hp q hq h
        exact hext p hp q hq (hinj (Finset.mem_coe.mpr (Finset.mem_univ _))
          (Finset.mem_coe.mpr (Finset.mem_univ _)) h)
      · intro p _
        exact hmem p.1 (Finset.mem_univ _)
      · intro p hp q hq
        rw [hadj p.1 (Finset.mem_univ _) q.1 (Finset.mem_univ _)]
        exact (substGraph_adj_of_fst A B p q (hext p hp q hq)).symm
    | insert u T huT ih =>
      obtain ⟨κT, hκT, hXT⟩ := ih
      let u0 : Σ a, β a := ⟨u, base u⟩
      let M : Finset (Σ a, β a) := Finset.univ.filter (fun p => p.1 = u)
      have hMmem : ∀ p, p ∈ M ↔ p.1 = u := by
        intro p
        simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
      have hu0 : u0 ∈ X T := (hXmem T u0).mpr (Or.inr rfl)
      have hne : ∀ p ∈ (X T).erase u0, p.1 ≠ u := by
        intro p hp hpu
        obtain ⟨hpne, hpX⟩ := Finset.mem_erase.mp hp
        rcases (hXmem T p).mp hpX with h | h
        · exact huT (hpu ▸ h)
        · apply hpne
          obtain ⟨a, x⟩ := p
          dsimp only at hpu h
          subst hpu
          rw [h]
      have hXeq : X (insert u T) = (X T).erase u0 ∪ M := by
        ext p
        rw [hXmem, Finset.mem_union, Finset.mem_erase, hXmem, hMmem, Finset.mem_insert]
        by_cases hpu : p.1 = u
        · simp [hpu]
        · have hpne : p ≠ u0 := fun e => hpu (by rw [e])
          simp [hpu, hpne]
      have hmod : ∀ p ∈ (X T).erase u0, ∀ m ∈ M,
          ((substGraph A B).Adj p m ↔ (substGraph A B).Adj p u0) := by
        intro p hp m hm
        have hpu := hne p hp
        have hmu := (hMmem m).mp hm
        obtain ⟨a, x⟩ := p
        obtain ⟨b, y⟩ := m
        dsimp only at hpu hmu
        subst hmu
        rw [substGraph_adj_of_ne A B hpu x y, substGraph_adj_of_ne A B hpu x (base b)]
      have hMEH : EHOn (substGraph A B) M (δ u) := by
        intro V _ G S hno
        apply hBδ u V G S
        rintro ⟨f, hinj, hmem, hadj⟩
        apply hno
        refine ⟨fun p => if h : p.1 = u then f (h ▸ p.2) else f (base u), ?_, ?_, ?_⟩
        · intro p hp q hq hpq
          have hpu := (hMmem p).mp hp
          have hqu := (hMmem q).mp hq
          obtain ⟨a, x⟩ := p
          obtain ⟨b, y⟩ := q
          dsimp only at hpu hqu
          subst hpu
          subst hqu
          simp only [dif_pos] at hpq
          have := hinj (Finset.mem_coe.mpr (Finset.mem_univ x))
            (Finset.mem_coe.mpr (Finset.mem_univ y)) hpq
          rw [this]
        · intro p hp
          have hpu := (hMmem p).mp hp
          obtain ⟨a, x⟩ := p
          dsimp only at hpu
          subst hpu
          simp only [dif_pos]
          exact hmem x (Finset.mem_univ _)
        · intro p hp q hq
          have hpu := (hMmem p).mp hp
          have hqu := (hMmem q).mp hq
          obtain ⟨a, x⟩ := p
          obtain ⟨b, y⟩ := q
          dsimp only at hpu hqu
          subst hpu
          subst hqu
          simp only [dif_pos]
          rw [hadj x (Finset.mem_univ _) y (Finset.mem_univ _), substGraph_adj_same]
      have hrep := ehOn_module_replace (substGraph A B) (X T) M u0 hu0 hmod κT (δ u) hκT (hδ u)
        hXT hMEH
      have hden : 0 < ((X T).card : ℝ) + 1 + (X T).card / κT + 1 / δ u := by
        have h1 : (0 : ℝ) ≤ ((X T).card : ℝ) / κT :=
          div_nonneg (Nat.cast_nonneg _) hκT.le
        have h2 : (0 : ℝ) < 1 / δ u := one_div_pos.mpr (hδ u)
        have h3 : (0 : ℝ) ≤ ((X T).card : ℝ) := Nat.cast_nonneg _
        linarith
      refine ⟨1 / (((X T).card : ℝ) + 1 + (X T).card / κT + 1 / δ u), one_div_pos.mpr hden, ?_⟩
      rw [hXeq]
      exact hrep
  obtain ⟨κ, hκ, h⟩ := key Finset.univ
  refine ⟨κ, hκ, ?_⟩
  have hX : X Finset.univ = Finset.univ := by
    ext p
    rw [hXmem]
    simp
  rw [hX] at h
  exact h

/-- Lexicographic powers of a graph with a positive EH exponent have one. -/
theorem ehOn_lexPow {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : SimpleGraph α) (hA : ∃ γ : ℝ, 0 < γ ∧ EHOn A Finset.univ γ) :
    ∀ n, ∃ κ : ℝ, 0 < κ ∧ EHOn (lexPow A n) Finset.univ κ
  | 0 => by
    refine ⟨1, one_pos, ?_⟩
    intro V _ G S hno
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, Finset.Subset.refl _, Or.inr (by simp), by simp⟩
    · exfalso
      apply hno
      refine ⟨fun _ => v, ?_, fun _ _ => hv, ?_⟩
      · intro a _ b _ _
        exact Subsingleton.elim (α := PUnit) a b
      · intro a _ b _
        constructor
        · intro h
          exact absurd h G.irrefl
        · intro h
          exact absurd h (SimpleGraph.irrefl _)
  | n + 1 => by
    have ih := ehOn_lexPow A hA n
    exact ehOn_substGraph A (fun _ => lexPow A n) hA (fun _ => ih)

#print axioms ehOn_substGraph
#print axioms ehOn_lexPow
end AllPathsLocal
