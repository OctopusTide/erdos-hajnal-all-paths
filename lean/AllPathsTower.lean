import AllPathsSubstEH

/-!
The fibre tower and multipartite homogenization (main paper, Part I,
"Backward construction and forward selection"). Fibres are indexed by their distance
`d` from the last fibre; fibre `d` is the lexicographic power `R(Q, towerExp d)`,
large enough for the colouring by one external bit and the adjacency vector on the
whole next fibre.
-/

namespace AllPathsLocal

open Finset

/-- Exponents of the tower: the last fibre needs two colours; each earlier fibre
    needs one bit and one adjacency vector on the following fibre. -/
noncomputable def towerExp (α : Type) [Fintype α] : ℕ → ℕ
  | 0 => 2
  | d + 1 => 2 * 2 ^ (Fintype.card (LexT α (towerExp α d)))

/-- Forward selection: copies of `Q` in every fibre up to `k`, with the external
    predicate constant on the copy in fibre `k`, and the relation `M` uniform
    between the copies in consecutive fibres. No uniformity of `M` is assumed. -/
theorem tower_homogenize {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Q : SimpleGraph α)
    (M : ∀ d, LexT α (towerExp α (d + 1)) → LexT α (towerExp α d) → Prop) :
    ∀ (k : ℕ) (ext : LexT α (towerExp α k) → Prop),
      ∃ e : ∀ d, α → LexT α (towerExp α d),
        (∀ d, d ≤ k → Function.Injective (e d) ∧
          ∀ a b, (lexPow Q (towerExp α d)).Adj (e d a) (e d b) ↔ Q.Adj a b) ∧
        (∀ a a', ext (e k a) ↔ ext (e k a')) ∧
        ∀ d, d < k → (∀ a a', M d (e (d + 1) a) (e d a')) ∨
          (∀ a a', ¬ M d (e (d + 1) a) (e d a')) := by
  classical
  intro k
  induction k with
  | zero =>
    intro ext
    obtain ⟨f, hinj, hadj, hmono⟩ := lexPow_ramsey Q (towerExp α 0)
      (fun x => decide (ext x)) (Finset.univ : Finset Bool) (fun _ => Finset.mem_univ _)
      (by simp [towerExp])
    have hdef : ∀ d, Nonempty (α → LexT α (towerExp α d)) := fun d =>
      ⟨fun _ => Classical.arbitrary _⟩
    refine ⟨fun d => if h : d = 0 then h ▸ f else Classical.choice (hdef d), ?_, ?_, ?_⟩
    · intro d hd
      have h0 : d = 0 := Nat.le_zero.mp hd
      subst h0
      simp only [dif_pos]
      exact ⟨hinj, hadj⟩
    · intro a a'
      simp only [dif_pos]
      have := hmono a a'
      simpa using this
    · intro d hd
      exact absurd hd (Nat.not_lt_zero d)
  | succ k ih =>
    intro ext
    obtain ⟨f, hinj, hadj, hmono⟩ := lexPow_ramsey Q (towerExp α (k + 1))
      (fun x => ((decide (ext x), fun y => decide (M k x y)) :
        Bool × (LexT α (towerExp α k) → Bool)))
      (Finset.univ) (fun _ => Finset.mem_univ _)
      (by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
          Fintype.card_bool]
        simp [towerExp])
    obtain ⟨a0⟩ := (inferInstance : Nonempty α)
    obtain ⟨e, hcopy, hext, hunif⟩ := ih (fun y => M k (f a0) y)
    have hvec : ∀ a a' y, M k (f a) y ↔ M k (f a') y := by
      intro a a' y
      have h := hmono a a'
      have h2 := congrFun (congrArg Prod.snd h) y
      simpa using h2
    have hbit : ∀ a a', ext (f a) ↔ ext (f a') := by
      intro a a'
      have h := congrArg Prod.fst (hmono a a')
      simpa using h
    refine ⟨fun d => if h : d = k + 1 then h ▸ f else e d, ?_, ?_, ?_⟩
    · intro d hd
      by_cases h : d = k + 1
      · subst h
        simp only [dif_pos]
        exact ⟨hinj, hadj⟩
      · simp only [dif_neg h]
        exact hcopy d (by omega)
    · intro a a'
      simp only [dif_pos]
      exact hbit a a'
    · intro d hd
      by_cases h : d = k
      · subst h
        have hne : d ≠ d + 1 := by omega
        simp only [dif_pos, dif_neg hne]
        by_cases hM : M d (f a0) (e d a0)
        · left
          intro a a'
          exact (hvec a a0 _).mpr ((hext a0 a').mp hM)
        · right
          intro a a' hcon
          exact hM ((hext a' a0).mp ((hvec a a0 _).mp hcon))
      · have h1 : d + 1 ≠ k + 1 := by omega
        have h2 : d ≠ k + 1 := by omega
        simp only [dif_neg h1, dif_neg h2]
        exact hunif d (by omega)

#print axioms tower_homogenize
end AllPathsLocal
