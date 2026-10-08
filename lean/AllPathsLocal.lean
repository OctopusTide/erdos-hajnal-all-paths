import EHP6.Tooth

/-!
Local dependency audit for All_paths_EH_English_proof(1).txt.
This formalizes induced-path prefixing (Part II, Sections 3 and 4).
It does NOT claim the Tooth recurrence, wonderfulness, or EH for all paths.
No new axiom or unfinished proof is used.
-/

namespace AllPathsLocal

def IsInducedPath {V : Type} (G : SimpleGraph V) {n : ℕ}
    (p : Fin n → V) : Prop :=
  Function.Injective p ∧
    ∀ i j, G.Adj (p i) (p j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val

theorem isInducedPath_iff_embedding {V : Type} (G : SimpleGraph V) {n : ℕ}
    (p : Fin n → V) :
    IsInducedPath G p ↔
      Function.Injective p ∧
        ∀ i j, G.Adj (p i) (p j) ↔ (EHP6.pathGraph' n).Adj i j := by
  simp only [IsInducedPath, EHP6.pathGraph', SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hinj, h⟩
    refine ⟨hinj, fun i j => ?_⟩
    rw [h]
    constructor
    · intro e
      refine ⟨?_, e⟩
      intro heq
      subst heq
      omega
    · exact fun e => e.2
  · rintro ⟨hinj, h⟩
    refine ⟨hinj, fun i j => ?_⟩
    rw [h]
    constructor
    · exact fun e => e.2
    · intro e
      refine ⟨?_, e⟩
      intro heq
      subst heq
      omega

theorem prefix_inducedPath {V : Type} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 1) → V) (root : V)
    (hp : IsInducedPath G p)
    (hnew : ∀ i, root ≠ p i)
    (hroot : ∀ i, G.Adj root (p i) ↔ i = 0) :
    IsInducedPath G (Fin.cases root p) := by
  constructor
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _
        rfl
      · intro hij
        exact False.elim (hnew b hij)
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact False.elim (hnew a hij.symm)
      · intro hij
        exact congrArg Fin.succ (hp.1 hij)
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · simp
      · simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ, hroot]
        have hb := b.isLt
        simp only [Fin.ext_iff, Fin.val_zero]
        omega
    · refine Fin.cases ?_ (fun b => ?_) j
      · simp only [Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
        rw [G.adj_comm, hroot]
        simp only [Fin.ext_iff, Fin.val_zero]
        omega
      · simp only [Fin.cases_succ, Fin.val_succ, hp.2]
        omega

theorem prefix_two_inducedPath {V : Type} (G : SimpleGraph V) {n : ℕ}
    (p : Fin (n + 1) → V) (r z : V)
    (hp : IsInducedPath G p)
    (hznew : ∀ i, z ≠ p i)
    (hz : ∀ i, G.Adj z (p i) ↔ i = 0)
    (hrz : r ≠ z) (hrnew : ∀ i, r ≠ p i)
    (hedge : G.Adj r z) (hnochord : ∀ i, ¬ G.Adj r (p i)) :
    IsInducedPath G (Fin.cases r (Fin.cases z p)) := by
  apply prefix_inducedPath G (Fin.cases z p) r
    (prefix_inducedPath G p z hp hznew hz)
  · intro i
    exact Fin.cases hrz hrnew i
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hedge]
    · simp [hnochord]

#print axioms isInducedPath_iff_embedding
#print axioms prefix_inducedPath
#print axioms prefix_two_inducedPath

def RootedP4Free {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (Y : Finset V) (u : V) : Prop :=
  ¬ ∃ p : Fin 4 → V, IsInducedPath Gᶜ p ∧ p 0 = u ∧
    ∀ i, i ≠ 0 → p i ∈ Y

/- The ambient-independent RP4 premise used before the RP5 Tooth theorem
   in P7_from_P6_English_proof.txt, lines 167--175. -/
theorem rooted_p4_module_law {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y K : Finset V} {u : V}
    (huY : u ∉ Y) (hfree : RootedP4Free G Y u)
    (hK : EHP6.IsAnticomponent G (EHP6.nbrs G u Y) K) :
    EHP6.IsModule G Y K := by
  classical
  open Finset in
  obtain ⟨hKsub, _, hKanti, hKc⟩ := hK
  have hKmem : ∀ k ∈ K, k ∈ Y ∧ G.Adj u k := by
    intro k hk
    exact Finset.mem_filter.mp (hKsub hk)
  refine ⟨fun k hk => (hKmem k hk).1, fun y hy => ?_⟩
  obtain ⟨hyY, hyK⟩ := Finset.mem_sdiff.mp hy
  by_cases hyu : G.Adj u y
  · exact Or.inl (hKc y (Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨hyY, hyu⟩, hyK⟩))
  by_cases hall : ∀ k ∈ K, G.Adj y k
  · exact Or.inl hall
  by_cases hnone : ∀ k ∈ K, ¬ G.Adj y k
  · exact Or.inr hnone
  exfalso
  push Not at hall hnone
  obtain ⟨p₀, hp₀K, hp₀⟩ := hnone
  obtain ⟨q₀, hq₀K, hq₀⟩ := hall
  obtain ⟨w, hwP, z, hzP, hwz⟩ := hKanti (K.filter (G.Adj y))
    (Finset.filter_subset _ _)
    ⟨p₀, Finset.mem_filter.mpr ⟨hp₀K, hp₀⟩⟩
    ⟨q₀, Finset.mem_sdiff.mpr
      ⟨hq₀K, fun h => hq₀ (Finset.mem_filter.mp h).2⟩⟩
  obtain ⟨hwK, hyw⟩ := Finset.mem_filter.mp hwP
  obtain ⟨hzK, hzy⟩ := Finset.mem_sdiff.mp hzP
  have hyz : ¬ G.Adj y z := fun h => hzy (Finset.mem_filter.mpr ⟨hzK, h⟩)
  have huz := (hKmem z hzK).2
  have huw := (hKmem w hwK).2
  have duy : u ≠ y := fun h => huY (h ▸ hyY)
  have duz := G.ne_of_adj huz
  have duw := G.ne_of_adj huw
  have dyz : y ≠ z := fun h => hyK (h ▸ hzK)
  have dyw := G.ne_of_adj hyw
  have dzw : z ≠ w := by intro h; subst z; exact hyz hyw
  apply hfree
  refine ⟨![u, y, z, w], ?_, rfl, ?_⟩
  · constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [Ne.symm]
    · intro i j
      have huy' : ¬ G.Adj y u := fun h => hyu (G.adj_symm h)
      have hyz' : ¬ G.Adj z y := fun h => hyz (G.adj_symm h)
      have hwz' : ¬ G.Adj z w := fun h => hwz (G.adj_symm h)
      have hzu := G.adj_symm huz
      have hwu := G.adj_symm huw
      have hwy := G.adj_symm hyw
      fin_cases i <;> fin_cases j <;>
        simp [SimpleGraph.compl_adj, duy, duz, duw, dyz, dyw, dzw,
          Ne.symm duy, Ne.symm duz, Ne.symm duw, Ne.symm dyz,
          Ne.symm dyw, Ne.symm dzw, hyu, hyz, hwz, huy', hyz', hwz',
          huz, huw, hyw, hzu, hwu, hwy]
  · intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · exact hyY
    · exact (hKmem z hzK).1
    · exact (hKmem w hwK).1

#print axioms rooted_p4_module_law

/- The full five-outcome RP4 Tooth contract needed by the all-path
   research, obtained from the newly proved root-to-module interface and
   the original, ambient-independent, kernel-checked Tooth theorem. -/
theorem rp4_tooth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hx20 : x ≤ 1 / 2 ^ 20)
    (hk : 2 ^ 16 ≤ k) (hkx : (k : ℝ) ≤ 2 / Real.sqrt x)
    (Y U : Finset V) (hn : 16 / x ^ 3 ≤ (Y.card : ℝ))
    (houtside : ∀ u ∈ U, u ∉ Y)
    (hroots : ∀ u ∈ U, RootedP4Free G Y u) :
    (∃ K : ℕ, (k : ℝ) ≤ (K : ℝ) ^ 4 ∧ (K : ℝ) ≤ 1 / x ∧
        ∃ β : EHP6.Blockade Y K (Y.card / (K : ℝ) ^ 4), β.IsPure G) ∨
    (∃ L : ℕ, (k : ℝ) ^ 3 ≤ (9 * (L : ℝ)) ^ 4 ∧ (8 * (L : ℝ)) ^ 4 ≤ (k : ℝ) ^ 3 ∧
        ∃ β : EHP6.Blockade Y L (Y.card / (2 * k)), β.IsPure G) ∨
    (∃ β : EHP6.Blockade Y ⌊1 / x⌋₊ (x ^ 2 * Y.card / k),
        β.IsComplete G ∨ β.IsAnticomplete G) ∨
    (∃ β : EHP6.Blockade Y ⌊1 / (x * k)⌋₊ (x ^ 3 * Y.card / 4), β.IsComplete G) ∨
    (∃ Y' ⊆ Y, (Y.card : ℝ) / k ≤ Y'.card ∧
        ∀ u ∈ U, (∀ y ∈ Y', G.Adj u y) ∨
          ((EHP6.nbrs G u Y').card : ℝ) < x * Y'.card / 4) := by
  apply EHP6.tooth_lemma hx hx20 hk hkx Y U hn
  intro u hu K hK
  exact rooted_p4_module_law G (houtside u hu) (hroots u hu) hK

#check @prefix_inducedPath
#check @prefix_two_inducedPath
#check @rooted_p4_module_law
#check @rp4_tooth
#print axioms rp4_tooth

end AllPathsLocal
