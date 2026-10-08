import RP5LayerInterfaces

namespace AllPathsLocal

def CyclicConsecutive (n : ℕ) (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i.val = 0 ∧ j.val + 1 = n) ∨ (j.val = 0 ∧ i.val + 1 = n)

def IsInducedCycle {V : Type} (G : SimpleGraph V) {n : ℕ} (p : Fin n → V) : Prop :=
  Function.Injective p ∧ ∀ i j, G.Adj (p i) (p j) ↔ CyclicConsecutive n i j

theorem cycle_first_four_induced_path {V : Type} (G : SimpleGraph V) {n : ℕ}
    (hn : 5 ≤ n) (p : Fin n → V) (hp : IsInducedCycle G p) :
    IsInducedPath G (fun i : Fin 4 => p (Fin.castLE (show 4 ≤ n by omega) i)) := by
  constructor
  · exact hp.1.comp (Fin.castLE_injective _)
  · intro i j
    rw [hp.2]
    simp only [CyclicConsecutive, Fin.val_castLE]
    have hi := i.isLt
    have hj := j.isLt
    omega

def cycleComplementIndices {n : ℕ} (hn : 5 ≤ n) : Fin 4 → Fin n :=
  ![⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n - 1, by omega⟩, ⟨1, by omega⟩]

theorem cycle_complement_induced_path {V : Type} (G : SimpleGraph V) {n : ℕ}
    (hn : 5 ≤ n) (p : Fin n → V) (hp : IsInducedCycle G p) :
    IsInducedPath Gᶜ (fun i => p (cycleComplementIndices hn i)) := by
  have he : Function.Injective (cycleComplementIndices hn) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [cycleComplementIndices, Fin.ext_iff] at hij ⊢ <;> omega
  constructor
  · exact hp.1.comp he
  · intro i j
    have heq : p (cycleComplementIndices hn i) = p (cycleComplementIndices hn j) ↔ i = j := by
      constructor
      · intro h
        exact he (hp.1 h)
      · intro h
        subst j
        rfl
    simp only [SimpleGraph.compl_adj, ne_eq, heq, hp.2]
    fin_cases i <;> fin_cases j <;>
      simp [cycleComplementIndices, CyclicConsecutive, Fin.ext_iff] <;> omega

theorem rooted_p4_excludes_complement_hole {V : Type} [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (hn : 5 ≤ n) (p : Fin n → V) (S : Finset V)
    (hfree : RootedP4Free G S (p ⟨0, by omega⟩))
    (hrest : ∀ i : Fin n, i.val ≠ 0 → p i ∈ S) : ¬ IsInducedCycle Gᶜ p := by
  intro hp
  let e : Fin 4 → Fin n := Fin.castLE (show 4 ≤ n by omega)
  refine hfree ⟨fun i => p (e i), cycle_first_four_induced_path Gᶜ hn p hp, rfl, ?_⟩
  intro i hi
  apply hrest
  intro hz
  apply hi
  apply Fin.ext
  exact hz

theorem rooted_p4_excludes_hole {V : Type} [DecidableEq V]
    (G : SimpleGraph V) {n : ℕ} (hn : 5 ≤ n) (p : Fin n → V) (S : Finset V)
    (hfree : RootedP4Free G S (p ⟨0, by omega⟩))
    (hrest : ∀ i : Fin n, i.val ≠ 0 → p i ∈ S) : ¬ IsInducedCycle G p := by
  intro hp
  refine hfree ⟨fun i => p (cycleComplementIndices hn i),
    cycle_complement_induced_path G hn p hp, rfl, ?_⟩
  intro i hi
  apply hrest
  fin_cases i <;> simp [cycleComplementIndices, Fin.ext_iff] at hi ⊢ <;> omega

#print axioms cycle_first_four_induced_path
#print axioms cycle_complement_induced_path
#print axioms rooted_p4_excludes_complement_hole
#print axioms rooted_p4_excludes_hole

end AllPathsLocal
