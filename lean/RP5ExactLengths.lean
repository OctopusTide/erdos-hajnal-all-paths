import RP5PaperFrontier

namespace AllPathsLocal

/-- The source Blockade length is a lower bound. Explicit truncation makes k the
    actual integer length, which is essential for the upper length bound in III.4. -/
def exactLengthBlockade {V : Type} [DecidableEq V] {Y : Finset V} {k : ℕ} {w : ℝ}
    (β : EHP6.Blockade Y k w) : EHP6.Blockade Y k w :=
  let hkm : k ≤ β.m := by exact_mod_cast β.len
  let e : Fin k → Fin β.m := Fin.castLE hkm
  ⟨k, fun i => β.B (e i), le_rfl, fun i => β.sub (e i), fun i => β.wid (e i),
    fun i j hij => β.disj (e i) (e j) (fun h => hij (Fin.castLE_injective hkm h))⟩

theorem exactLengthBlockade_length {V : Type} [DecidableEq V]
    {Y : Finset V} {k : ℕ} {w : ℝ} (β : EHP6.Blockade Y k w) :
    (exactLengthBlockade β).m = k := rfl

theorem exactLengthBlockade_pure {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y : Finset V} {k : ℕ} {w : ℝ}
    (β : EHP6.Blockade Y k w) (hp : β.IsPure G) : (exactLengthBlockade β).IsPure G := by
  intro i j hij
  exact hp _ _ (fun h => hij (Fin.castLE_injective _ h))

theorem exactLengthBlockade_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y : Finset V} {k : ℕ} {w : ℝ}
    (β : EHP6.Blockade Y k w) (hp : β.IsComplete G) : (exactLengthBlockade β).IsComplete G := by
  intro i j hij
  exact hp _ _ (fun h => hij (Fin.castLE_injective _ h))

theorem exactLengthBlockade_anticomplete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y : Finset V} {k : ℕ} {w : ℝ}
    (β : EHP6.Blockade Y k w) (hp : β.IsAnticomplete G) : (exactLengthBlockade β).IsAnticomplete G := by
  intro i j hij
  exact hp _ _ (fun h => hij (Fin.castLE_injective _ h))

theorem exactLengthBlockade_directed {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Y : Finset V} {k : ℕ} {w ε : ℝ}
    (β : EHP6.Blockade Y k w)
    (hp : ∀ i j, i < j → EHP6.Complete G (β.B i) (β.B j) ∨ EHP6.SparseTo G ε (β.B j) (β.B i)) :
    ∀ i j, i < j → EHP6.Complete G ((exactLengthBlockade β).B i) ((exactLengthBlockade β).B j) ∨
      EHP6.SparseTo G ε ((exactLengthBlockade β).B j) ((exactLengthBlockade β).B i) := by
  intro i j hij
  exact hp _ _ hij

#print axioms exactLengthBlockade_length
#print axioms exactLengthBlockade_pure
#print axioms exactLengthBlockade_complete
#print axioms exactLengthBlockade_anticomplete
#print axioms exactLengthBlockade_directed

end AllPathsLocal
