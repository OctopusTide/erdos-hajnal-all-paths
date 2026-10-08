import RP5ThinLayerPaper
import Mathlib.Data.Finset.Max

namespace AllPathsLocal

/-- Strong ordered property actually supplied by the negative root prefixes.
    H is the complement orientation in the intended application. -/
def OrderedP4EndpointFree {V : Type} [LT V] (H : SimpleGraph V) : Prop :=
  ∀ p : Fin 4 → V, IsInducedPath H p → ¬ (p 0 < p 1 ∧ p 0 < p 2 ∧ p 0 < p 3)

theorem ordered_p4_endpoint_obstruction {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (hfree : OrderedP4EndpointFree H)
    {u a b v : V} (hua : u < a) (hub : u < b) (huv : u < v)
    (huaEdge : H.Adj u a) (hab : H.Adj a b) (hbv : H.Adj b v)
    (hubNon : ¬ H.Adj u b) (huvNon : ¬ H.Adj u v) (havNon : ¬ H.Adj a v) : False := by
  have dua : u ≠ a := ne_of_lt hua
  have dub : u ≠ b := ne_of_lt hub
  have duv : u ≠ v := ne_of_lt huv
  have dab : a ≠ b := H.ne_of_adj hab
  have dbv : b ≠ v := H.ne_of_adj hbv
  have dav : a ≠ v := by intro he; subst v; exact huvNon huaEdge
  have hpath : IsInducedPath H ![u,a,b,v] := by
    constructor
    · intro i j he
      fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
    · intro i j
      have hau := H.adj_symm huaEdge
      have hba := H.adj_symm hab
      have hvb := H.adj_symm hbv
      have hbu : ¬ H.Adj b u := fun h => hubNon (H.adj_symm h)
      have hvu : ¬ H.Adj v u := fun h => huvNon (H.adj_symm h)
      have hva : ¬ H.Adj v a := fun h => havNon (H.adj_symm h)
      fin_cases i <;> fin_cases j <;>
        simp [huaEdge, hab, hbv, hau, hba, hvb, hubNon, huvNon, havNon, hbu, hvu, hva]
  exact hfree ![u,a,b,v] hpath ⟨hua, hub, huv⟩

#print axioms ordered_p4_endpoint_obstruction
end AllPathsLocal
