import RP5ThinCountContradiction

namespace AllPathsLocal

theorem filter_card_classical {V : Type} (p : V → Prop) (s : Finset V)
    (d : DecidablePred p) :
    (@Finset.filter V p d s).card =
      (@Finset.filter V p (fun x => Classical.propDecidable (p x)) s).card := by
  have he : d = (fun x => Classical.propDecidable (p x)) := Subsingleton.elim _ _
  rw [he]

#print axioms filter_card_classical
end AllPathsLocal
