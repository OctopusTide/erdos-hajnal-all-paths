import RP5OrderedCertificate

namespace AllPathsLocal

/-- A finite ordered endpoint-free graph has an actual optimal colouring
    and an equally large clique, including the empty graph. -/
theorem ordered_clique_color_certificate {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hfree : OrderedP4EndpointFree H) :
    Nonempty (CliqueColorCertificate H) := by
  classical
  obtain ⟨C⟩ := ordered_finset_certificate H hfree Finset.univ
  exact ⟨{ k := C.k
           color := fun v => ⟨C.color v, C.bound v (Finset.mem_univ v)⟩
           proper := fun u v huv he => C.proper u (Finset.mem_univ u) v
             (Finset.mem_univ v) huv (congrArg Fin.val he)
           clique := C.clique
           clique_card := C.card
           clique_adj := C.adjacent }⟩

/-- At most one vertex from each ordered layer transports the actual order
    to the transversal. Rooted complement-P4 exclusion supplies the ordered
    obstruction, and thus constructs the complement certificate. -/
theorem ordered_layer_transversal_certificate {V : Type} [DecidableEq V]
    (G : SimpleGraph V) {l : ℕ} (L : Fin l → Finset V) (T : Finset V)
    (hcover : ∀ v ∈ T, ∃ i, v ∈ L i)
    (hthin : ∀ i, (T ∩ L i).card ≤ 1)
    (hroot : ∀ i, ∀ v ∈ L i,
      RootedP4Free G ((Finset.univ.filter (fun j => i < j)).biUnion L) v) :
    Nonempty (CliqueColorCertificate (Gᶜ.induce (T : Set V))) := by
  classical
  choose index hindex using (fun v : ↥(T : Set V) => hcover v.val v.property)
  have hinj : Function.Injective index := by
    intro u v he
    apply Subtype.ext
    exact Finset.card_le_one.mp (hthin (index u)) u.val
      (Finset.mem_inter.mpr ⟨u.property, hindex u⟩) v.val
      (Finset.mem_inter.mpr ⟨v.property, he ▸ hindex v⟩)
  letI : LinearOrder ↥(T : Set V) := LinearOrder.lift' index hinj
  apply ordered_clique_color_certificate
  intro p hp hlt
  let q : Fin 4 → V := fun j => (p j).val
  have hq : IsInducedPath Gᶜ q :=
    ⟨fun i j he => hp.1 (Subtype.ext he), hp.2⟩
  apply hroot (index (p 0)) (p 0).val (hindex (p 0))
  refine ⟨q, hq, rfl, ?_⟩
  intro j hj
  have hltj : index (p 0) < index (p j) := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact hlt.1
    · exact hlt.2.1
    · exact hlt.2.2
  exact Finset.mem_biUnion.mpr ⟨index (p j),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hltj⟩, hindex (p j)⟩

#print axioms ordered_clique_color_certificate
#print axioms ordered_layer_transversal_certificate
end AllPathsLocal
