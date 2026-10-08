import RP5Structure
import EHP6.NSSL41

/-! Actual rooted cuts for Chapter III.1/III.5. Every child is a proper subset;
    the anticomponents are pairwise complete and the remainder is placed last. -/

namespace AllPathsLocal

structure RootCut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V) where
  C : Finset (Finset V)
  A : Finset V
  component : ∀ K ∈ C, EHP6.IsAnticomponent G (EHP6.nbrs G u S) K
  remainder : A = S \ EHP6.nbrs G u S
  cover : C.biUnion id ∪ A = S
  disjointC : ∀ K ∈ C, ∀ L ∈ C, K ≠ L → Disjoint K L
  disjointA : ∀ K ∈ C, Disjoint K A
  completeC : ∀ K ∈ C, ∀ L ∈ C, K ≠ L → EHP6.Complete G K L
  properC : ∀ K ∈ C, K ⊂ S
  properA : A ⊂ S
  nonemptyA : A.Nonempty

/-- Enumerate all true complement-components of the root's neighborhood. -/
theorem exists_root_cut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V)
    (hpos : 0 < (EHP6.nbrs G u S).card)
    (hnotfull : (EHP6.nbrs G u S).card < S.card) : Nonempty (RootCut G S u) := by
  classical
  let N := EHP6.nbrs G u S
  let C := N.powerset.filter (fun K => EHP6.IsAnticomponent G N K)
  let A := S \ N
  change 0 < N.card at hpos
  change N.card < S.card at hnotfull
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have hNproper : N ⊂ S := Finset.ssubset_iff_subset_ne.mpr
    ⟨hNS, fun h => by rw [h] at hnotfull; exact lt_irrefl _ hnotfull⟩
  have hc : ∀ K ∈ C, EHP6.IsAnticomponent G N K := by
    intro K hK
    exact (Finset.mem_filter.mp hK).2
  have hCcover : C.biUnion id = N := by
    apply Finset.Subset.antisymm
    · apply Finset.biUnion_subset.mpr
      intro K hK
      exact (hc K hK).1
    · intro v hv
      obtain ⟨K, hK, hvK, _⟩ := EHP6.exists_comp (G := Gᶜ) hv
      have hanti := EHP6.comp_to_anti (G := G) hK
      exact Finset.mem_biUnion.mpr ⟨K,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hK.1, hanti⟩, hvK⟩
  have hdisj : ∀ K ∈ C, ∀ L ∈ C, K ≠ L → Disjoint K L := by
    intro K hK L hL hKL
    apply Finset.disjoint_left.mpr
    intro v hvK hvL
    have hk := EHP6.isAnticomponent_iff_isComp_compl.mp (hc K hK)
    have hl := EHP6.isAnticomponent_iff_isComp_compl.mp (hc L hL)
    exact hKL (Finset.Subset.antisymm
      (EHP6.comp_unique hl hk hvL hvK) (EHP6.comp_unique hk hl hvK hvL))
  have hAnonempty : A.Nonempty := by
    have hh : 0 < A.card := by
      rw [Finset.card_sdiff_of_subset hNS]
      omega
    exact Finset.card_pos.mp hh
  have hAproper : A ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro heq
    obtain ⟨v, hvN⟩ := Finset.card_pos.mp hpos
    have hvA : v ∈ A := heq ▸ hNS hvN
    exact (Finset.mem_sdiff.mp hvA).2 hvN
  refine ⟨{
    C := C
    A := A
    component := hc
    remainder := rfl
    cover := ?_
    disjointC := hdisj
    disjointA := ?_
    completeC := ?_
    properC := ?_
    properA := hAproper
    nonemptyA := hAnonempty
  }⟩
  · rw [hCcover]
    exact Finset.union_sdiff_of_subset hNS
  · intro K hK
    apply Finset.disjoint_left.mpr
    intro v hvK hvA
    exact (Finset.mem_sdiff.mp hvA).2 ((hc K hK).1 hvK)
  · intro K hK L hL hKL p hp q hq
    have hqK : q ∉ K := fun hh => Finset.disjoint_left.mp (hdisj K hK L hL hKL) hh hq
    exact G.adj_symm ((hc K hK).2.2.2 q
      (Finset.mem_sdiff.mpr ⟨(hc L hL).1 hq, hqK⟩) p hp)
  · intro K hK
    exact Finset.ssubset_of_subset_of_ssubset (hc K hK).1 hNproper

theorem rootedP4Free_mono {V : Type} [DecidableEq V] (G : SimpleGraph V)
    {S T : Finset V} {u : V} (hST : S ⊆ T) (hfree : RootedP4Free G T u) :
    RootedP4Free G S u := by
  rintro ⟨p, hp, hp0, htail⟩
  exact hfree ⟨p, hp, hp0, fun i hi => hST (htail i hi)⟩

theorem complete_vertex_rootedP4Free {V : Type} [DecidableEq V]
    (G : SimpleGraph V) {S : Finset V} {u : V}
    (hcomp : ∀ v ∈ S, G.Adj u v) : RootedP4Free G S u := by
  rintro ⟨p, hp, hp0, htail⟩
  have he := (hp.2 (0 : Fin 4) (1 : Fin 4)).mpr (by decide)
  have hn := ((SimpleGraph.compl_adj G _ _).mp he).2
  rw [hp0] at hn
  exact hn (hcomp (p 1) (htail 1 (by decide)))

/-- C-before-A is the nontrivial one-sided root law, inherited by all descendant subsets. -/
theorem root_cut_later_remainder_rp4 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {Y S K Z : Finset V} {u v : V} (cut : RootCut G S u)
    (hSY : S ⊆ Y) (hu : u ∉ Y) (hfree : RootedP5Free G Y u)
    (hK : K ∈ cut.C) (hZ : Z ⊆ K) (hv : v ∈ cut.A) :
    RootedP4Free G Z v := by
  have hv' : v ∈ S \ EHP6.nbrs G u S := by rwa [cut.remainder] at hv
  have hvS := (Finset.mem_sdiff.mp hv').1
  have huv : ¬ G.Adj u v := by
    intro h
    exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_filter.mpr ⟨hvS, h⟩)
  have hKsub := (cut.component K hK).1
  have hNsub : EHP6.nbrs G u S ⊆ S := Finset.filter_subset _ _
  apply rp5_to_rp4 G hu (hSY hvS) (hZ.trans (hKsub.trans (hNsub.trans hSY))) hfree huv
  intro z hz
  exact (Finset.mem_filter.mp (hKsub (hZ hz))).2

/-- Two distinct C children are complete, so a later vertex cannot start a complement P4
    into any earlier descendant block. -/
theorem root_cut_distinct_components_rp4 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S K L Z : Finset V} {u v : V} (cut : RootCut G S u)
    (hK : K ∈ cut.C) (hL : L ∈ cut.C) (hKL : K ≠ L)
    (hZ : Z ⊆ K) (hv : v ∈ L) : RootedP4Free G Z v := by
  apply complete_vertex_rootedP4Free G
  intro z hz
  exact G.adj_symm (cut.completeC K hK L hL hKL z (hZ hz) v hv)

#print axioms exists_root_cut
#print axioms rootedP4Free_mono
#print axioms complete_vertex_rootedP4Free
#print axioms root_cut_later_remainder_rp4
#print axioms root_cut_distinct_components_rp4

end AllPathsLocal
