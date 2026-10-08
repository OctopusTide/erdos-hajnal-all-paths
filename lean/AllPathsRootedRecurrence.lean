import RP5Tooth

namespace AllPathsLocal

/-- Rooted complement path exclusion for q VERTICES. The explicit zero index
    also makes the definition meaningful when q=0. Original RP4/RP5 definitions
    are retained and proved equivalent at their respective indices below. -/
def RootedPathFree {V : Type} (G : SimpleGraph V) (q : ℕ)
    (Y : Finset V) (r : V) : Prop :=
  ¬ ∃ (p : Fin q → V) (i : Fin q), i.val = 0 ∧ IsInducedPath Gᶜ p ∧
    p i = r ∧ ∀ j, j ≠ i → p j ∈ Y

theorem rooted_path_free_four {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (Y : Finset V) (r : V) :
    RootedPathFree G 4 Y r ↔ RootedP4Free G Y r := by
  constructor
  · intro h ⟨p, hp, hpr, htail⟩
    exact h ⟨p, 0, rfl, hp, hpr, htail⟩
  · intro h ⟨p, i, hi, hp, hpr, htail⟩
    have he : i = 0 := Fin.ext hi
    subst i
    exact h ⟨p, hp, hpr, htail⟩

theorem rooted_path_free_five {V : Type} (G : SimpleGraph V) (Y : Finset V) (r : V) :
    RootedPathFree G 5 Y r ↔ RootedP5Free G Y r := by
  constructor
  · intro h ⟨p, hp, hpr, htail⟩
    exact h ⟨p, 0, rfl, hp, hpr, htail⟩
  · intro h ⟨p, i, hi, hp, hpr, htail⟩
    have he : i = 0 := Fin.ext hi
    subst i
    exact h ⟨p, hp, hpr, htail⟩

theorem rooted_path_free_mono {V : Type} (G : SimpleGraph V) (q : ℕ)
    {Y T : Finset V} {r : V} (hfree : RootedPathFree G q Y r) (hTY : T ⊆ Y) :
    RootedPathFree G q T r := by
  rintro ⟨p, i, hi, hp, hpr, htail⟩
  exact hfree ⟨p, i, hi, hp, hpr, fun j hj => hTY (htail j hj)⟩

/-- One-root prefix used in every RPq frontier and negative transversal.
    The ambient host and original target Y remain unchanged. -/
theorem rooted_path_free_prefix {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) {Y T : Finset V} {r z : V}
    (hr : r ∉ Y) (hz : z ∈ Y) (hTY : T ⊆ Y)
    (hfree : RootedPathFree G (n+2) Y r) (hrz : ¬ G.Adj r z)
    (hrT : ∀ t ∈ T, G.Adj r t) : RootedPathFree G (n+1) T z := by
  rintro ⟨p, i, hi, hp, hpz, htail⟩
  have he : i = 0 := Fin.ext hi
  subst i
  have hpY : ∀ j, p j ∈ Y := by
    intro j
    by_cases hj : j = 0
    · simpa only [hj, hpz] using hz
    · exact hTY (htail j hj)
  have hnew : ∀ j, r ≠ p j := fun j he => hr (he ▸ hpY j)
  have hhead : ∀ j, Gᶜ.Adj r (p j) ↔ j = 0 := by
    intro j
    by_cases hj : j = 0
    · have hrzNe : r ≠ z := fun he => hr (he ▸ hz)
      simp [SimpleGraph.compl_adj, hj, hpz, hrzNe, hrz]
    · simp [SimpleGraph.compl_adj, hj, hrT (p j) (htail j hj)]
  apply hfree
  refine ⟨Fin.cases r p, 0, rfl, prefix_inducedPath Gᶜ p r hp hnew hhead, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro hj
    exact False.elim (hj rfl)
  · intro _
    exact hpY k

/-- The offending-pair two-root prefix lowers RPq to RP(q-2).
    All vertices stay in the SAME original host and target, so the theorem
    introduces no change of ambient forbidden class. -/
theorem rooted_path_free_two_prefix {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) {Y T : Finset V} {r z a : V}
    (hr : r ∉ Y) (hz : z ∈ Y) (ha : a ∈ Y) (hTY : T ⊆ Y)
    (hzT : z ∉ T) (hza : z ≠ a)
    (hfree : RootedPathFree G (n+3) Y r)
    (hrz : ¬ G.Adj r z) (hzaNon : ¬ G.Adj z a) (hra : G.Adj r a)
    (hrFull : ∀ t ∈ T, G.Adj r t) (hzFull : ∀ t ∈ T, G.Adj z t) :
    RootedPathFree G (n+1) T a := by
  rintro ⟨p, i, hi, hp, hpa, htail⟩
  have he : i = 0 := Fin.ext hi
  subst i
  have hpY : ∀ j, p j ∈ Y := by
    intro j
    by_cases hj : j = 0
    · simpa only [hj, hpa] using ha
    · exact hTY (htail j hj)
  have hrNew : ∀ j, r ≠ p j := fun j he => hr (he ▸ hpY j)
  have hzNew : ∀ j, z ≠ p j := by
    intro j he
    by_cases hj : j = 0
    · exact hza (by simpa only [hj, hpa] using he)
    · exact hzT (he ▸ htail j hj)
  have hzHead : ∀ j, Gᶜ.Adj z (p j) ↔ j = 0 := by
    intro j
    by_cases hj : j = 0
    · simp [SimpleGraph.compl_adj, hj, hpa, hza, hzaNon]
    · simp [SimpleGraph.compl_adj, hj, hzFull (p j) (htail j hj)]
  have hrzNe : r ≠ z := fun he => hr (he ▸ hz)
  have hrzEdge : Gᶜ.Adj r z := (G.compl_adj r z).mpr ⟨hrzNe, hrz⟩
  have hrNoChord : ∀ j, ¬ Gᶜ.Adj r (p j) := by
    intro j h
    by_cases hj : j = 0
    · exact ((G.compl_adj r (p j)).mp h).2 (by simpa only [hj, hpa] using hra)
    · exact ((G.compl_adj r (p j)).mp h).2 (hrFull (p j) (htail j hj))
  apply hfree
  refine ⟨Fin.cases r (Fin.cases z p), 0, rfl,
    prefix_two_inducedPath Gᶜ p r z hp hzNew hzHead hrzNe hrNew hrzEdge hrNoChord, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro hj
    exact False.elim (hj rfl)
  · intro _
    exact Fin.cases hz hpY k

#print axioms rooted_path_free_four
#print axioms rooted_path_free_five
#print axioms rooted_path_free_mono
#print axioms rooted_path_free_prefix
#print axioms rooted_path_free_two_prefix
end AllPathsLocal
