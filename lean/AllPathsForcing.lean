import AllPathsLift

/-!
Arm growth (main paper, Part I, "The forcing template"). If every lift of `Q`
contains an induced path on `s` vertices or an `(n+1)`-arm, then every lift of the
tower `P_h[R(Q, c_d) : d]` contains an induced path on `s` vertices or an
`(n+2)`-arm, provided `n + 2 ≤ h` and `s ≤ h + 1`.
-/

namespace AllPathsLocal

open Finset

/-- Vertices of the tower template over `P_h`. -/
abbrev TowerV (α : Type) [Fintype α] (h : ℕ) : Type :=
  Σ d : Fin h, LexT α (towerExp α d.val)

/-- The tower template `P_h[R(Q, towerExp d) : d < h]`. -/
noncomputable def towerGraph {α : Type} [Fintype α] (Q : SimpleGraph α) (h : ℕ) :
    SimpleGraph (TowerV α h) :=
  substGraph (EHP6.pathGraph' h) (fun d => lexPow Q (towerExp α d.val))

/-- The vertex `x` of fibre `d`. -/
def towerMk {α : Type} [Fintype α] {h : ℕ} (d : ℕ) (hd : d < h)
    (x : LexT α (towerExp α d)) : TowerV α h := ⟨⟨d, hd⟩, x⟩

theorem towerMk_fibre {α : Type} [Fintype α] {h : ℕ} {d d' : ℕ} {hd : d < h} {hd' : d' < h}
    {x : LexT α (towerExp α d)} {y : LexT α (towerExp α d')}
    (he : (towerMk d hd x : TowerV α h) = towerMk d' hd' y) : d = d' := by
  have h1 := congrArg (fun p : TowerV α h => p.1.val) he
  exact h1

theorem towerGraph_adj_ne {α : Type} [Fintype α] (Q : SimpleGraph α) {h : ℕ} {d d' : ℕ}
    (hd : d < h) (hd' : d' < h) (hne : d ≠ d')
    (x : LexT α (towerExp α d)) (y : LexT α (towerExp α d')) :
    (towerGraph Q h).Adj (towerMk d hd x) (towerMk d' hd' y) ↔ (d + 1 = d' ∨ d' + 1 = d) := by
  have hne' : (⟨d, hd⟩ : Fin h) ≠ ⟨d', hd'⟩ := fun e => hne (Fin.mk.inj_iff.mp e)
  unfold towerGraph towerMk
  rw [substGraph_adj_of_ne _ _ hne']
  simp only [EHP6.pathGraph', SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨hne', h⟩

theorem towerGraph_adj_same {α : Type} [Fintype α] (Q : SimpleGraph α) {h : ℕ} {d : ℕ}
    (hd : d < h) (x y : LexT α (towerExp α d)) :
    (towerGraph Q h).Adj (towerMk d hd x) (towerMk d hd y) ↔
      (lexPow Q (towerExp α d)).Adj x y := by
  unfold towerGraph towerMk
  exact substGraph_adj_same (EHP6.pathGraph' h)
    (fun d : Fin h => lexPow Q (towerExp α d.val)) ⟨d, hd⟩ x y

theorem towerMk_congr {α : Type} [Fintype α] {h : ℕ} {d d' : ℕ} (hdd : d = d')
    (hd : d < h) (hd' : d' < h) (f : ∀ d, LexT α (towerExp α d)) :
    (towerMk d hd (f d) : TowerV α h) = towerMk d' hd' (f d') := by
  subst hdd
  rfl

set_option maxHeartbeats 1600000 in
/-- **Arm growth.** -/
theorem forcing_step {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Q : SimpleGraph α) (s n h : ℕ) (hnh : n + 2 ≤ h) (hsh : s ≤ h + 1)
    (hQ : ∀ (V : Type) (F : SimpleGraph V) (L : Lift F Q),
      (∃ p : Fin s → V, IsInducedPath F p) ∨ L.HasArm n) :
    ∀ (V : Type) (F : SimpleGraph V) (L : Lift F (towerGraph Q h)),
      (∃ p : Fin s → V, IsInducedPath F p) ∨ L.HasArm (n + 1) := by
  classical
  intro V F L
  by_cases hpath : ∃ p : Fin s → V, IsInducedPath F p
  · exact Or.inl hpath
  right
  obtain ⟨a0⟩ := (inferInstance : Nonempty α)
  -- the b-b relation between consecutive fibres
  let M : ∀ d, LexT α (towerExp α (d + 1)) → LexT α (towerExp α d) → Prop := fun d x y =>
    if hd : d + 1 < h then F.Adj (L.b (towerMk (d + 1) hd x)) (L.b (towerMk d (by omega) y))
    else False
  obtain ⟨e, hcopy, -, hunif⟩ := tower_homogenize Q M (h - 1) (fun _ => True)
  have hM : ∀ d (hd : d + 1 < h) x y, M d x y ↔
      F.Adj (L.b (towerMk (d + 1) hd x)) (L.b (towerMk d (by omega) y)) := by
    intro d hd x y
    simp only [M, dif_pos hd]
  -- every fibre copy carries a lift of Q, hence an arm
  have harm : ∀ d (hd : d < h), ∃ idx : Fin (n + 1) → α, Function.Injective idx ∧
      IsInducedPath F (fun k => if k = 0 then L.z (towerMk d hd (e d (idx k)))
        else L.b (towerMk d hd (e d (idx k)))) := by
    intro d hd
    have hc := hcopy d (by omega)
    have hinjE : Function.Injective (fun a => (towerMk d hd (e d a) : TowerV α h)) := by
      intro a a' haa
      have h1 : e d a = e d a' := by
        have h2 := Sigma.mk.inj_iff.mp haa
        exact eq_of_heq h2.2
      exact hc.1 h1
    have hadjE : ∀ a a', (towerGraph Q h).Adj (towerMk d hd (e d a)) (towerMk d hd (e d a')) ↔
        Q.Adj a a' := fun a a' => (towerGraph_adj_same Q hd _ _).trans (hc.2 a a')
    rcases hQ V F (L.comp _ hinjE hadjE) with hp | harm
    · exact absurd hp hpath
    · exact harm
  by_cases hbad : ∃ j, j < n ∧ ∀ a a', ¬ M j (e (j + 1) a) (e j a')
  · -- an anticomplete pair among the first n: a long induced path
    exfalso
    obtain ⟨j, hjn, hanti⟩ := hbad
    have hj1 : j + 1 < h := by omega
    have hj0 : j < h := by omega
    obtain ⟨idx, hidx, hp⟩ := harm j hj0
    set arm : Fin (n + 1) → V := fun k => if k = 0 then L.z (towerMk j hj0 (e j (idx k)))
      else L.b (towerMk j hj0 (e j (idx k))) with harmdef
    have hp1 := inducedPath_rev F arm hp
    set m := h - 1 - j with hm
    let p2 : Fin m → V := fun k =>
      if k.val = 0 then L.b (towerMk (j + 1) hj1 (e (j + 1) a0))
      else L.z (towerMk (j + 1 + k.val) (by have := k.isLt; omega) (e (j + 1 + k.val) a0))
    have hp2 : IsInducedPath F p2 := by
      constructor
      · intro k k' hkk
        by_cases hk : k.val = 0 <;> by_cases hk' : k'.val = 0
        · exact Fin.ext (by omega)
        · simp only [p2, if_pos hk, if_neg hk'] at hkk
          exact absurd hkk.symm (L.hzb_ne _ _)
        · simp only [p2, if_neg hk, if_pos hk'] at hkk
          exact absurd hkk (L.hzb_ne _ _)
        · simp only [p2, if_neg hk, if_neg hk'] at hkk
          have h1 := towerMk_fibre (L.hz_inj hkk)
          exact Fin.ext (by omega)
      · intro k k'
        by_cases hk : k.val = 0 <;> by_cases hk' : k'.val = 0
        · simp only [p2, if_pos hk, if_pos hk']
          constructor
          · intro hh
            exact absurd hh F.irrefl
          · intro hh
            omega
        · simp only [p2, if_pos hk, if_neg hk']
          rw [F.adj_comm, L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
            towerGraph_adj_ne Q _ _ (by omega)]
          omega
        · simp only [p2, if_neg hk, if_pos hk']
          rw [L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
            towerGraph_adj_ne Q _ _ (by omega)]
          omega
        · simp only [p2, if_neg hk, if_neg hk']
          by_cases hkk : k.val = k'.val
          · have hkeq : k = k' := Fin.ext hkk
            subst hkeq
            constructor
            · intro hh
              exact absurd hh F.irrefl
            · intro hh
              omega
          · rw [L.hzz _ _ (fun he => by have := towerMk_fibre he; omega),
              towerGraph_adj_ne Q _ _ (by omega)]
            omega
    have hne : ∀ i k, arm (Fin.rev i) ≠ p2 k := by
      intro i k
      by_cases hi : Fin.rev i = 0 <;> by_cases hk : k.val = 0
      · simp only [harmdef, p2, if_pos hi, if_pos hk]
        exact L.hzb_ne _ _
      · simp only [harmdef, p2, if_pos hi, if_neg hk]
        intro he
        have := towerMk_fibre (L.hz_inj he)
        omega
      · simp only [harmdef, p2, if_neg hi, if_pos hk]
        intro he
        have := towerMk_fibre (L.hb_inj he)
        omega
      · simp only [harmdef, p2, if_neg hi, if_neg hk]
        exact fun he => L.hzb_ne _ _ he.symm
    have hadj : ∀ i k, F.Adj (arm (Fin.rev i)) (p2 k) ↔ (i.val + 1 = n + 1 ∧ k.val = 0) := by
      intro i k
      have hrev : Fin.rev i = 0 ↔ i.val = n := by
        constructor
        · intro hh
          have := congrArg Fin.val hh
          simp only [Fin.val_rev, Fin.val_zero] at this
          have := i.isLt
          omega
        · intro hh
          apply Fin.ext
          simp only [Fin.val_rev, Fin.val_zero]
          omega
      by_cases hi : Fin.rev i = 0 <;> by_cases hk : k.val = 0
      · simp only [harmdef, p2, if_pos hi, if_pos hk]
        rw [L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
          towerGraph_adj_ne Q _ _ (by omega)]
        have := hrev.mp hi
        omega
      · simp only [harmdef, p2, if_pos hi, if_neg hk]
        rw [L.hzz _ _ (fun he => by have := towerMk_fibre he; omega),
          towerGraph_adj_ne Q _ _ (by omega)]
        omega
      · simp only [harmdef, p2, if_neg hi, if_pos hk]
        have hni : i.val ≠ n := fun hh => hi (hrev.mpr hh)
        constructor
        · intro hh
          exact absurd ((hM j hj1 _ _).mpr (F.adj_symm hh)) (hanti _ _)
        · intro hh
          omega
      · simp only [harmdef, p2, if_neg hi, if_neg hk]
        rw [F.adj_comm, L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
          towerGraph_adj_ne Q _ _ (by omega)]
        omega
    have hbig := inducedPath_append F (fun i => arm (Fin.rev i)) p2 hp1 hp2 hne hadj
    have hlen : s ≤ n + 1 + m := by omega
    exact hpath ⟨_, inducedPath_castLE F hlen _ hbig⟩
  · -- the first n consecutive pairs are complete: an (n+2)-arm
    push Not at hbad
    have hcomp : ∀ j, j < n → ∀ a a', M j (e (j + 1) a) (e j a') := by
      intro j hj
      rcases hunif j (by omega) with hc | hc
      · exact hc
      · obtain ⟨a, a', haa⟩ := hbad j hj
        exact absurd haa (hc a a')
    refine ⟨fun k => towerMk (n + 1 - k.val) (by omega) (e (n + 1 - k.val) a0), ?_, ?_⟩
    · intro k k' hkk
      have h1 := towerMk_fibre hkk
      have := k.isLt
      have := k'.isLt
      exact Fin.ext (by omega)
    · constructor
      · intro k k' hkk
        have hkl := k.isLt
        have hkl' := k'.isLt
        by_cases hk : k = 0 <;> by_cases hk' : k' = 0
        · rw [hk, hk']
        · simp only [if_pos hk, if_neg hk'] at hkk
          exact absurd hkk (L.hzb_ne _ _)
        · simp only [if_neg hk, if_pos hk'] at hkk
          exact absurd hkk.symm (L.hzb_ne _ _)
        · simp only [if_neg hk, if_neg hk'] at hkk
          have h1 := towerMk_fibre (L.hb_inj hkk)
          exact Fin.ext (by omega)
      · intro k k'
        have hkl := k.isLt
        have hkl' := k'.isLt
        have hk0 : k = 0 ↔ k.val = 0 := by
          constructor
          · intro hh; rw [hh]; rfl
          · intro hh; exact Fin.ext hh
        have hk0' : k' = 0 ↔ k'.val = 0 := by
          constructor
          · intro hh; rw [hh]; rfl
          · intro hh; exact Fin.ext hh
        by_cases hk : k = 0 <;> by_cases hk' : k' = 0
        · simp only [if_pos hk, if_pos hk']
          have h1 := hk0.mp hk
          have h2 := hk0'.mp hk'
          constructor
          · intro hh
            rw [hk, hk'] at hh
            exact absurd hh F.irrefl
          · intro hh
            omega
        · simp only [if_pos hk, if_neg hk']
          have h1 := hk0.mp hk
          have h2 : k'.val ≠ 0 := fun hh => hk' (hk0'.mpr hh)
          rw [L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
            towerGraph_adj_ne Q _ _ (by omega)]
          omega
        · simp only [if_neg hk, if_pos hk']
          have h1 : k.val ≠ 0 := fun hh => hk (hk0.mpr hh)
          have h2 := hk0'.mp hk'
          rw [F.adj_comm, L.hzb _ _ (fun he => by have := towerMk_fibre he; omega),
            towerGraph_adj_ne Q _ _ (by omega)]
          omega
        · simp only [if_neg hk, if_neg hk']
          have h1 : k.val ≠ 0 := fun hh => hk (hk0.mpr hh)
          have h2 : k'.val ≠ 0 := fun hh => hk' (hk0'.mpr hh)
          by_cases hkk : k.val = k'.val
          · have hkeq : k = k' := Fin.ext hkk
            subst hkeq
            constructor
            · intro hh
              exact absurd hh F.irrefl
            · intro hh
              omega
          · constructor
            · intro hh
              have h3 := L.hbb _ _ hh
              rw [towerGraph_adj_ne Q _ _ (by omega)] at h3
              omega
            · intro hh
              rcases hh with hh | hh
              · -- k' = k + 1: fibres (n+1-k) = (n+1-k') + 1
                have hd : n + 1 - k'.val < n := by omega
                have hc := hcomp (n + 1 - k'.val) hd a0 a0
                have hd1 : n + 1 - k'.val + 1 < h := by omega
                have h4 := (hM _ hd1 _ _).mp hc
                have hidx : n + 1 - k'.val + 1 = n + 1 - k.val := by omega
                have hE : (towerMk (n + 1 - k'.val + 1) hd1 (e (n + 1 - k'.val + 1) a0) :
                    TowerV α h) = towerMk (n + 1 - k.val) (by omega) (e (n + 1 - k.val) a0) :=
                  towerMk_congr hidx hd1 _ (fun d => e d a0)
                rw [hE] at h4
                exact h4
              · have hd : n + 1 - k.val < n := by omega
                have hc := hcomp (n + 1 - k.val) hd a0 a0
                have hd1 : n + 1 - k.val + 1 < h := by omega
                have h4 := F.adj_symm ((hM _ hd1 _ _).mp hc)
                have hidx : n + 1 - k.val + 1 = n + 1 - k'.val := by omega
                have hE : (towerMk (n + 1 - k.val + 1) hd1 (e (n + 1 - k.val + 1) a0) :
                    TowerV α h) = towerMk (n + 1 - k'.val) (by omega) (e (n + 1 - k'.val) a0) :=
                  towerMk_congr hidx hd1 _ (fun d => e d a0)
                rw [hE] at h4
                exact h4

#print axioms towerGraph_adj_ne
#print axioms towerGraph_adj_same
#print axioms forcing_step
end AllPathsLocal
