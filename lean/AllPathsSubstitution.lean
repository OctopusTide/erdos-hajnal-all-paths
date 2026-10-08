import RP5ManyHomogeneous
import RP5BinomialRatio

/-!
Quantitative substitution for the Erdős–Hajnal property (main paper, Part I,
"Quantitative one-vertex substitution"), in a set-relative form: replacing one
vertex `u` of a pattern by a module `M` preserves a positive EH exponent.
No forbidden path is involved; this is the Alon–Pach–Solymosi counting argument.
-/

namespace AllPathsLocal

open Finset

/-- An induced copy, inside the host set `S` of `G`, of the pattern `Ω[X]`. -/
def EmbedsOn {W V : Type} (Ω : SimpleGraph W) (X : Finset W) (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  ∃ f : W → V, Set.InjOn f X ∧ (∀ a ∈ X, f a ∈ S) ∧
    ∀ a ∈ X, ∀ b ∈ X, (G.Adj (f a) (f b) ↔ Ω.Adj a b)

/-- EH exponent `κ` for the pattern `Ω[X]`: every host set without an induced
    copy has a homogeneous subset of size at least `|S|^κ`. -/
def EHOn {W : Type} (Ω : SimpleGraph W) (X : Finset W) (κ : ℝ) : Prop :=
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) (S : Finset V), ¬ EmbedsOn Ω X G S →
    ∃ T ⊆ S, IsHomogeneousFinset G T ∧ (S.card : ℝ) ^ κ ≤ T.card

theorem embedsOn_mono {W V : Type} (Ω : SimpleGraph W) (X : Finset W) (G : SimpleGraph V)
    {S S' : Finset V} (h : EmbedsOn Ω X G S) (hS : S ⊆ S') : EmbedsOn Ω X G S' := by
  obtain ⟨f, hinj, hmem, hadj⟩ := h
  exact ⟨f, hinj, fun a ha => hS (hmem a ha), hadj⟩

theorem homogeneous_of_card_le_two {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (T : Finset V) (hT : T.card ≤ 2) : IsHomogeneousFinset G T := by
  by_cases h : ∃ u ∈ T, ∃ v ∈ T, G.Adj u v
  · obtain ⟨u, hu, v, hv, huv⟩ := h
    left
    intro a ha b hb hab
    have huvne : u ≠ v := G.ne_of_adj huv
    have hsub : ({u, v} : Finset V) ⊆ T := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    have hcard : ({u, v} : Finset V).card = 2 := Finset.card_pair huvne
    have heq : ({u, v} : Finset V) = T :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hT)
    rw [← heq] at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact huv
    · exact G.adj_symm huv
    · exact absurd rfl hab
  · right
    intro a ha b hb hab
    exact h ⟨a, ha, b, hb, hab⟩

/-- The scalar end of the substitution count. -/
theorem substitution_scalar (n r : ℝ) (a : ℕ) (γ δ R1 R2 m k : ℝ)
    (hγ : 0 < γ) (hδ : 0 < δ) (hr : 2 ≤ r) (hR1 : R1 = r ^ (1 / γ)) (hR2 : R2 = r ^ (1 / δ))
    (hm0 : 0 ≤ m) (hm : m ≤ 2 * R1) (hk0 : 0 ≤ k) (hk : k ≤ R2) (hn : n ≤ 2 * k * m ^ a) :
    n ≤ r ^ ((a : ℝ) + 1 + a / γ + 1 / δ) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hR1pos : 0 < R1 := by rw [hR1]; exact Real.rpow_pos_of_pos hr0 _
  have hR2pos : 0 < R2 := by rw [hR2]; exact Real.rpow_pos_of_pos hr0 _
  have h1 : m ^ a ≤ (2 * R1) ^ a := pow_le_pow_left₀ hm0 hm a
  have h2 : 2 * k * m ^ a ≤ 2 * R2 * (2 * R1) ^ a :=
    mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) h1 (by positivity) (by positivity)
  have h3 : 2 * R2 * (2 * R1) ^ a = 2 ^ (a + 1) * (R1 ^ a * R2) := by
    rw [mul_pow, pow_succ]
    ring
  have h4 : (2 : ℝ) ^ (a + 1) ≤ r ^ (a + 1) := pow_le_pow_left₀ (by norm_num) hr (a + 1)
  have h5 : R1 ^ a = r ^ ((a : ℝ) / γ) := by
    rw [hR1, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    congr 1
    field_simp
  have h6 : r ^ (a + 1) = r ^ ((a : ℝ) + 1) := by
    rw [← Real.rpow_natCast]
    push_cast
    rfl
  have h7 : r ^ ((a : ℝ) + 1 + a / γ + 1 / δ) = r ^ ((a : ℝ) + 1) * (r ^ ((a : ℝ) / γ) * R2) := by
    rw [hR2, ← Real.rpow_add hr0, ← Real.rpow_add hr0]
    congr 1
    ring
  rw [h7, ← h5, ← h6]
  have hpos : 0 ≤ R1 ^ a * R2 := by positivity
  calc n ≤ 2 * k * m ^ a := hn
    _ ≤ 2 * R2 * (2 * R1) ^ a := h2
    _ = 2 ^ (a + 1) * (R1 ^ a * R2) := h3
    _ ≤ r ^ (a + 1) * (R1 ^ a * R2) := mul_le_mul_of_nonneg_right h4 hpos

/-- **Module replacement.** If `Ω[X]` has EH exponent `γ` and `Ω[M]` has EH exponent
    `δ`, and every vertex of `X \ {u}` sees all of `M` exactly as it sees `u`, then
    `Ω[(X \ {u}) ∪ M]` has the EH exponent `1/(|X| + 1 + |X|/γ + 1/δ)`. -/
theorem ehOn_module_replace {W : Type} [DecidableEq W] (Ω : SimpleGraph W)
    (X M : Finset W) (u : W) (hu : u ∈ X)
    (hmod : ∀ a ∈ X.erase u, ∀ m ∈ M, (Ω.Adj a m ↔ Ω.Adj a u))
    (γ δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (hX : EHOn Ω X γ) (hM : EHOn Ω M δ) :
    EHOn Ω (X.erase u ∪ M) (1 / ((X.card : ℝ) + 1 + X.card / γ + 1 / δ)) := by
  classical
  intro V _ G S hno
  set a := X.card with ha
  set e : ℝ := (a : ℝ) + 1 + a / γ + 1 / δ with he
  have he1 : 1 ≤ e := by
    have h1 : (0 : ℝ) ≤ a / γ := by positivity
    have h2 : (0 : ℝ) ≤ 1 / δ := by positivity
    have h3 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have he0 : 0 < e := by linarith
  have hκ1 : 1 / e ≤ 1 := by rw [div_le_one he0]; exact he1
  have hκ0 : 0 < 1 / e := by positivity
  set n := S.card with hn
  -- small hosts
  by_cases hn2 : n ≤ 1
  · refine ⟨S, subset_rfl, homogeneous_of_card_le_two G S (by omega), ?_⟩
    show (n : ℝ) ^ (1 / e) ≤ (n : ℝ)
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have h0R : (n : ℝ) = 0 := by exact_mod_cast h0
      rw [h0R, Real.zero_rpow hκ0.ne']
    · have h1 : n = 1 := by omega
      have h1R : (n : ℝ) = 1 := by exact_mod_cast h1
      rw [h1R, Real.one_rpow]
  push Not at hn2
  -- a maximum homogeneous subset
  obtain ⟨T0, hT0mem, hT0max⟩ := Finset.exists_max_image
    (S.powerset.filter (fun T => IsHomogeneousFinset G T)) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, Or.inr (by simp)⟩⟩
  obtain ⟨hT0S, hT0hom⟩ := Finset.mem_filter.mp hT0mem
  have hT0S' : T0 ⊆ S := Finset.mem_powerset.mp hT0S
  have hmax : ∀ T ⊆ S, IsHomogeneousFinset G T → T.card ≤ T0.card := fun T hT hh =>
    hT0max T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hh⟩)
  set r := T0.card with hr
  have hr2 : 2 ≤ r := by
    obtain ⟨P, hPS, hPc⟩ := Finset.exists_subset_card_eq (show 2 ≤ S.card by omega)
    have := hmax P hPS (homogeneous_of_card_le_two G P (by omega))
    omega
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hr0 : (0 : ℝ) < r := by linarith
  -- it suffices to bound n by r^e
  suffices hmain : (n : ℝ) ≤ (r : ℝ) ^ e by
    refine ⟨T0, hT0S', hT0hom, ?_⟩
    have h1 : (n : ℝ) ^ (1 / e) ≤ ((r : ℝ) ^ e) ^ (1 / e) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hmain hκ0.le
    have h2 : ((r : ℝ) ^ e) ^ (1 / e) = r := by
      rw [← Real.rpow_mul hr0.le, mul_one_div_cancel he0.ne', Real.rpow_one]
    rw [h2] at h1
    exact h1
  set R1 : ℝ := (r : ℝ) ^ (1 / γ) with hR1
  set R2 : ℝ := (r : ℝ) ^ (1 / δ) with hR2
  have hR1ge : 1 ≤ R1 := Real.one_le_rpow (by linarith) (by positivity)
  set m := Nat.floor R1 + 1 with hmdef
  have hmgt : R1 < m := by
    rw [hmdef]
    push_cast
    exact Nat.lt_floor_add_one R1
  have hmle : (m : ℝ) ≤ 2 * R1 := by
    rw [hmdef]
    push_cast
    have := Nat.floor_le (show 0 ≤ R1 by linarith)
    linarith
  -- every m-subset of S contains a copy of Ω[X]
  have hcopy : ∀ A ⊆ S, A.card = m → EmbedsOn Ω X G A := by
    intro A hAS hAc
    by_contra hnot
    obtain ⟨T, hTA, hTh, hTc⟩ := hX V G A hnot
    have h1 := hmax T (hTA.trans hAS) hTh
    have h2 : R1 ^ γ < (m : ℝ) ^ γ := Real.rpow_lt_rpow (by linarith) hmgt hγ
    have h3 : R1 ^ γ = r := by
      rw [hR1, ← Real.rpow_mul hr0.le, one_div_mul_cancel hγ.ne', Real.rpow_one]
    rw [hAc] at hTc
    have h4 : (T.card : ℝ) ≤ r := by exact_mod_cast h1
    linarith
  have ha1 : 1 ≤ a := Finset.card_pos.mpr ⟨u, hu⟩
  by_cases hmn : n < m
  · -- n ≤ R1 ≤ r^e
    have h1 : (n : ℝ) ≤ R1 := by
      have h2 : n ≤ Nat.floor R1 := by omega
      exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
    have h3 : R1 ≤ (r : ℝ) ^ e := by
      rw [hR1]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have h4 : 1 / γ ≤ (a : ℝ) / γ := by
        apply div_le_div_of_nonneg_right _ hγ.le
        exact_mod_cast ha1
      have h5 : (0 : ℝ) ≤ 1 / δ := by positivity
      have h6 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
      rw [he]
      linarith
    exact h1.trans h3
  push Not at hmn
  -- vertex sets of copies of Ω[X] in S
  let IsCopy : (W → V) → Prop := fun f => Set.InjOn f X ∧ (∀ x ∈ X, f x ∈ S) ∧
    ∀ x ∈ X, ∀ y ∈ X, (G.Adj (f x) (f y) ↔ Ω.Adj x y)
  let wit : Finset (Finset V) :=
    (S.powersetCard a).filter (fun C => ∃ f, IsCopy f ∧ X.image f = C)
  have hw : ∀ C ∈ wit, C ⊆ S ∧ C.card = a := fun C hC =>
    Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1
  have hex : ∀ A ∈ S.powersetCard m, ∃ C ∈ wit, C ⊆ A := by
    intro A hA
    obtain ⟨hAS, hAc⟩ := Finset.mem_powersetCard.mp hA
    obtain ⟨f, hinj, hmem, hadj⟩ := hcopy A hAS hAc
    refine ⟨X.image f, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩,
      f, ⟨hinj, fun x hx => hAS (hmem x hx), hadj⟩, rfl⟩, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact hAS (hmem x hx)
    · exact Finset.card_image_of_injOn hinj
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact hmem x hx
  have ham : a ≤ m := by
    obtain ⟨A, hAS, hAc⟩ := Finset.exists_subset_card_eq hmn
    obtain ⟨C, hC, hCA⟩ := hex A (Finset.mem_powersetCard.mpr ⟨hAS, hAc⟩)
    have h1 := Finset.card_le_card hCA
    rw [(hw C hC).2, hAc] at h1
    exact h1
  have hcount := good_samples_witness_count S wit (S.powersetCard m) a m ham hw
    (Finset.Subset.refl _) hex
  rw [Finset.card_powersetCard] at hcount
  have hpow := homogeneous_count_power_lower n m a wit.card ham hmn
    (hcount.trans (Nat.mul_le_mul_right _ (by omega)))
  -- one chosen embedding per copy
  obtain ⟨v0, hv0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hchoose : ∀ C : Finset V, C ∈ wit → ∃ f, IsCopy f ∧ X.image f = C := fun C hC =>
    (Finset.mem_filter.mp hC).2
  let F : Finset V → (W → V) := fun C =>
    if h : C ∈ wit then Classical.choose (hchoose C h) else fun _ => v0
  have hF : ∀ C ∈ wit, IsCopy (F C) ∧ X.image (F C) = C := by
    intro C hC
    simp only [F, dif_pos hC]
    exact Classical.choose_spec (hchoose C hC)
  let Y := X.erase u
  let ψ : Finset V → ((x : W) → x ∈ Y → V) := fun C x _ => F C x
  have hψmem : ∀ C ∈ wit, ψ C ∈ Y.pi (fun _ => S) := by
    intro C hC
    rw [Finset.mem_pi]
    intro x hx
    exact (hF C hC).1.2.1 x (Finset.mem_of_mem_erase hx)
  set K := Nat.floor R2 with hK
  have hR2nn : 0 ≤ R2 := by rw [hR2]; positivity
  -- every fibre of ψ has at most R2 members
  have hfibre : ∀ ψ0 ∈ wit.image ψ, (wit.filter (fun C => ψ C = ψ0)).card ≤ K := by
    intro ψ0 hψ0
    obtain ⟨C0, hC0, hC0ψ⟩ := Finset.mem_image.mp hψ0
    set Cs := wit.filter (fun C => ψ C = ψ0) with hCs
    have hCsw : ∀ C ∈ Cs, C ∈ wit ∧ ψ C = ψ0 := fun C hC => Finset.mem_filter.mp hC
    have hagree : ∀ C ∈ Cs, ∀ x ∈ Y, F C x = F C0 x := by
      intro C hC x hx
      have h1 : ψ C = ψ C0 := (hCsw C hC).2.trans hC0ψ.symm
      exact congrFun (congrFun h1 x) hx
    let E := Cs.image (fun C => F C u)
    have hinjE : Set.InjOn (fun C => F C u) (Cs : Set (Finset V)) := by
      intro C hC C' hC' hCC'
      have hCw := (hCsw C hC).1
      have hC'w := (hCsw C' hC').1
      have heq : ∀ x ∈ X, F C x = F C' x := by
        intro x hx
        by_cases hxu : x = u
        · rw [hxu]; exact hCC'
        · have hxY : x ∈ Y := Finset.mem_erase.mpr ⟨hxu, hx⟩
          rw [hagree C hC x hxY, hagree C' hC' x hxY]
      rw [← (hF C hCw).2, ← (hF C' hC'w).2]
      exact Finset.image_congr heq
    have hEcard : E.card = Cs.card := Finset.card_image_of_injOn hinjE
    have hES : E ⊆ S := by
      intro v hv
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hv
      exact (hF C (hCsw C hC).1).1.2.1 u hu
    have hC0w : IsCopy (F C0) := (hF C0 hC0).1
    have hnoM : ¬ EmbedsOn Ω M G E := by
      rintro ⟨g, hginj, hgmem, hgadj⟩
      apply hno
      -- for y ∈ M, g y = F C u for some C in the fibre
      have hgE : ∀ y ∈ M, ∃ C ∈ Cs, g y = F C u := by
        intro y hy
        obtain ⟨C, hC, hCe⟩ := Finset.mem_image.mp (hgmem y hy)
        exact ⟨C, hC, hCe.symm⟩
      have hcross : ∀ x ∈ Y, x ∉ M → ∀ y ∈ M, F C0 x ≠ g y ∧
          (G.Adj (F C0 x) (g y) ↔ Ω.Adj x y) := by
        intro x hx _ y hy
        obtain ⟨C, hC, hgy⟩ := hgE y hy
        have hCcopy := (hF C (hCsw C hC).1).1
        have hxX : x ∈ X := Finset.mem_of_mem_erase hx
        have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
        rw [hgy, ← hagree C hC x hx]
        refine ⟨fun h => hxu (hCcopy.1 hxX hu h), ?_⟩
        rw [hCcopy.2.2 x hxX u hu]
        exact (hmod x hx y hy).symm
      refine ⟨fun x => if x ∈ M then g x else F C0 x, ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        simp only at hxy
        rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
        · by_cases hxM : x ∈ M <;> by_cases hyM : y ∈ M
          · rw [if_pos hxM, if_pos hyM] at hxy; exact hginj hxM hyM hxy
          · rw [if_pos hxM, if_neg hyM] at hxy
            exact absurd hxy.symm (hcross y hy hyM x hxM).1
          · rw [if_neg hxM, if_pos hyM] at hxy
            exact absurd hxy (hcross x hx hxM y hyM).1
          · rw [if_neg hxM, if_neg hyM] at hxy
            exact hC0w.1 (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
        · by_cases hxM : x ∈ M
          · rw [if_pos hxM, if_pos hy] at hxy; exact hginj hxM hy hxy
          · rw [if_neg hxM, if_pos hy] at hxy
            exact absurd hxy (hcross x hx hxM y hy).1
        · by_cases hyM : y ∈ M
          · rw [if_pos hx, if_pos hyM] at hxy; exact hginj hx hyM hxy
          · rw [if_pos hx, if_neg hyM] at hxy
            exact absurd hxy.symm (hcross y hy hyM x hx).1
        · rw [if_pos hx, if_pos hy] at hxy; exact hginj hx hy hxy
      · intro x hx
        by_cases hxM : x ∈ M
        · simp only [if_pos hxM]; exact hES (hgmem x hxM)
        · simp only [if_neg hxM]
          rcases Finset.mem_union.mp hx with hx | hx
          · exact hC0w.2.1 x (Finset.mem_of_mem_erase hx)
          · exact absurd hx hxM
      · intro x hx y hy
        by_cases hxM : x ∈ M <;> by_cases hyM : y ∈ M
        · simp only [if_pos hxM, if_pos hyM]; exact hgadj x hxM y hyM
        · simp only [if_pos hxM, if_neg hyM]
          have hyY : y ∈ Y := (Finset.mem_union.mp hy).resolve_right hyM
          rw [G.adj_comm, Ω.adj_comm]
          exact (hcross y hyY hyM x hxM).2
        · simp only [if_neg hxM, if_pos hyM]
          have hxY : x ∈ Y := (Finset.mem_union.mp hx).resolve_right hxM
          exact (hcross x hxY hxM y hyM).2
        · simp only [if_neg hxM, if_neg hyM]
          have hxY : x ∈ Y := (Finset.mem_union.mp hx).resolve_right hxM
          have hyY : y ∈ Y := (Finset.mem_union.mp hy).resolve_right hyM
          exact hC0w.2.2 x (Finset.mem_of_mem_erase hxY) y (Finset.mem_of_mem_erase hyY)
    obtain ⟨T, hTE, hTh, hTc⟩ := hM V G E hnoM
    have h1 := hmax T (hTE.trans hES) hTh
    have h2 : (E.card : ℝ) ^ δ ≤ r := hTc.trans (by exact_mod_cast h1)
    have h3 : ((E.card : ℝ) ^ δ) ^ (1 / δ) ≤ (r : ℝ) ^ (1 / δ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h2 (one_div_pos.mpr hδ).le
    have h4 : ((E.card : ℝ) ^ δ) ^ (1 / δ) = E.card := by
      rw [← Real.rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hδ.ne', Real.rpow_one]
    rw [h4] at h3
    rw [← hEcard]
    exact Nat.le_floor h3
  have hwit : wit.card ≤ K * n ^ (a - 1) := by
    have h1 := Finset.card_le_mul_card_image wit K hfibre
    have h2 : (wit.image ψ).card ≤ (Y.pi (fun _ => S)).card :=
      Finset.card_le_card (fun ψ0 h => by
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp h
        exact hψmem C hC)
    have h3 : (Y.pi (fun _ => S)).card = n ^ (a - 1) := by
      rw [Finset.card_pi, Finset.prod_const, Finset.card_erase_of_mem hu]
    rw [h3] at h2
    exact h1.trans (Nat.mul_le_mul_left K h2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfinal : (n : ℝ) ≤ 2 * (K : ℝ) * (m : ℝ) ^ a := by
    have hwitR : (wit.card : ℝ) ≤ (K : ℝ) * (n : ℝ) ^ (a - 1) := by exact_mod_cast hwit
    have h1 : (n : ℝ) ^ a ≤ 2 * ((K : ℝ) * (n : ℝ) ^ (a - 1)) * (m : ℝ) ^ a := by
      refine hpow.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h2 : (n : ℝ) ^ a = (n : ℝ) ^ (a - 1) * n := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    have h3 : (n : ℝ) ^ (a - 1) * n ≤ (n : ℝ) ^ (a - 1) * (2 * (K : ℝ) * (m : ℝ) ^ a) := by
      linarith [show 2 * ((K : ℝ) * (n : ℝ) ^ (a - 1)) * (m : ℝ) ^ a =
        (n : ℝ) ^ (a - 1) * (2 * (K : ℝ) * (m : ℝ) ^ a) by ring]
    exact le_of_mul_le_mul_left h3 (by positivity)
  exact substitution_scalar (n : ℝ) (r : ℝ) a γ δ R1 R2 (m : ℝ) (K : ℝ) hγ hδ hrR hR1 hR2
    (Nat.cast_nonneg _) hmle (Nat.cast_nonneg _) (Nat.floor_le hR2nn) hfinal

#print axioms embedsOn_mono
#print axioms homogeneous_of_card_le_two
#print axioms substitution_scalar
#print axioms ehOn_module_replace
end AllPathsLocal
