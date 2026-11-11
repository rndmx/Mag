/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDLocAMain
import AlgMag.SDTorus

/-!
# Lemma D, Step 1: the closed orbit is `κ[Λ]`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Step 1. Let `I` be a maximal
homogeneous ideal over `q`, for a grading with invariants `A₀`. Localizing `A/I` at `A₀ ∖ q` gives a graded field `E`.
When the degrees form a free group, `E` has a graded augmentation to `K = E₀`, a residue field of `q`; this gives
`Ω : A → K[Γ]` with kernel `I`, supported on the subgroup `Λ` of degrees. So `I` is prime, and `q A ⊂ I`.
-/

universe u

namespace AlgMag.SD

open AlgMag.SQ AlgMag.SDTorus

section GradedField

variable {E Γ : Type u} [CommRing E] [AddCommGroup Γ] (c : Coact E Γ)

lemma SDR3Orbit_isHom_one : c.IsHom 0 (1 : E) := by
  change c.σ 1 = _
  rw [map_one, AddMonoidAlgebra.one_def]

lemma SDR3Orbit_isHom_add {d : Γ} {a b : E} (ha : c.IsHom d a) (hb : c.IsHom d b) : c.IsHom d (a + b) := by
  change c.σ (a + b) = _
  rw [map_add, ha, hb, AddMonoidAlgebra.single_add]

lemma SDR3Orbit_isHom_zero (d : Γ) : c.IsHom d (0 : E) := by
  change c.σ 0 = _
  simp

lemma SDR3Orbit_isHom_neg {d : Γ} {a : E} (ha : c.IsHom d a) : c.IsHom d (-a) := by
  change c.σ (-a) = _
  rw [map_neg, ha, AddMonoidAlgebra.single_neg]

/-- The inverse of a homogeneous unit is homogeneous. -/
lemma SDR3Orbit_isHom_inv {d : Γ} {a b : E} (ha : c.IsHom d a) (hab : a * b = 1) : c.IsHom (-d) b := by
  have h1 : a * c.comp (0 - d) b = 1 := by
    rw [← c.comp_mul_of_isHom ha, hab]
    exact c.comp_self_of_isHom (SDR3Orbit_isHom_one c)
  have h2 : c.comp (0 - d) b = b := by
    calc c.comp (0 - d) b = (a * b) * c.comp (0 - d) b := by rw [hab, one_mul]
      _ = b * (a * c.comp (0 - d) b) := by ring
      _ = b := by rw [h1, mul_one]
  have := c.comp_isHom (0 - d) b
  rwa [h2, zero_sub] at this

variable [Nontrivial E]

/-- The subgroup of degrees of a graded field. -/
def SDR3Orbit_Λ (hu : ∀ d a, c.IsHom d a → a ≠ 0 → IsUnit a) : AddSubgroup Γ where
  carrier := {d | ∃ a, c.IsHom d a ∧ a ≠ 0}
  zero_mem' := ⟨1, SDR3Orbit_isHom_one c, one_ne_zero⟩
  add_mem' := by
    rintro d e ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
    exact ⟨a * b, ha.mul hb, ((hu d a ha ha0).mul (hu e b hb hb0)).ne_zero⟩
  neg_mem' := by
    rintro d ⟨a, ha, ha0⟩
    obtain ⟨b, hb⟩ := (hu d a ha ha0).exists_right_inv
    refine ⟨b, SDR3Orbit_isHom_inv c ha hb, fun h => ?_⟩
    rw [h, mul_zero] at hb
    exact zero_ne_one hb

/-- **Step 1, the augmentation**: a graded field whose degrees form a free group maps to its degree `0` part. -/
theorem SDR3Orbit_gradedField (hu : ∀ d a, c.IsHom d a → a ≠ 0 → IsUnit a)
    (hfree : Module.Free ℤ (SDR3Orbit_Λ c hu)) :
    ∃ φ : E →+* E, (∀ y, c.IsHom 0 (φ y)) ∧ (∀ a, c.IsHom 0 a → φ a = a) ∧
      ∀ d a, c.IsHom d a → a ≠ 0 → IsUnit (φ a) := by
  classical
  let Λ := SDR3Orbit_Λ c hu
  let b := Module.Free.chooseBasis ℤ Λ
  have hex : ∀ i, ∃ a : Eˣ, c.IsHom (b i : Γ) (a : E) := fun i => by
    obtain ⟨a, ha, ha0⟩ := (b i).2
    exact ⟨(hu _ a ha ha0).unit, ha⟩
  choose a ha using hex
  let χ : Λ →ₗ[ℤ] Additive Eˣ := b.constr ℤ fun i => Additive.ofMul (a i)
  let St : Submodule ℤ Λ := AddSubgroup.toIntSubmodule
    { carrier := {l | c.IsHom (l : Γ) ((χ l).toMul : E)}
      zero_mem' := by
        change c.IsHom 0 (((χ 0).toMul : Eˣ) : E)
        rw [map_zero]
        exact SDR3Orbit_isHom_one c
      add_mem' := by
        intro l m hl hm
        change c.IsHom ((l : Γ) + m) (((χ (l + m)).toMul : Eˣ) : E)
        rw [map_add]
        exact Coact.IsHom.mul hl hm
      neg_mem' := by
        intro l hl
        change c.IsHom (-(l : Γ)) (((χ (-l)).toMul : Eˣ) : E)
        rw [map_neg]
        exact SDR3Orbit_isHom_inv c hl (Units.mul_inv _) }
  have hχ : ∀ l : Λ, c.IsHom (l : Γ) ((χ l).toMul : E) := by
    have htop : (⊤ : Submodule ℤ Λ) ≤ St := by
      rw [← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change c.IsHom (b i : Γ) (((χ (b i)).toMul : Eˣ) : E)
      simp only [χ, Module.Basis.constr_basis]
      exact ha i
    exact fun l => htop (Submodule.mem_top (x := l))
  have hinv : ∀ l : Λ, c.IsHom (-(l : Γ)) (((χ l).toMul⁻¹ : Eˣ) : E) := fun l =>
    SDR3Orbit_isHom_inv c (hχ l) (Units.mul_inv _)
  let ψ : Γ → E := fun d => if h : d ∈ Λ then (((χ ⟨d, h⟩).toMul⁻¹ : Eˣ) : E) else 0
  have hψ : ∀ l : Λ, ψ l = (((χ l).toMul⁻¹ : Eˣ) : E) := fun l => by simp [ψ]
  have hψ0 : ψ 0 = 1 := by
    have := hψ 0
    simpa using this
  have hψadd : ∀ l m : Λ, ψ ((l : Γ) + m) = ψ l * ψ m := fun l m => by
    have := hψ (l + m)
    rw [AddSubgroup.coe_add] at this
    rw [this, hψ, hψ, map_add]
    simp [mul_comm]
  have hdeg : ∀ {d : Γ} {y : E}, c.IsHom d y → y ≠ 0 → d ∈ Λ := fun hy h0 => ⟨_, hy, h0⟩
  let φf : E → E := fun y => (c.σ y).coeff.sum fun d x => x * ψ d
  have hφadd : ∀ x y, φf (x + y) = φf x + φf y := fun x y => by
    simp only [φf, map_add, AddMonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index' (by simp) (by intro d p q; ring)
  have hφhom : ∀ {d : Γ} {y : E}, c.IsHom d y → φf y = y * ψ d := by
    intro d y hy
    simp only [φf]
    have hy' : c.σ y = AddMonoidAlgebra.single d y := hy
    rw [hy', AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]
  have hφ0 : φf 0 = 0 := by simp [φf]
  have hφmulH : ∀ {d e : Γ} {x y : E}, c.IsHom d x → c.IsHom e y → φf (x * y) = φf x * φf y := by
    intro d e x y hx hy
    rw [hφhom (hx.mul hy), hφhom hx, hφhom hy]
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have := hψadd ⟨d, hdeg hx hx0⟩ ⟨e, hdeg hy hy0⟩
    simp only at this
    rw [this]
    ring
  have hφmul : ∀ x y, φf (x * y) = φf x * φf y := by
    intro x y
    induction x using c.induction with
    | h0 => simp [hφ0]
    | hadd x₁ x₂ h₁ h₂ => rw [add_mul, hφadd, h₁, h₂, hφadd, add_mul]
    | hh d x₁ hx₁ =>
      induction y using c.induction with
      | h0 => simp [hφ0]
      | hadd y₁ y₂ h₁ h₂ => rw [mul_add, hφadd, h₁, h₂, hφadd, mul_add]
      | hh e y₁ hy₁ => exact hφmulH hx₁ hy₁
  have hφ1 : φf 1 = 1 := by rw [hφhom (SDR3Orbit_isHom_one c), hψ0, one_mul]
  let φ : E →+* E :=
    { toFun := φf, map_one' := hφ1, map_mul' := hφmul, map_zero' := hφ0, map_add' := hφadd }
  refine ⟨φ, fun y => ?_, fun a ha0 => ?_, fun d x hx hx0 => ?_⟩
  · change c.IsHom 0 (φf y)
    induction y using c.induction with
    | h0 => rw [hφ0]; exact SDR3Orbit_isHom_zero c 0
    | hadd x₁ x₂ h₁ h₂ => rw [hφadd]; exact SDR3Orbit_isHom_add c h₁ h₂
    | hh d x₁ hx₁ =>
      rw [hφhom hx₁]
      by_cases h0 : x₁ = 0
      · rw [h0, zero_mul]; exact SDR3Orbit_isHom_zero c 0
      · have hm := hdeg hx₁ h0
        have h1 := hψ ⟨d, hm⟩
        simp only at h1
        rw [h1]
        have h2 := hx₁.mul (hinv ⟨d, hm⟩)
        simpa using h2
  · change φf a = a
    rw [hφhom ha0, hψ0, mul_one]
  · change IsUnit (φf x)
    rw [hφhom hx]
    have hm := hdeg hx hx0
    have h1 := hψ ⟨d, hm⟩
    simp only at h1
    rw [h1]
    exact (hu d x hx hx0).mul (Units.isUnit _)

end GradedField

/-! ### Localizing a grading at invariants -/

section Loc

variable {B Γ : Type u} [CommRing B] [AddCommGroup Γ] (c : Coact B Γ) (S : Submonoid B)
  (hS : ∀ s ∈ S, c.IsHom 0 s)

/-- The map `B → Loc[Γ]`. -/
noncomputable abbrev SDR3Orbit_locMap : B →+* AddMonoidAlgebra (Localization S) Γ :=
  (AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S))).comp c.σ

include hS in
lemma SDR3Orbit_locMap_unit (s : S) : IsUnit (SDR3Orbit_locMap c S s) := by
  have h0 : c.σ (s : B) = AddMonoidAlgebra.single 0 (s : B) := hS s s.2
  simp only [SDR3Orbit_locMap, RingHom.comp_apply, h0, AddMonoidAlgebra.mapRingHom_single]
  obtain ⟨v, hv⟩ := (IsLocalization.map_units (Localization S) s).exists_right_inv
  refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single 0 v) ?_
  rw [AddMonoidAlgebra.single_mul_single, add_zero, hv, AddMonoidAlgebra.one_def]

/-- The coaction on `Localization S`. -/
noncomputable def SDR3Orbit_locσ : Localization S →+* AddMonoidAlgebra (Localization S) Γ :=
  IsLocalization.lift (M := S) (g := SDR3Orbit_locMap c S) (SDR3Orbit_locMap_unit c S hS)

lemma SDR3Orbit_locσ_alg (b : B) : SDR3Orbit_locσ c S hS (algebraMap B _ b) =
    AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S)) (c.σ b) :=
  IsLocalization.lift_eq _ b

/-- The augmentation of `R[Γ]`, written as the sum of the coefficients. -/
lemma SDR3Orbit_sum_mul {R : Type u} [CommRing R] (x y : AddMonoidAlgebra R Γ) :
    (x * y).coeff.sum (fun _ a => a) = x.coeff.sum (fun _ a => a) * y.coeff.sum (fun _ a => a) := by
  let ε : AddMonoidAlgebra R Γ →+* R := (AddMonoidAlgebra.lift R R Γ (1 : Multiplicative Γ →* R)).toRingHom
  have hε : ∀ z : AddMonoidAlgebra R Γ, ε z = z.coeff.sum (fun _ a => a) := fun z => by
    change AddMonoidAlgebra.lift R R Γ _ z = _
    rw [AddMonoidAlgebra.lift_apply]
    simp
  rw [← hε, ← hε, ← hε, map_mul]

/-- The grading of a localization at invariants. -/
noncomputable def SDR3Orbit_locCoact : Coact (Localization S) Γ where
  σ := SDR3Orbit_locσ c S hS
  sum_eq y := by
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S y
    simp only at hbs
    have hs0 : (AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S)) (c.σ (s : B))) =
        AddMonoidAlgebra.single 0 (algebraMap B _ (s : B)) := by
      rw [hS s s.2, AddMonoidAlgebra.mapRingHom_single]
    have hb : ∀ b : B, ((AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S))) (c.σ b)).coeff.sum
        (fun _ a => a) = algebraMap B (Localization S) b := by
      intro b
      conv_rhs => rw [← c.sum_eq b, Finsupp.sum, map_sum]
      rw [Finsupp.sum]
      have hsub : ((AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S))) (c.σ b)).coeff.support ⊆
          (c.σ b).coeff.support := fun d hd => by
        rw [Finsupp.mem_support_iff] at hd ⊢
        intro h0
        apply hd
        rw [AddMonoidAlgebra.coeff_mapRingHom, h0, map_zero]
      refine (Finset.sum_subset hsub fun d _ hd => Finsupp.notMem_support_iff.1 hd).trans ?_
      exact Finset.sum_congr rfl fun d _ => AddMonoidAlgebra.coeff_mapRingHom ..
    have h1 := congrArg (fun z => z.coeff.sum (fun _ a => a)) (congrArg (SDR3Orbit_locσ c S hS) hbs)
    simp only [map_mul, SDR3Orbit_locσ_alg] at h1
    rw [SDR3Orbit_sum_mul, hb, hb] at h1
    exact (IsLocalization.map_units (Localization S) s).mul_right_cancel (h1.trans hbs.symm)
  hom y d := by
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj S y
    simp only at hbs
    set a := (SDR3Orbit_locσ c S hS y).coeff d with ha
    have hs0 : SDR3Orbit_locσ c S hS (algebraMap B _ (s : B)) = AddMonoidAlgebra.single 0 (algebraMap B _ (s : B)) := by
      rw [SDR3Orbit_locσ_alg, hS s s.2, AddMonoidAlgebra.mapRingHom_single]
    have h1 : SDR3Orbit_locσ c S hS y * AddMonoidAlgebra.single 0 (algebraMap B _ (s : B)) =
        AddMonoidAlgebra.mapRingHom Γ (algebraMap B (Localization S)) (c.σ b) := by
      rw [← hs0, ← map_mul, hbs, SDR3Orbit_locσ_alg]
    have h2 : a * algebraMap B _ (s : B) = algebraMap B _ (c.comp d b) := by
      have := congrArg (fun z => z.coeff d) h1
      simp only [AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_mapRingHom] at this
      exact this
    have hc : c.σ (c.comp d b) = AddMonoidAlgebra.single d (c.comp d b) := c.comp_isHom d b
    have hL : SDR3Orbit_locσ c S hS a * AddMonoidAlgebra.single 0 (algebraMap B _ (s : B)) =
        AddMonoidAlgebra.single d (algebraMap B (Localization S) (c.comp d b)) := by
      rw [← hs0, ← map_mul, h2, SDR3Orbit_locσ_alg, hc, AddMonoidAlgebra.mapRingHom_single]
    have hR : AddMonoidAlgebra.single d a * AddMonoidAlgebra.single 0 (algebraMap B (Localization S) (s : B)) =
        AddMonoidAlgebra.single d (algebraMap B (Localization S) (c.comp d b)) := by
      rw [AddMonoidAlgebra.single_mul_single, add_zero, h2]
    have h3 := hL.trans hR.symm
    obtain ⟨v, hv⟩ := (IsLocalization.map_units (Localization S) s).exists_right_inv
    have hu : IsUnit (AddMonoidAlgebra.single (0 : Γ) (algebraMap B (Localization S) (s : B))) := by
      refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single 0 v) ?_
      rw [AddMonoidAlgebra.single_mul_single, add_zero, hv, AddMonoidAlgebra.one_def]
    exact hu.mul_left_inj.1 h3

lemma SDR3Orbit_locCoact_alg (d : Γ) (b : B) :
    (SDR3Orbit_locCoact c S hS).comp d (algebraMap B _ b) = algebraMap B _ (c.comp d b) := by
  change (SDR3Orbit_locσ c S hS _).coeff d = _
  rw [SDR3Orbit_locσ_alg, AddMonoidAlgebra.coeff_mapRingHom]
  rfl

end Loc

/-! ### The closed orbit -/

section Orbit

variable {A A₀ Γ : Type u} [CommRing A] [CommRing A₀] [AddCommGroup Γ] {c : Coact A Γ} {ι : A₀ →+* A}

/-- `q A ⊂ I`, by maximality of the closed orbit. -/
theorem SDR3Orbit_q_mem (hι : c.IsInv ι) {q : Ideal A₀} [q.IsPrime] {I : Ideal A} (hI : c.IsHomIdeal I)
    (hIq : ∀ a, ι a ∈ I → a ∈ q) (hmax : ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    {a : A₀} (ha : a ∈ q) : ι a ∈ I := by
  by_contra hn
  obtain ⟨h, hh, b, hb⟩ := exists_inv_of_homog hι hI hIq hmax ((hι.range _).2 ⟨a, rfl⟩) hn
  apply hh
  have e0 : c.comp 0 (ι h) = ι h := c.comp_self_of_isHom ((hι.range _).2 ⟨h, rfl⟩)
  have e1 : ι h = ι (a * hι.r b) := by
    rw [← e0, hb, hι.comp_ι, map_mul, hι.ι_r]
  rw [hι.inj e1]
  exact q.mul_mem_right _ ha

/-- **Step 1.** The closed orbit `I` over `q`: a field `K`, a residue field of `q`, and a map `φ : A → K` extending
`A₀ → K` whose vanishing on homogeneous elements detects `I`. The added hypothesis `hfree` holds for `Γ = ℤ^r`. -/
theorem SDR3Orbit_closedOrbit (hι : c.IsInv ι) {q : Ideal A₀} [q.IsPrime] {I : Ideal A} (hI : c.IsHomIdeal I)
    (hIq : ∀ a, ι a ∈ I → a ∈ q) (hmax : ∀ J, c.IsHomIdeal J → I < J → ∃ a, ι a ∈ J ∧ a ∉ q)
    (hfree : ∀ L : AddSubgroup Γ, Module.Free ℤ L) :
    ∃ (K : Type u) (_ : Field K) (ρ : A₀ →+* K) (φ : A →+* K), (∀ a, φ (ι a) = ρ a) ∧ (∀ a, ρ a = 0 ↔ a ∈ q) ∧
      (∀ k, ∃ r s, s ∉ q ∧ k * ρ s = ρ r) ∧ ∀ d a, c.IsHom d a → (φ a = 0 ↔ a ∈ I) := by
  classical
  let cB := SDLocA_quot c I hI
  let mk := Ideal.Quotient.mk I
  let S : Submonoid (A ⧸ I) := q.primeCompl.map (mk.comp ι)
  have hS : ∀ s ∈ S, cB.IsHom 0 s := by
    rintro _ ⟨s, -, rfl⟩
    have h0 : c.comp 0 (ι s) = ι s := c.comp_self_of_isHom ((hι.range _).2 ⟨s, rfl⟩)
    have := cB.comp_isHom 0 (mk (ι s))
    rwa [SDLocA_quot_comp, h0] at this
  let E := Localization S
  let cE : Coact E Γ := SDR3Orbit_locCoact cB S hS
  let α : A →+* E := (algebraMap (A ⧸ I) E).comp mk
  have hαI : ∀ a, α a = 0 ↔ ∃ s, s ∉ q ∧ ι s * a ∈ I := by
    intro a
    constructor
    · intro h
      obtain ⟨⟨_, s, hs, rfl⟩, hz⟩ := (IsLocalization.map_eq_zero_iff S E _).1 h
      exact ⟨s, hs, Ideal.Quotient.eq_zero_iff_mem.1 (by simpa [mk] using hz)⟩
    · rintro ⟨s, hs, hm⟩
      refine (IsLocalization.map_eq_zero_iff S E _).2 ⟨⟨_, s, hs, rfl⟩, ?_⟩
      have : mk (ι s * a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      simpa [mk] using this
  have hαu : ∀ s, s ∉ q → IsUnit (α (ι s)) := fun s hs =>
    IsLocalization.map_units E (⟨mk (ι s), s, hs, rfl⟩ : S)
  have h1q : (1 : A₀) ∉ q := (Ideal.ne_top_iff_one q).1 (Ideal.IsPrime.ne_top ‹_›)
  have hne : Nontrivial E := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have h1 : α 1 = 0 := by rw [map_one]; exact h
    obtain ⟨s, hs, hm⟩ := (hαI 1).1 h1
    exact hs (hIq s (by simpa using hm))
  have hcomp : ∀ d a, cE.comp d (α a) = α (c.comp d a) := fun d a => by
    change cE.comp d (algebraMap _ _ (mk a)) = _
    rw [SDR3Orbit_locCoact_alg, SDLocA_quot_comp]
    rfl
  have hαhom : ∀ {d a}, c.IsHom d a → cE.IsHom d (α a) := fun {d a} ha => by
    have := cE.comp_isHom d (α a)
    rwa [hcomp, c.comp_self_of_isHom ha] at this
  have hform : ∀ d y, cE.IsHom d y → ∃ s a, s ∉ q ∧ c.IsHom d a ∧ y * α (ι s) = α a := by
    intro d y hy
    obtain ⟨⟨b, ⟨_, s, hs, rfl⟩⟩, hbs⟩ := IsLocalization.surj S y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hbs' : y * α (ι s) = α a := hbs
    refine ⟨s, c.comp d a, hs, c.comp_isHom d a, ?_⟩
    have h1 := congrArg (cE.comp d) hbs'
    rw [hcomp, mul_comm, cE.comp_mul_of_isHom (hαhom ((hι.range _).2 ⟨s, rfl⟩)), sub_zero,
      cE.comp_self_of_isHom hy] at h1
    rw [mul_comm]
    exact h1
  have hu : ∀ d y, cE.IsHom d y → y ≠ 0 → IsUnit y := by
    intro d y hy hy0
    obtain ⟨s, a, hs, ha, he⟩ := hform d y hy
    have haI : a ∉ I := fun hm => hy0 (by
      have h0 : α a = 0 := (hαI a).2 ⟨1, h1q, by simpa using hm⟩
      rw [h0] at he
      exact (hαu s hs).mul_left_eq_zero.1 he)
    obtain ⟨h, hh, b, hb⟩ := exists_inv_of_homog hι hI hIq hmax ha haI
    have hua : IsUnit (α a) := by
      have : IsUnit (α a * α b) := by rw [← map_mul, ← hb]; exact hαu h hh
      exact isUnit_of_mul_isUnit_left this
    rw [← he] at hua
    exact isUnit_of_mul_isUnit_left hua
  obtain ⟨φE, hφ0, hφid, hφu⟩ := SDR3Orbit_gradedField cE hu (hfree _)
  let K : Subring E :=
    { carrier := {y | cE.IsHom 0 y}
      mul_mem' := fun {x y} hx hy => by simpa using Coact.IsHom.mul hx hy
      one_mem' := SDR3Orbit_isHom_one cE
      add_mem' := fun hx hy => SDR3Orbit_isHom_add cE hx hy
      zero_mem' := SDR3Orbit_isHom_zero cE 0
      neg_mem' := fun hx => SDR3Orbit_isHom_neg cE hx }
  have hK : IsField K := by
    refine ⟨⟨1, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩, mul_comm, fun {k} hk => ?_⟩
    have hk0 : (k : E) ≠ 0 := fun h => hk (Subtype.ext h)
    obtain ⟨b, hb⟩ := (hu 0 k k.2 hk0).exists_right_inv
    have hb0 : cE.IsHom 0 b := by simpa using SDR3Orbit_isHom_inv cE k.2 hb
    exact ⟨⟨b, hb0⟩, Subtype.ext hb⟩
  let φ : A →+* K := (φE.comp α).codRestrict K fun y => hφ0 _
  have hιK : ∀ a, cE.IsHom 0 (α (ι a)) := fun a => hαhom ((hι.range _).2 ⟨a, rfl⟩)
  refine ⟨K, hK.toField, φ.comp ι, φ, fun _ => rfl, fun a => ?_, fun k => ?_, fun d a ha => ?_⟩
  · have hv : ((φ.comp ι) a : E) = α (ι a) := hφid _ (hιK a)
    constructor
    · intro h0
      have h1 : α (ι a) = 0 := by rw [← hv, h0]; rfl
      by_contra hn
      exact (hαu a hn).ne_zero h1
    · intro hm
      apply Subtype.ext
      rw [hv]
      exact (hαI _).2 ⟨1, h1q, by simpa using SDR3Orbit_q_mem hι hI hIq hmax hm⟩
  · obtain ⟨s, a, hs, ha, he⟩ := hform 0 k k.2
    obtain ⟨r, rfl⟩ := (hι.range a).1 ha
    refine ⟨r, s, hs, Subtype.ext ?_⟩
    change (k : E) * φE (α (ι s)) = φE (α (ι r))
    rw [hφid _ (hιK s), hφid _ (hιK r)]
    exact he
  · constructor
    · intro h0
      by_contra haI
      have hα : α a ≠ 0 := by
        intro h
        obtain ⟨s, hs, hm⟩ := (hαI a).1 h
        obtain ⟨h', hh', b, hb⟩ := exists_inv_of_homog hι hI hIq hmax ha haI
        have : ι (s * h') ∈ I := by
          rw [map_mul, hb, ← mul_assoc]
          exact I.mul_mem_right _ hm
        obtain h1 | h1 := Ideal.IsPrime.mem_or_mem ‹_› (hIq _ this)
        · exact hs h1
        · exact hh' h1
      have hunit := hφu d (α a) (hαhom ha) hα
      have h1 : φE (α a) = 0 := congrArg Subtype.val h0
      rw [h1] at hunit
      exact not_isUnit_zero hunit
    · intro hm
      apply Subtype.ext
      change φE (α a) = 0
      rw [(hαI a).2 ⟨1, h1q, by simpa using hm⟩, map_zero]

/-- The orbit map `Ω : A → K[Γ]` of `φ`; its kernel is `I`, so `I` is prime for a torsion-free grading. -/
theorem SDR3Orbit_Ω_ker {K : Type u} [Field K] (φ : A →+* K) {I : Ideal A} (hI : c.IsHomIdeal I)
    (hφ : ∀ d a, c.IsHom d a → (φ a = 0 ↔ a ∈ I)) (y : A) :
    (AddMonoidAlgebra.mapRingHom Γ φ).comp c.σ y = 0 ↔ y ∈ I := by
  have hco : ∀ d, ((AddMonoidAlgebra.mapRingHom Γ φ).comp c.σ y).coeff d = φ (c.comp d y) := fun d =>
    AddMonoidAlgebra.coeff_mapRingHom ..
  constructor
  · intro h
    refine c.mem_of_comp_mem I y fun d => (hφ d _ (c.comp_isHom d y)).1 ?_
    rw [← hco, h]
    rfl
  · intro hy
    ext d
    rw [hco]
    exact (hφ d _ (c.comp_isHom d y)).2 (hI y hy d)

/-- The closed orbit is prime. -/
theorem SDR3Orbit_prime [UniqueSums Γ] {K : Type u} [Field K] (φ : A →+* K) {I : Ideal A} (hI : c.IsHomIdeal I)
    (hφ : ∀ d a, c.IsHom d a → (φ a = 0 ↔ a ∈ I)) : I.IsPrime := by
  have : I = RingHom.ker ((AddMonoidAlgebra.mapRingHom Γ φ).comp c.σ) := by
    ext y
    exact (SDR3Orbit_Ω_ker φ hI hφ y).symm
  rw [this]
  exact RingHom.ker_isPrime _

/-- `ℤ^r` has free subgroups. -/
theorem SDR3Orbit_lat_free (r : ℕ) (L : AddSubgroup (Lat.{u} r)) : Module.Free ℤ L := by
  have : Module.Free ℤ (AddSubgroup.toIntSubmodule L) := inferInstance
  exact this

end Orbit

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Orbit_gradedField
#print axioms AlgMag.SD.SDR3Orbit_q_mem
#print axioms AlgMag.SD.SDR3Orbit_closedOrbit
#print axioms AlgMag.SD.SDR3Orbit_Ω_ker
#print axioms AlgMag.SD.SDR3Orbit_prime
#print axioms AlgMag.SD.SDR3Orbit_lat_free
