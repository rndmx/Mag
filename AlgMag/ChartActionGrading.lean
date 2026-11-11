/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartGradedAction
import AlgMag.Sec5Etale

/-!
# The grading attached to an action of `D(M)` on an affine object

Converse of `AlgMag/ChartGradedAction.lean`: an action of `D(M)`, `M` finitely generated, on an
affine object `U` defines the coaction `c : Γ(U) → Γ(U)[M]`, and the homogeneous elements of degree
`d` are the `a` with `c a = a X^d`. This is §7 of the chart-lemma proof,
"action = coaction by `ℤ[M]`; on affines = `M`-grading".
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

local notation "SCH" => BigFppfOver.toScheme B S hS

section Rings
variable (U : BigFppfOver B S hS)

/-- `Γ(U)[M]`. -/
abbrev R1 (M : Type u) [AddCommGroup M] : Type u := AddMonoidAlgebra (RT U) M

/-- `Γ(U)[M][M]`. -/
abbrev R2 (M : Type u) [AddCommGroup M] : Type u := AddMonoidAlgebra (R1 U M) M

/-- `Γ(U) → Γ(U)[M]`. -/
noncomputable abbrev ι1 : RT U →+* R1 U M := AddMonoidAlgebra.singleZeroRingHom

/-- `R → Γ(U)[M][M]`. -/
noncomputable abbrev ι12 : R1 U M →+* R2 U M := AddMonoidAlgebra.singleZeroRingHom

/-- `Γ(U) → Γ(U)[M][M]`. -/
noncomputable abbrev ι2 : RT U →+* R2 U M := (ι12 U).comp (ι1 U)

end Rings

section Eval

variable {A R : Type*} [CommRing A] [CommRing R] {M' : Type*} [AddCommGroup M']

/-- `A[M] → R` given by `x` and `h`. -/
noncomputable def evalAt (x : A →+* R) (h : Multiplicative M' →* R) : AddMonoidAlgebra A M' →+* R :=
  AddMonoidAlgebra.liftNCRingHom x h (fun _ _ => mul_comm _ _)

lemma evalAt_single (x : A →+* R) (h : Multiplicative M' →* R) (d : M') (b : A) :
    evalAt x h (AddMonoidAlgebra.single d b) = x b * h (Multiplicative.ofAdd d) := by
  simp [evalAt, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

lemma evalAt_ι (x : A →+* R) (h : Multiplicative M' →* R) (b : A) :
    evalAt x h (AddMonoidAlgebra.singleZeroRingHom b) = x b := by
  have := evalAt_single x h (0 : M') b
  simpa using this

lemma evalAt_id_eq_sum (p : AddMonoidAlgebra A M') :
    evalAt (RingHom.id _) 1 p = p.coeff.sum fun _ b => b := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | single d b => rw [evalAt_single]; simp

/-- `A → A[M][M]`. -/
noncomputable abbrev incl2 (A M' : Type*) [CommRing A] [AddCommGroup M'] :
    A →+* AddMonoidAlgebra (AddMonoidAlgebra A M') M' :=
  (AddMonoidAlgebra.singleZeroRingHom).comp AddMonoidAlgebra.singleZeroRingHom

/-- The inner variable of `A[M][M]`. -/
noncomputable abbrev innerX (A M' : Type*) [CommRing A] [AddCommGroup M'] :
    Multiplicative M' →* AddMonoidAlgebra (AddMonoidAlgebra A M') M' :=
  ((AddMonoidAlgebra.singleZeroRingHom :
    AddMonoidAlgebra A M' →+* AddMonoidAlgebra (AddMonoidAlgebra A M') M')).toMonoidHom.comp
    (AddMonoidAlgebra.of A M')

/-- The outer variable of `A[M][M]`. -/
noncomputable abbrev outerY (A M' : Type*) [CommRing A] [AddCommGroup M'] :
    Multiplicative M' →* AddMonoidAlgebra (AddMonoidAlgebra A M') M' :=
  AddMonoidAlgebra.of (AddMonoidAlgebra A M') M'

lemma innerX_ofAdd (e : M') : innerX A M' (Multiplicative.ofAdd e) =
    AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single e 1) := rfl

lemma outerY_ofAdd (e : M') : outerY A M' (Multiplicative.ofAdd e) =
    AddMonoidAlgebra.single e 1 := rfl

lemma coeff_eval_diag [DecidableEq M'] (p : AddMonoidAlgebra A M') (d : M') :
    (evalAt (incl2 A M') (innerX A M' * outerY A M') p).coeff d =
      AddMonoidAlgebra.single d (p.coeff d) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq, AddMonoidAlgebra.single_add]
  | single e b =>
    rw [evalAt_single]
    by_cases hed : e = d
    · subst hed
      simp [innerX_ofAdd, outerY_ofAdd, AddMonoidAlgebra.single_mul_single]
    · simp [innerX_ofAdd, outerY_ofAdd, AddMonoidAlgebra.single_mul_single, hed]

lemma eval_inner (q : AddMonoidAlgebra A M') :
    evalAt (incl2 A M') (innerX A M') q = AddMonoidAlgebra.singleZeroRingHom q := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single e b =>
    rw [evalAt_single]
    simp [innerX_ofAdd, AddMonoidAlgebra.single_mul_single]

lemma coeff_eval_coact [DecidableEq M'] (c : A →+* AddMonoidAlgebra A M')
    (p : AddMonoidAlgebra A M') (d : M') :
    (evalAt ((evalAt (incl2 A M') (innerX A M')).comp c) (outerY A M') p).coeff d =
      c (p.coeff d) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single e b =>
    rw [evalAt_single]
    by_cases hed : e = d
    · subst hed
      simp [eval_inner, outerY_ofAdd, AddMonoidAlgebra.single_mul_single]
    · simp [eval_inner, outerY_ofAdd, AddMonoidAlgebra.single_mul_single, hed]

end Eval

section Coaction

variable {U : BigFppfOver B S hS}
variable [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (act : AAction (fppfO B S hS) M (yoneda.obj U))

include hU in
lemma contains1 : B.Contains (Spec (.of (R1 U M))) := contains_M (contains_RT U)

include hU in
lemma contains2 : B.Contains (Spec (.of (R2 U M))) := contains_M (contains1 (U := U))

/-- A monoid map to `R` composed with a ring map `R → Γ(T)`. -/
noncomputable def secPt {T : BigFppfOver B S hS} {R : Type u} [CommRing R]
    (s : R →+* Γ((SCH).obj T, ⊤)) (z : Multiplicative M →* R) :
    Multiplicative M →* Γ((SCH).obj T, ⊤) where
  toFun m := s (z m)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]

/-- The action, with the group point written in `Γ(T)`. -/
noncomputable def smulAt {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (t : T ⟶ U) : T ⟶ U :=
  act.smul (F := yoneda.obj U) (U := op T) h t

omit hU [AddMonoid.FG M] in
lemma smulAt_one {T : BigFppfOver B S hS} (t : T ⟶ U) : smulAt act 1 t = t :=
  act.one_smul (F := yoneda.obj U) (U := op T) t

omit hU [AddMonoid.FG M] in
lemma smulAt_mul {T : BigFppfOver B S hS} (g h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) :
    smulAt act (g * h) t = smulAt act g (smulAt act h t) :=
  act.mul_smul (F := yoneda.obj U) (U := op T) g h t

omit hU [AddMonoid.FG M] in
lemma comp_smulAt {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) :
    τ ≫ smulAt act h t =
      smulAt act (secPt ((SCH).map τ).appTop.hom h) (τ ≫ t) :=
  act.map_smul (F := yoneda.obj U) τ.op h t

/-- The universal point of `D(M)`, over `Spec Γ(U)[M]`. -/
noncomputable abbrev univPt1 :
    Multiplicative M →* Γ((SCH).obj (spObj U (ι1 U (M := M)) contains1), ⊤) :=
  secPt (spSec U (ι1 U (M := M)) contains1) (AddMonoidAlgebra.of (RT U) M)

/-- The action morphism `Spec Γ(U)[M] → U`. -/
noncomputable def univMap : spObj U (ι1 U (M := M)) contains1 ⟶ U :=
  smulAt act univPt1 (spToT U (ι1 U (M := M)) contains1)

/-- The coaction `c : Γ(U) → Γ(U)[M]`. -/
noncomputable def coact : RT U →+* R1 U M :=
  ((RingEquiv.ofBijective _ (spSec_bijective U (ι1 U (M := M)) contains1)).symm : _ →+* _).comp
    ((SCH).map (univMap act)).appTop.hom

lemma spSec_coact (a : RT U) :
    spSec U (ι1 U) contains1 (coact act a) = ((SCH).map (univMap act)).appTop.hom a :=
  (RingEquiv.ofBijective _ (spSec_bijective U (ι1 U (M := M)) contains1)).apply_symm_apply _

omit act in
lemma exists_spLift {T : BigFppfOver B S hS} {R' : Type u} [CommRing R'] (ρ : RT U →+* R')
    (hC : B.Contains (Spec (.of R'))) (t : T ⟶ U) (ψ : R' →+* Γ((SCH).obj T, ⊤))
    (hψ : ψ.comp ρ = ((SCH).map t).appTop.hom) :
    ∃ τ : T ⟶ spObj U ρ hC, τ ≫ spToT U ρ hC = t ∧
      ∀ x, ((SCH).map τ).appTop.hom (spSec U ρ hC x) = ψ x :=
  ⟨spLift U ρ hC t ψ hψ, spLift_toT U ρ hC t ψ hψ, spLift_appTop U ρ hC t ψ hψ⟩

lemma smulAt_eq_comp {T : BigFppfOver B S hS} (t : T ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (τ : T ⟶ spObj U (ι1 U (M := M)) contains1)
    (hτ : τ ≫ spToT U (ι1 U (M := M)) contains1 = t)
    (hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := U)) = h) :
    smulAt act h t = τ ≫ univMap act := by
  subst hτ hres
  exact (comp_smulAt act τ _ _).symm

lemma appTop_comp_univMap {T : BigFppfOver B S hS} (τ : T ⟶ spObj U (ι1 U (M := M)) contains1)
    (a : RT U) :
    ((SCH).map (τ ≫ univMap act)).appTop.hom a =
      ((SCH).map τ).appTop.hom (spSec U (ι1 U) contains1 (coact act a)) := by
  rw [spSec_coact, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- **The universal formula**: the action on `t : T ⟶ U` is `a ↦ ∑ t(a_d) h(d)`. -/
theorem appTop_smul {T : BigFppfOver B S hS} (t : T ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (a : RT U) :
    ((SCH).map (smulAt act h t)).appTop.hom a =
      evalAt ((SCH).map t).appTop.hom h (coact act a) := by
  have hψ : (evalAt ((SCH).map t).appTop.hom h).comp (ι1 U (M := M)) = ((SCH).map t).appTop.hom :=
    RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 U M) (ι1 U) contains1 t _ hψ
  have hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := U)) = h := MonoidHom.ext fun m => by
    refine (hτ₂ _).trans ?_
    refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
    rw [map_one, one_mul]
    rfl
  rw [smulAt_eq_comp act t h τ hτ₁ hres, appTop_comp_univMap]
  exact hτ₂ _

/-- Counit: `∑ a_d = a`. -/
theorem sum_coact (a : RT U) : (coact act a).coeff.sum (fun _ b => b) = a := by
  have h := appTop_smul act (T := U) (𝟙 U) 1 a
  rw [smulAt_one, CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop] at h
  rw [← evalAt_id_eq_sum]
  exact h.symm

/-- Coassociativity, in the form: the component `a_d` of `a` has `c(a_d) = a_d X^d`. -/
theorem coact_coeff (a : RT U) (d : M) :
    coact act ((coact act a).coeff d) = AddMonoidAlgebra.single d ((coact act a).coeff d) := by
  classical
  let sec := spSec U (ι2 U (M := M)) contains2
  let t₂ := spToT U (ι2 U (M := M)) contains2
  let X : Multiplicative M →* R2 U M := innerX (RT U) M
  let Y : Multiplicative M →* R2 U M := outerY (RT U) M
  have ht₂ : ((SCH).map t₂).appTop.hom = sec.comp (ι2 U) :=
    RingHom.ext fun b => spToT_appTop U _ _ b
  have hmul := smulAt_mul act (secPt sec Y) (secPt sec X) t₂
  have hsec : ∀ (x : RT U →+* R2 U M) (z : Multiplicative M →* R2 U M) (p : R1 U M),
      evalAt (sec.comp x) (secPt sec z) p = sec (evalAt x z p) := by
    intro x z p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => rw [map_zero, map_zero, map_zero]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | single e b =>
      rw [evalAt_single, evalAt_single, map_mul]
      rfl
  have hh : ((SCH).map (smulAt act (secPt sec X) t₂)).appTop.hom =
      sec.comp ((evalAt (ι2 U) X).comp (coact act)) := by
    refine RingHom.ext fun b => ?_
    rw [appTop_smul, ht₂]
    exact hsec _ _ _
  have key := congrArg (fun z => ((SCH).map z).appTop.hom a) hmul
  rw [appTop_smul, appTop_smul act (smulAt act (secPt sec X) t₂) (secPt sec Y) a, hh, ht₂] at key
  have e₁ : secPt sec Y * secPt sec X = secPt sec (X * Y) := by
    ext m
    change sec (Y m) * sec (X m) = sec (X m * Y m)
    rw [map_mul, mul_comm]
  rw [e₁, hsec, hsec] at key
  have key' := (spSec_bijective U _ _).1 key
  have := congrArg (fun z : R2 U M => z.coeff d) key'
  simp only [X, Y] at this
  rw [coeff_eval_diag, coeff_eval_coact] at this
  exact this.symm

/-- Degree `d`: the `a` with `c a = a X^d`. -/
def homog (d : M) : AddSubgroup (RT U) where
  carrier := {a | coact act a = AddMonoidAlgebra.single d a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_neg, ha, AddMonoidAlgebra.single_neg]

/-- On homogeneous elements the action is multiplication by the character. -/
theorem appTop_smul_of_mem {T : BigFppfOver B S hS} (t : T ⟶ U)
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) {d : M} {a : RT U} (ha : a ∈ homog act d) :
    ((SCH).map (smulAt act h t)).appTop.hom a =
      ((SCH).map t).appTop.hom a * h (Multiplicative.ofAdd d) := by
  rw [appTop_smul, show coact act a = _ from ha, evalAt_single]

instance : SetLike.GradedMonoid (homog act) where
  one_mem := by
    change coact act 1 = _
    rw [map_one, AddMonoidAlgebra.one_def]
  mul_mem := by
    intro d e a b ha hb
    change coact act (a * b) = _
    rw [map_mul, show coact act a = _ from ha, show coact act b = _ from hb,
      AddMonoidAlgebra.single_mul_single]

theorem homog_internal [DecidableEq M] : DirectSum.IsInternal (homog act) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have key : ∀ (w : ⨁ d, homog act d) (d : M),
        (coact act (DirectSum.coeAddMonoidHom (homog act) w)).coeff d = (w d : RT U) := by
      intro w d
      induction w using DirectSum.induction_on with
      | zero => simp
      | of e x =>
        rw [DirectSum.coeAddMonoidHom_of, show coact act _ = _ from x.2]
        by_cases hed : e = d
        · subst hed; simp
        · simp [DirectSum.of_eq_of_ne, hed, Ne.symm hed]
      | add x y hx hy => simp [map_add, hx, hy]
    ext d
    have := key w d
    rw [hw, map_zero] at this
    simpa using this.symm
  · intro a
    refine ⟨∑ d ∈ (coact act a).coeff.support, DirectSum.of (fun d => homog act d) d
      ⟨(coact act a).coeff d, coact_coeff act a d⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact sum_coact act a

/-- The grading of `Γ(U)` attached to the action. -/
noncomputable def gradedRingOfAction [DecidableEq M] : GradedRing (homog act) :=
  { (inferInstance : SetLike.GradedMonoid (homog act)) with
    toDecomposition := (homog_internal act).chooseDecomposition }

end Coaction

end AlgMag.ChartMain
