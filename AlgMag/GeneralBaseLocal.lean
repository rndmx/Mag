/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseChart
import AlgMag.GeneralBaseGrading

/-!
# From an action to a grading, and Theorem 3.20 over an affine open of the base

See `AlgMag.GeneralBaseChart`.

## Main results

* `AlgMag.GB.gradingOf`, `AlgMag.GB.gradedAlgebraOf`, `AlgMag.GB.ptX_smul_of_mem`: Proposition 2.22.
* `AlgMag.GB.localEquiv`, `AlgMag.GB.toPoint_localEquiv_symm`: Theorem 3.20 over `U`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.GB

section Coaction

variable {R C D P : Type u} [CommRing R] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
  [AddCommMonoid P]

/-- The evaluation `C[P] → D` at a point of `𝔸(P)` over `C → D`. -/
def evP (t : C →ₐ[R] D) (a : Multiplicative P →* D) : AddMonoidAlgebra C P →ₐ[R] D :=
  AddMonoidAlgebra.liftNCAlgHom t a fun _ _ => Commute.all _ _

@[simp] lemma evP_single (t : C →ₐ[R] D) (a : Multiplicative P →* D) (n : P) (c : C) :
    evP t a (AddMonoidAlgebra.single n c) = t c * a (Multiplicative.ofAdd n) := by
  simp [evP, AddMonoidAlgebra.liftNC_single]

lemma comp_evP {D' : Type u} [CommRing D'] [Algebra R D'] (f : D →ₐ[R] D') (t : C →ₐ[R] D)
    (a : Multiplicative P →* D) :
    f.comp (evP t a) = evP (f.comp t) ((f : D →* D').comp a) := by
  refine AlgHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n c => simp

variable {M A : Type u} [AddCommMonoid M] [CommRing A] [Algebra R A]

/-- The point `(m, k) ↦ X^{(m, 0)}` of `𝔸(M)` over `A[M × M]`. -/
def hOne (A M : Type u) [CommRing A] [AddCommMonoid M] :
    Multiplicative M →* AddMonoidAlgebra A (M × M) :=
  (AddMonoidAlgebra.of A (M × M)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M M))

/-- The point `(m, k) ↦ X^{(0, k)}` of `𝔸(M)` over `A[M × M]`. -/
def hTwo (A M : Type u) [CommRing A] [AddCommMonoid M] :
    Multiplicative M →* AddMonoidAlgebra A (M × M) :=
  (AddMonoidAlgebra.of A (M × M)).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M M))

lemma hOne_apply (m : Multiplicative M) :
    hOne A M m = AddMonoidAlgebra.single (Multiplicative.toAdd m, 0) 1 := rfl

lemma hTwo_apply (m : Multiplicative M) :
    hTwo A M m = AddMonoidAlgebra.single (0, Multiplicative.toAdd m) 1 := rfl

lemma coeff_ev_mul (x : AddMonoidAlgebra A M) (m k : M) :
    (evP (constAlg (R := R) (M × M) A) (hOne A M * hTwo A M) x).coeff (m, k) =
      if m = k then x.coeff m else 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    split_ifs <;> simp
  | single n c =>
    rw [evP_single, MonoidHom.mul_apply, hOne_apply, hTwo_apply, constAlg_apply]
    simp only [AddMonoidAlgebra.single_mul_single, toAdd_ofAdd, Prod.mk_add_mk, add_zero, zero_add,
      mul_one, one_mul, AddMonoidAlgebra.coeff_single]
    by_cases h : n = m
    · subst h
      by_cases h' : n = k
      · subst h'; simp
      · have : (n, n) ≠ (n, k) := fun e => h' (congrArg Prod.snd e)
        simp [h', Finsupp.single_eq_of_ne, this, Ne.symm this]
    · have : (n, n) ≠ (m, k) := fun e => h (congrArg Prod.fst e)
      rw [Finsupp.single_eq_of_ne (Ne.symm this), Finsupp.single_eq_of_ne (Ne.symm h)]
      simp

lemma coeff_ev_two_mul (w : AddMonoidAlgebra A M) (n m k : M) :
    (evP (constAlg (R := R) (M × M) A) (hTwo A M) w *
      AddMonoidAlgebra.single (n, 0) 1).coeff (m, k) = if n = m then w.coeff k else 0 := by
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    split_ifs <;> simp
  | single j c =>
    rw [evP_single, hTwo_apply, constAlg_apply]
    simp only [AddMonoidAlgebra.single_mul_single, toAdd_ofAdd, Prod.mk_add_mk, add_zero, zero_add,
      mul_one, AddMonoidAlgebra.coeff_single]
    by_cases h : n = m
    · subst h
      by_cases h' : j = k
      · subst h'; simp
      · have : (n, j) ≠ (n, k) := fun e => h' (congrArg Prod.snd e)
        simp [Finsupp.single_eq_of_ne, h', this, Ne.symm h', Ne.symm this]
    · have : (n, j) ≠ (m, k) := fun e => h (congrArg Prod.fst e)
      rw [Finsupp.single_eq_of_ne (Ne.symm this)]
      simp [h]

variable (ρ : A →ₐ[R] AddMonoidAlgebra A M)

lemma coeff_ev_rho (x : AddMonoidAlgebra A M) (m k : M) :
    (evP ((evP (constAlg (R := R) (M × M) A) (hTwo A M)).comp ρ) (hOne A M) x).coeff (m, k) =
      (ρ (x.coeff m)).coeff k := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
  | single n c =>
    rw [evP_single, hOne_apply]
    simp only [AlgHom.comp_apply, toAdd_ofAdd]
    rw [coeff_ev_two_mul, AddMonoidAlgebra.coeff_single]
    by_cases h : n = m
    · subst h; simp
    · rw [Finsupp.single_eq_of_ne (Ne.symm h), if_neg h]
      simp

/-- **Proposition 2.22**, from a coaction to a grading: `A_m = {a | ρ a = a X^m}`. -/
def coactGrading (m : M) : Submodule R A where
  carrier := {a | ρ a = AddMonoidAlgebra.single m a}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
  zero_mem' := by simp
  smul_mem' r a ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, ha, AddMonoidAlgebra.smul_single]

variable {ρ}

lemma mem_coactGrading {m : M} {a : A} :
    a ∈ coactGrading ρ m ↔ ρ a = AddMonoidAlgebra.single m a := Iff.rfl

/-- **Proposition 2.22**: a coaction `ρ : A → A[M]` of the bialgebra `ℤ[M]`, given by the counit
and coassociativity identities, is a grading of `A`. -/
def coactGradedAlgebra
    (hcounit : ((AddMonoidAlgebra.liftNCAlgHom (AlgHom.id R A) (1 : Multiplicative M →* A)
      fun _ _ => Commute.all _ _)).comp ρ = AlgHom.id R A)
    (hco : (evP (constAlg (R := R) (M × M) A) (hOne A M * hTwo A M)).comp ρ =
      (evP ((evP (constAlg (R := R) (M × M) A) (hTwo A M)).comp ρ) (hOne A M)).comp ρ) :
    GradedAlgebra (coactGrading ρ) := by
  have hsum : ∀ a : A, ((ρ a).coeff.sum fun _ c => c) = a := by
    intro a
    have h := DFunLike.congr_fun hcounit a
    have key : ∀ x : AddMonoidAlgebra A M, (AddMonoidAlgebra.liftNCAlgHom (AlgHom.id R A)
        (1 : Multiplicative M →* A) fun _ _ => Commute.all _ _) x = x.coeff.sum fun _ c => c := by
      intro x
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy =>
        rw [map_add, hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
      | single n c =>
        simp [AddMonoidAlgebra.liftNC_single]
    rw [← key]
    exact h
  have hmem : ∀ (a : A) (m : M), (ρ a).coeff m ∈ coactGrading ρ m := by
    intro a m
    rw [mem_coactGrading]
    refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun k => ?_)
    have h := DFunLike.congr_fun hco a
    have h2 := congrArg (fun x => AddMonoidAlgebra.coeff x (m, k)) h
    simp only [AlgHom.comp_apply] at h2
    rw [coeff_ev_mul, coeff_ev_rho] at h2
    rw [← h2, AddMonoidAlgebra.coeff_single]
    by_cases e : m = k
    · subst e; simp
    · rw [if_neg e, Finsupp.single_eq_of_ne (Ne.symm e)]
  have hint : DirectSum.IsInternal (coactGrading ρ) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h : ∀ (y : DirectSum M fun m => coactGrading ρ m) (k : M),
          (ρ (DirectSum.coeAddMonoidHom (coactGrading ρ) y)).coeff k = (y k : A) := by
        intro y k
        induction y using DirectSum.induction_on with
        | zero => simp
        | of m x =>
          rw [DirectSum.coeAddMonoidHom_of, mem_coactGrading.mp x.2, AddMonoidAlgebra.coeff_single]
          by_cases e : m = k
          · subst e
            simp
          · rw [Finsupp.single_eq_of_ne (Ne.symm e), DirectSum.of_eq_of_ne _ _ _ (Ne.symm e)]
            rfl
        | add x y hx hy =>
          rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
          rfl
      refine DFinsupp.ext fun k => Subtype.ext ?_
      have := h x k
      rw [hx, map_zero] at this
      exact this.symm
    · intro a
      refine ⟨∑ m ∈ (ρ a).coeff.support, DirectSum.of (fun m => coactGrading ρ m) m
        ⟨(ρ a).coeff m, hmem a m⟩, ?_⟩
      rw [map_sum]
      simp only [DirectSum.coeAddMonoidHom_of]
      exact hsum a
  exact
    { one_mem := by
        change ρ 1 = AddMonoidAlgebra.single 0 1
        rw [map_one]
        rfl
      mul_mem := by
        intro i j a b ha hb
        change ρ (a * b) = AddMonoidAlgebra.single (i + j) (a * b)
        rw [map_mul, mem_coactGrading.mp ha, mem_coactGrading.mp hb,
          AddMonoidAlgebra.single_mul_single]
      toDecomposition := hint.chooseDecomposition }

end Coaction

section Action

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U) {M : Type u} [AddCommMonoid M]

/-- Points of `𝔸(P)` with values in `Γ(T, ⊤)`, in the notation of the chart. -/
def toGa {P : Type u} [AddCommMonoid P] {T : Over S} (hT : LiesOver T U)
    (h : APt (overO S) P (op T)) : Multiplicative P →* Ga hU T hT := h

/-- The inverse of `AlgMag.GB.toGa`. -/
def ofGa {P : Type u} [AddCommMonoid P] {T : Over S} (hT : LiesOver T U)
    (h : Multiplicative P →* Ga hU T hT) : APt (overO S) P (op T) := h

variable (X : Over S) [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))

/-- The algebra `A[P]` over `R`. -/
abbrev Aover (X : Over S) (U : S.Opens) (P : Type u) [AddCommMonoid P] : CommAlgCat.{u} Γ(S, U) :=
  CommAlgCat.of Γ(S, U) (AddMonoidAlgebra (Aalg X U) P)

/-- The constant morphism `A → A[P]`, read as a point of `X` over `Spec A[P]`. -/
def xConst (P : Type u) [AddCommMonoid P] : Phi hU (Aover X U P) ⟶ X :=
  (ptX X hU _ (liesOver_Phi hU _)).symm ((eta hU (Aover X U P)).comp (constAlg P (Aalg X U)))

/-- The universal point of `𝔸(M)` over `Spec A[M]`. -/
def hUniv : APt (overO S) M (op (Phi hU (Aover X U M))) :=
  ofGa hU (liesOver_Phi hU _) (((eta hU (Aover X U M)) : Aover X U M →* _).comp
    (AddMonoidAlgebra.of (Aalg X U) M))

variable {X} in
/-- The coaction `ρ : A → A[M]` of the action: the image of the universal pair. -/
def rho : Aalg X U →ₐ[Γ(S, U)] AddMonoidAlgebra (Aalg X U) M :=
  ((etaEquiv hU (Aover X U M)).symm.toAlgHom).comp
    (ptX X hU _ (liesOver_Phi hU _) (act.smul (hUniv hU X) (xConst hU X M)))

lemma eta_rho : (eta hU (Aover X U M)).comp (rho hU act) =
    ptX X hU _ (liesOver_Phi hU _) (act.smul (hUniv hU X) (xConst hU X M)) := by
  refine AlgHom.ext fun a => ?_
  exact (etaEquiv hU (Aover X U M)).apply_symm_apply _

/-- The action on arbitrary points over `U`, through the coaction: for `T` over `U`, affine or not,
`h • x` is `A → A[M] → Γ(T, ⊤)`, the second map being evaluation at `(x, h)`. -/
theorem ptX_smul {T : Over S} (hT : LiesOver T U) (h : APt (overO S) M (op T)) (x : T ⟶ X) :
    ptX X hU T hT (act.smul h x) = (evP (ptX X hU T hT x) (toGa hU hT h)).comp (rho hU act) := by
  let e : Aover X U M →ₐ[Γ(S, U)] Ga hU T hT := evP (R := Γ(S, U)) (ptX X hU T hT x) (toGa hU hT h)
  let c : T ⟶ Phi hU (Aover X U M) := (homPhi hU T hT (Aover X U M)).symm e
  have hc : (gpull hU (liesOver_Phi hU _) hT c).comp (eta hU (Aover X U M)) = e := by
    rw [eta, ← homPhi_comp, Category.comp_id]
    exact (homPhi hU T hT (Aover X U M)).apply_symm_apply e
  have h1 : APt.res c.op (hUniv hU X) = h := by
    refine MonoidHom.ext fun m => ?_
    have := DFunLike.congr_fun hc (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1)
    refine this.trans ?_
    rw [evP_single, map_one, one_mul]
    rfl
  have h2 : c ≫ xConst hU X M = x := by
    apply (ptX X hU T hT).injective
    rw [ptX_comp X hU (liesOver_Phi hU _) hT, xConst, Equiv.apply_symm_apply, ← AlgHom.comp_assoc,
      hc]
    refine AlgHom.ext fun a => ?_
    change e (AddMonoidAlgebra.single 0 a) = _
    rw [evP_single]
    change _ * (toGa hU hT h) 1 = _
    rw [map_one, mul_one]
  have key := act.map_smul c.op (hUniv hU X) (xConst hU X M)
  rw [h1] at key
  have key' : c ≫ act.smul (hUniv hU X) (xConst hU X M) = act.smul h (c ≫ xConst hU X M) := key
  rw [h2] at key'
  rw [← key']
  refine (ptX_comp X hU (liesOver_Phi hU _) hT c (act.smul (hUniv hU X) (xConst hU X M))).trans ?_
  rw [← eta_rho, ← AlgHom.comp_assoc, hc]

variable {X} in
/-- **Proposition 2.22** (over `U`): the coaction is counital. -/
lemma rho_counit : ((AddMonoidAlgebra.liftNCAlgHom (AlgHom.id Γ(S, U) (Aalg X U))
    (1 : Multiplicative M →* Aalg X U) fun _ _ => Commute.all _ _)).comp (rho hU act) =
    AlgHom.id _ _ := by
  have hT := liesOver_Phi hU (Aalg X U)
  have h1 := ptX_smul hU X act hT 1 (iotaX X hU)
  rw [act.one_smul] at h1
  have h0 : ptX X hU _ hT (iotaX X hU) = eta hU (Aalg X U) := by
    change homPhi hU _ hT _ (toChart X hU _ hT (iotaX X hU)) = _
    congr 1
    apply (toChart X hU _ hT).symm.injective
    rw [Equiv.symm_apply_apply]
    exact (Category.id_comp _).symm
  rw [h0] at h1
  refine AlgHom.ext fun a => (eta_bijective hU (Aalg X U)).1 ?_
  have h2 := DFunLike.congr_fun h1 a
  refine Eq.trans ?_ h2.symm
  have h3 : ∀ y : AddMonoidAlgebra (Aalg X U) M, eta hU (Aalg X U) ((AddMonoidAlgebra.liftNCAlgHom
      (AlgHom.id Γ(S, U) (Aalg X U)) (1 : Multiplicative M →* Aalg X U)
      fun _ _ => Commute.all _ _) y) = evP (eta hU (Aalg X U)) (toGa hU hT 1) y := by
    intro y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n c =>
      rw [evP_single]
      simp [AddMonoidAlgebra.liftNC_single]
      rw [show toGa hU hT (1 : APt (overO S) M _) (Multiplicative.ofAdd n) = 1 from rfl, mul_one]
  exact h3 _

variable {X} in
/-- **Proposition 2.22** (over `U`): the coaction is coassociative. -/
lemma rho_coassoc :
    (evP (constAlg (R := Γ(S, U)) (M × M) (Aalg X U)) (hOne (Aalg X U) M * hTwo (Aalg X U) M)).comp
        (rho hU act) =
      (evP ((evP (constAlg (R := Γ(S, U)) (M × M) (Aalg X U)) (hTwo (Aalg X U) M)).comp
        (rho hU act)) (hOne (Aalg X U) M)).comp (rho hU act) := by
  let D := Aover X U (M × M)
  have hT := liesOver_Phi hU D
  let η : D →ₐ[Γ(S, U)] Ga hU (Phi hU D) hT := eta hU D
  let y : Aalg X U →ₐ[Γ(S, U)] Ga hU (Phi hU D) hT := η.comp (constAlg (M × M) (Aalg X U))
  let x : Phi hU D ⟶ X := (ptX X hU _ hT).symm y
  let h₁ : APt (overO S) M (op (Phi hU D)) := ofGa hU hT ((η : D →* _).comp (hOne (Aalg X U) M))
  let h₂ : APt (overO S) M (op (Phi hU D)) := ofGa hU hT ((η : D →* _).comp (hTwo (Aalg X U) M))
  have hm := congrArg (ptX X hU _ hT) (act.mul_smul h₁ h₂ x)
  rw [ptX_smul hU X act hT, ptX_smul hU X act hT, ptX_smul hU X act hT, Equiv.apply_symm_apply] at hm
  refine AlgHom.ext fun a => (eta_bijective hU D).1 ?_
  have h2 := DFunLike.congr_fun hm a
  have e1 : (η.comp (evP (constAlg (R := Γ(S, U)) (M × M) (Aalg X U))
      (hOne (Aalg X U) M * hTwo (Aalg X U) M))) = evP y (toGa hU hT (h₁ * h₂)) := by
    rw [comp_evP]
    congr 1
    exact MonoidHom.ext fun m => map_mul η _ _
  have e2 : (η.comp (evP (constAlg (R := Γ(S, U)) (M × M) (Aalg X U)) (hTwo (Aalg X U) M))) =
      evP y (toGa hU hT h₂) := comp_evP _ _ _
  have e3 : η.comp (evP ((evP (constAlg (R := Γ(S, U)) (M × M) (Aalg X U)) (hTwo (Aalg X U) M)).comp
        (rho hU act)) (hOne (Aalg X U) M)) =
      evP ((evP y (toGa hU hT h₂)).comp (rho hU act)) (toGa hU hT h₁) := by
    rw [comp_evP, ← AlgHom.comp_assoc, e2]
    rfl
  have e1' := DFunLike.congr_fun e1 (rho hU act a)
  have e3' := DFunLike.congr_fun e3 (rho hU act a)
  exact e1'.trans (h2.trans e3'.symm)

variable {X} in
/-- **Proposition 2.22** (over the affine open `U` of `S`): the components `A_m` of `A = Γ(X, p⁻¹ U)`
defined by the action of `𝔸(M)_S` on `X`. -/
def gradingOf : M → Submodule Γ(S, U) (Aalg X U) := coactGrading (rho hU act)

variable {X} in
/-- **Proposition 2.22** (over the affine open `U` of `S`): an action of `𝔸(M)_S` on `X`, affine over
`S`, is an `M`-grading of `A = Γ(X, p⁻¹ U)`. -/
@[instance_reducible]
def gradedAlgebraOf : GradedAlgebra (gradingOf hU act) :=
  coactGradedAlgebra (rho_counit hU act) (rho_coassoc hU act)

attribute [local instance] gradedAlgebraOf

variable {X} in
/-- **Proposition 2.22**: on the component `A_m`, `(h • x)(a) = x(a) h(m)`, for every point `(x, h)`
over any `T` over `U`. So the action is determined by the grading. -/
theorem ptX_smul_of_mem {T : Over S} (hT : LiesOver T U) (h : APt (overO S) M (op T)) (x : T ⟶ X)
    {m : M} {a : Aalg X U} (ha : a ∈ gradingOf hU act m) :
    ptX X hU T hT (act.smul h x) a =
      toGa hU hT h (Multiplicative.ofAdd m) * ptX X hU T hT x a := by
  rw [ptX_smul hU X act hT]
  change evP _ _ (rho hU act a) = _
  rw [mem_coactGrading.mp ha, evP_single, mul_comm]

end Action

end AlgMag.GB
