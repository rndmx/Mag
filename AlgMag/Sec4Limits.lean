/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6FPR
import AlgMag.Sec3Functorial
import StacksFrontier.AlgebraicGeometry.Size.Pullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Attractors with prescribed limits

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §4.

`Z` is an `S`-functor with a monomorphism to `X^F`. The attractor lives in a larger universe than
algebraic spaces (see `AlgMag.Representation`), so `Z` is allowed in any universe and the morphism
`Z → X^F` is given as a natural family of maps on points, `AlgMag.PointMap`.
-/

open CategoryTheory Opposite Limits AlgebraicGeometry

universe w v u

namespace AlgMag

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommMonoid M] {X : Cᵒᵖ ⥤ Type u} {act : AAction 𝒪 M X}
variable {N F : AddSubmonoid M}

/-- A morphism `Z → X^F` of `S`-functors, possibly in different universes, on points. -/
structure PointMap (Z : Cᵒᵖ ⥤ Type w) (act : AAction 𝒪 M X) (F : AddSubmonoid M) where
  /-- The map on `T`-points. -/
  toFun : ∀ T : Cᵒᵖ, Z.obj T → AttractorPt act F (unop T)
  naturality : ∀ {T T' : Cᵒᵖ} (s : T ⟶ T') (z : Z.obj T),
    toFun T' (Z.map s z) = AttractorPt.baseChange s.unop (toFun T z)

/-- `Z → X^F` is a monomorphism of functors: it is injective on points. -/
def PointMap.IsMono {Z : Cᵒᵖ ⥤ Type w} (i : PointMap Z act F) : Prop :=
  ∀ T, Function.Injective (i.toFun T)

variable (act) in
/-- **Definition 4.1.** The attractor `X^N_{F,Z}` with prescribed limit in `Z` relatively to the
face `F` of `N`: the points of `X^N` whose image in `X^F` belongs to `Z`. -/
noncomputable def prescribedLimit (hF : IsFace F N) {Z : Cᵒᵖ ⥤ Type w} (i : PointMap Z act F) :
    Subfunctor (attractor act N) where
  obj T := {f | ∃ z : Z.obj T, i.toFun T z = AttractorPt.ofFace hF (f : AttractorPt act N (unop T))}
  map {T T'} s f := by
    rintro ⟨z, hz⟩
    exact ⟨Z.map s z, by rw [i.naturality, hz]; rfl⟩

/-- **Definition 4.1**, case `F = N`: `IsFace N N`, used for the notation `X^N_Z`. -/
theorem isFace_refl (N : AddSubmonoid M) : IsFace N N :=
  ⟨le_rfl, fun hx hy _ => ⟨hx, hy⟩⟩

/-- **Proposition 4.2**, on points and in arbitrary universes:
`X^N_{F,Z}(T) = X^N(T) ×_{X^F(T)} Z(T)`. -/
noncomputable def prescribedLimitEquiv (hF : IsFace F N) {Z : Cᵒᵖ ⥤ Type w} (i : PointMap Z act F)
    (hi : i.IsMono) (T : Cᵒᵖ) :
    (prescribedLimit act hF i).obj T ≃
      {p : AttractorPt act N (unop T) × Z.obj T // AttractorPt.ofFace hF p.1 = i.toFun T p.2} where
  toFun f := ⟨(f.1, f.2.choose), f.2.choose_spec.symm⟩
  invFun p := ⟨p.1.1, p.1.2, p.2.symm⟩
  left_inv _ := rfl
  right_inv p := by
    refine Subtype.ext (Prod.ext rfl (hi T ?_))
    exact (Exists.choose_spec (p := fun z => i.toFun T z = AttractorPt.ofFace hF p.1.1)
      ⟨p.1.2, p.2.symm⟩).trans p.2

/-- The `PointMap` underlying a morphism of functors in the universe of the attractor. -/
def PointMap.ofHom {Z : Cᵒᵖ ⥤ Type _} (i : Z ⟶ attractor act F) : PointMap Z act F where
  toFun T z := i.app T z
  naturality s z := hom_naturality_apply i s z

/-- **Proposition 4.2.** For a monomorphism `Z ⟶ X^F` of functors,
`X^N_{F,Z} ≅ X^N ×_{X^F} Z`; the fibre product is the categorical one by
`AlgMag.isPullback_fibreProduct`. -/
noncomputable def prescribedLimitIso (hF : IsFace F N) {Z : Cᵒᵖ ⥤ Type _}
    (i : Z ⟶ attractor act F) [Mono i] :
    (prescribedLimit act hF (PointMap.ofHom i)).toFunctor ≅ fibreProduct (faceMap act hF) i :=
  have hi : (PointMap.ofHom i).IsMono := fun T =>
    (mono_iff_injective (i.app T)).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance T)
  NatIso.ofComponents
    (fun T => (((prescribedLimitEquiv hF (PointMap.ofHom i) hi T).trans
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun p => ⟨p.1, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })).toIso)
    (fun {T T'} s => by
      ext f
      refine Subtype.ext (Prod.ext rfl (hi T' ?_))
      refine (Exists.choose_spec (((prescribedLimit act hF (PointMap.ofHom i)).toFunctor.map s
        f).2)).trans ?_
      refine Eq.trans ?_ ((PointMap.ofHom i).naturality s _).symm
      refine Eq.trans ?_ (congrArg (AttractorPt.baseChange s.unop)
        (Exists.choose_spec f.2).symm)
      rfl)

/-- **Fact 4.3**, first assertion: the canonical morphism `X^N_{F,Z} → X^N` is a monomorphism.
By the construction of Definition 4.1 this needs neither separatedness nor `Z → X^F` mono. -/
theorem mono_prescribedLimit_ι (hF : IsFace F N) {Z : Cᵒᵖ ⥤ Type w} (i : PointMap Z act F) :
    Mono (prescribedLimit act hF i).ι :=
  inferInstance


section MonAffSec

/-- `ℤ[P]`, in the universe of `P`. -/
noncomputable abbrev ZMon (P : Type u) [AddCommMonoid P] : CommRingCat.{u} :=
  .of (AddMonoidAlgebra (ULift.{u} ℤ) P)

/-- The scheme `𝔸(P)_T = T ×_ℤ Spec ℤ[P]` (Definition 2.3). -/
noncomputable def MonAff (P : Type u) [AddCommMonoid P] (T : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from T) (terminal.from (Spec (ZMon P)))

namespace MonAff

variable {P : Type u} [AddCommMonoid P] {T : Scheme.{u}}

lemma zmon_ext {R : CommRingCat.{u}} {f g : ZMon P ⟶ R}
    (h : ∀ p : P, f.hom (AddMonoidAlgebra.single p 1) = g.hom (AddMonoidAlgebra.single p 1)) :
    f = g := by
  refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext ?_ h)
  rintro ⟨r⟩
  have key : ∀ k : AddMonoidAlgebra (ULift.{u} ℤ) P →+* R,
      k (AddMonoidAlgebra.single 0 (ULift.up r)) = (r : R) := by
    intro k
    let c : ℤ →+* R := k.comp ((AddMonoidAlgebra.singleZeroRingHom :
      ULift.{u} ℤ →+* AddMonoidAlgebra (ULift.{u} ℤ) P).comp
        (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom)
    exact eq_intCast c r
  exact (key f.hom).trans (key g.hom).symm

/-- The ring map `ℤ[P] → R` attached to a point `a` of `𝔸(P)` with values in `R`. -/
noncomputable def zmonLift {R : Type u} [CommRing R] (a : Multiplicative P →* R) :
    AddMonoidAlgebra (ULift.{u} ℤ) P →+* R :=
  AddMonoidAlgebra.liftNCRingHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom) a
    (fun _ _ => mul_comm _ _)

@[simp] lemma zmonLift_single {R : Type u} [CommRing R] (a : Multiplicative P →* R) (p : P) :
    zmonLift a (AddMonoidAlgebra.single p 1) = a (Multiplicative.ofAdd p) := by
  simp [zmonLift]

/-- Morphisms to `Spec ℤ[P]` are the points of `𝔸(P)`. -/
noncomputable def toSpecEquiv {X : Scheme.{u}} :
    (X ⟶ Spec (ZMon P)) ≃ (Multiplicative P →* Γ(X, ⊤)) where
  toFun f :=
    { toFun := fun p => f.appTop ((Scheme.ΓSpecIso (ZMon P)).inv
        (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1))
      map_one' := by
        have : (AddMonoidAlgebra.single (Multiplicative.toAdd (1 : Multiplicative P)) (1 : ULift.{u} ℤ)) =
          (1 : AddMonoidAlgebra (ULift.{u} ℤ) P) := rfl
        rw [this]
        erw [map_one, map_one]
      map_mul' := fun p q => by
        have : (AddMonoidAlgebra.single (Multiplicative.toAdd (p * q)) (1 : ULift.{u} ℤ)) =
          AddMonoidAlgebra.single (Multiplicative.toAdd p) 1 *
            (AddMonoidAlgebra.single (Multiplicative.toAdd q) 1 :
              AddMonoidAlgebra (ULift.{u} ℤ) P) := by
          rw [AddMonoidAlgebra.single_mul_single, mul_one]; rfl
        rw [this]
        erw [map_mul, map_mul] }
  invFun a := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (zmonLift a))
  left_inv f := by
    apply (ΓSpec.adjunction.homEquiv _ _).symm.injective
    apply Quiver.Hom.unop_inj
    rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
    dsimp
    simp only [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    apply zmon_ext
    intro p
    change zmonLift _ _ = _
    rw [zmonLift_single]
    rfl
  right_inv a := by
    ext p
    simp [zmonLift_single]

lemma toSpecEquiv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (ZMon P)) (p) :
    toSpecEquiv (f ≫ g) p = f.appTop (toSpecEquiv g p) := rfl

variable (P T) in
/-- The structure morphism `𝔸(P)_T → T`. -/
noncomputable def π : MonAff P T ⟶ T := pullback.fst _ _

variable (P T) in
/-- The projection `𝔸(P)_T → Spec ℤ[P]`. -/
noncomputable def toSpec : MonAff P T ⟶ Spec (ZMon P) := pullback.snd _ _

variable (P T) in
/-- The universal point of `𝔸(P)` on `𝔸(P)_T`. -/
noncomputable def coord : Multiplicative P →* Γ(MonAff P T, ⊤) :=
  toSpecEquiv (toSpec P T)

/-- A morphism to `𝔸(P)_T` from a morphism to `T` and a point of `𝔸(P)`. -/
noncomputable def homOf {X : Scheme.{u}} (f : X ⟶ T) (a : Multiplicative P →* Γ(X, ⊤)) :
    X ⟶ MonAff P T :=
  pullback.lift f (toSpecEquiv.symm a) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] lemma homOf_π {X : Scheme.{u}} (f : X ⟶ T)
    (a : Multiplicative P →* Γ(X, ⊤)) : homOf f a ≫ π P T = f :=
  pullback.lift_fst _ _ _

lemma homOf_coord {X : Scheme.{u}} (f : X ⟶ T) (a : Multiplicative P →* Γ(X, ⊤)) (p) :
    (homOf f a).appTop (coord P T p) = a p := by
  rw [coord, ← toSpecEquiv_comp]
  have : homOf f a ≫ toSpec P T = toSpecEquiv.symm a := pullback.lift_snd _ _ _
  rw [this, Equiv.apply_symm_apply]

lemma hom_ext' {X : Scheme.{u}} {f g : X ⟶ MonAff P T} (h₁ : f ≫ π P T = g ≫ π P T)
    (h₂ : ∀ p, f.appTop (coord P T p) = g.appTop (coord P T p)) : f = g := by
  refine pullback.hom_ext h₁ ?_
  change f ≫ toSpec P T = g ≫ toSpec P T
  refine toSpecEquiv.injective (MonoidHom.ext fun p => ?_)
  rw [toSpecEquiv_comp, toSpecEquiv_comp]
  exact h₂ p

/-- The ring map `Γ(T)[P] → Γ(𝔸(P)_T)`. -/
noncomputable def evalRing (P : Type u) [AddCommMonoid P] (T : Scheme.{u}) :
    AddMonoidAlgebra Γ(T, ⊤) P →+* Γ(MonAff P T, ⊤) :=
  AddMonoidAlgebra.liftNCRingHom ((π P T).appTop).hom (coord P T) (fun _ _ => mul_comm _ _)

@[simp] lemma evalRing_single_one (p : P) :
    evalRing P T (AddMonoidAlgebra.single p 1) = coord P T (Multiplicative.ofAdd p) := by
  change AddMonoidAlgebra.liftNC _ _ _ = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp

@[simp] lemma evalRing_single_zero (r : Γ(T, ⊤)) :
    evalRing P T (AddMonoidAlgebra.single 0 r) = (π P T).appTop r := by
  change AddMonoidAlgebra.liftNC _ _ _ = _
  rw [AddMonoidAlgebra.liftNC_single]
  simp

lemma toSpecΓ_map_appTop (X : Scheme.{u}) {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, ⊤)) (x : R) :
    (X.toSpecΓ ≫ Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = φ x := by
  have e : (X.toSpecΓ ≫ Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ := by
    simp [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  rw [e]
  simp

lemma isoSpec_inv_appTop (T : Scheme.{u}) [IsAffine T] (r : Γ(T, ⊤)) :
    T.isoSpec.inv.appTop r = (Scheme.ΓSpecIso Γ(T, ⊤)).inv r := by
  have h : T.isoSpec.hom ≫ T.isoSpec.inv = 𝟙 T := Iso.hom_inv_id _
  have e : T.isoSpec.hom.appTop (T.isoSpec.inv.appTop r) = r := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  have e2 : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).hom := by
    simp [Scheme.isoSpec]
  rw [e2] at e
  have e3 := congrArg (Scheme.ΓSpecIso Γ(T, ⊤)).inv e
  simpa using e3

set_option backward.isDefEq.respectTransparency.types false in
variable (P T) in
/-- `𝔸(P)_T = Spec Γ(T)[P]` for affine `T`. -/
noncomputable def isoOfIsAffine [IsAffine T] :
    MonAff P T ≅ Spec (.of (AddMonoidAlgebra Γ(T, ⊤) P)) where
  hom := (MonAff P T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalRing P T))
  inv := homOf (Spec.map (CommRingCat.ofHom AddMonoidAlgebra.singleZeroRingHom) ≫ T.isoSpec.inv)
    (((Scheme.ΓSpecIso (.of (AddMonoidAlgebra Γ(T, ⊤) P))).inv.hom.toMonoidHom).comp
      (AddMonoidAlgebra.of Γ(T, ⊤) P))
  hom_inv_id := by
    refine hom_ext' ?_ ?_
    · simp only [Category.assoc, homOf_π, Category.id_comp]
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      have : (evalRing P T).comp AddMonoidAlgebra.singleZeroRingHom = ((π P T).appTop).hom := by
        ext r; simp [evalRing]
      rw [this, CommRingCat.ofHom_hom, ← Scheme.toSpecΓ_naturality_assoc]
      simp [Scheme.isoSpec]
    · intro p
      rw [Scheme.Hom.id_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOf_coord]
      refine (toSpecΓ_map_appTop _ (CommRingCat.ofHom (evalRing P T)) _).trans ?_
      exact evalRing_single_one _
  inv_hom_id := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, Scheme.Hom.comp_app, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, Category.assoc, Scheme.Hom.id_app, ← Iso.eq_inv_comp,
      Category.comp_id]
    ext : 1
    refine AddMonoidAlgebra.ringHom_ext ?_ ?_
    · intro r
      change ((homOf _ _).appTop) (evalRing P T (AddMonoidAlgebra.single 0 r)) = _
      rw [evalRing_single_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOf_π,
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply, isoSpec_inv_appTop,
        ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    · intro p
      change ((homOf _ _).appTop) (evalRing P T (AddMonoidAlgebra.single p 1)) = _
      rw [evalRing_single_one, homOf_coord]
      rfl

lemma evalRing_bijective [IsAffine T] : Function.Bijective (evalRing P T) := by
  have e : ∀ x, evalRing P T x = (isoOfIsAffine P T).hom.appTop
      ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra Γ(T, ⊤) P))).inv x) := fun x =>
    (toSpecΓ_map_appTop _ (CommRingCat.ofHom (evalRing P T)) x).symm
  have : (evalRing P T : _ → _) = (isoOfIsAffine P T).hom.appTop ∘
      (Scheme.ΓSpecIso (.of (AddMonoidAlgebra Γ(T, ⊤) P))).inv := funext e
  rw [this]
  have : IsIso (isoOfIsAffine P T).hom.appTop :=
    inferInstanceAs (IsIso ((isoOfIsAffine P T).hom.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _)

/-- The morphism `𝔸(P')_T → 𝔸(P)_T` dual to `g : P →+ P'`. -/
noncomputable def reindex {P' : Type u} [AddCommMonoid P'] (g : P →+ P') (T : Scheme.{u}) :
    MonAff P' T ⟶ MonAff P T :=
  homOf (π P' T) ((coord P' T).comp (AddMonoidHom.toMultiplicative g))

lemma reindex_appTop_evalRing {P' : Type u} [AddCommMonoid P'] (g : P →+ P') (x) :
    (reindex g T).appTop (evalRing P T x) =
      evalRing P' T (AddMonoidAlgebra.mapDomainRingHom _ g x) := by
  have : ((reindex g T).appTop).hom.comp (evalRing P T) =
      (evalRing P' T).comp (AddMonoidAlgebra.mapDomainRingHom _ g) := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun p => ?_)
    · simp only [RingHom.comp_apply]
      rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero,
        evalRing_single_zero, evalRing_single_zero]
      change (reindex g T).appTop ((π P T).appTop r) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, reindex, homOf_π]
    · simp only [RingHom.comp_apply]
      rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        evalRing_single_one, evalRing_single_one]
      change (reindex g T).appTop (coord P T _) = _
      rw [reindex, homOf_coord]
      rfl
  exact congrArg (fun k => k x) this

lemma reindex_appTop_injective {P' : Type u} [AddCommMonoid P'] [IsAffine T] (g : P →+ P')
    (hg : Function.Injective g) : Function.Injective (reindex g T).appTop := by
  intro a b h
  obtain ⟨x, rfl⟩ := (evalRing_bijective (P := P) (T := T)).2 a
  obtain ⟨y, rfl⟩ := (evalRing_bijective (P := P) (T := T)).2 b
  rw [reindex_appTop_evalRing, reindex_appTop_evalRing] at h
  have h' := (evalRing_bijective (P := P') (T := T)).1 h
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainRingHom_apply] at h'
  rw [AddMonoidAlgebra.mapDomain_injective hg h']

/-- The morphism `𝔸(P)_S → 𝔸(P)_T` over `f : S ⟶ T`. -/
noncomputable def map {S T : Scheme.{u}} (f : S ⟶ T) : MonAff P S ⟶ MonAff P T :=
  homOf (π P S ≫ f) (coord P S)

lemma isPullback_map {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (map (P := P) f) (π P S) (π P T) f := by
  refine (IsPullback.paste_horiz_iff (.flip <| .of_hasPullback _ _) (homOf_π _ _)).mp ?_
  simp only [terminal.comp_from]
  convert! (IsPullback.of_hasPullback _ _).flip
  have : homOf (π P S ≫ f) (coord P S) ≫ toSpec P T = toSpecEquiv.symm (coord P S) :=
    pullback.lift_snd _ _ _
  exact this.trans (toSpecEquiv.symm_apply_apply _)

lemma map_reindex {P' : Type u} [AddCommMonoid P'] (g : P →+ P') {S T : Scheme.{u}} (f : S ⟶ T) :
    map f ≫ reindex g T = reindex g S ≫ map f := by
  refine hom_ext' ?_ fun p => ?_
  · simp [map, reindex]
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have h1 : (reindex g T).appTop (coord P T p) = coord P' T (AddMonoidHom.toMultiplicative g p) :=
      homOf_coord _ _ _
    have h2 : (reindex g S).appTop (coord P S p) = coord P' S (AddMonoidHom.toMultiplicative g p) :=
      homOf_coord _ _ _
    have h3 : ∀ {Q : Type u} [AddCommMonoid Q] (r), (map (P := Q) f).appTop (coord Q T r) = coord Q S r :=
      fun r => homOf_coord _ _ _
    rw [h1, h3, h3, h2]

lemma isIso_of_closed_of_injective {E Y : Scheme.{u}} [IsAffine Y] {i : E ⟶ Y}
    [IsClosedImmersion i] (h : Function.Injective i.appTop) : IsIso i := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  exact Scheme.IdealSheafData.ext_of_isAffine
    (by
      simp only [i.ker_apply ⟨⊤, isAffineOpen_top Y⟩, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact (RingHom.injective_iff_ker_eq_bot _).1 h)

/-- **Density** (used for Proposition 3.29): the closed immersion test. If a closed immersion
`i : E ⟶ 𝔸(P)_T` is factored through by `𝔸(P')_T ⟶ 𝔸(P)_T` with `P ⊆ P'`, then `i` is an isomorphism. -/
theorem isIso_of_factor {P' : Type u} [AddCommMonoid P'] (g : P →+ P')
    (hg : Function.Injective g) {E : Scheme.{u}} (i : E ⟶ MonAff P T) [IsClosedImmersion i]
    (j : MonAff P' T ⟶ E) (hj : j ≫ i = reindex g T) : IsIso i := by
  let 𝒰 : T.OpenCover := T.affineOpenCover.openCover
  have hopen : ∀ a, IsOpenImmersion (map (P := P) (𝒰.f a)) := fun a =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_map (𝒰.f a)).flip inferInstance
  let 𝒱 : (MonAff P T).OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀ (fun a => MonAff P (𝒰.X a))
    (fun a => map (𝒰.f a)) (fun x => by
      obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (π P T x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      have hp := isPullback_map (P := P) (𝒰.f a)
      refine ⟨a, hp.isoPullback.inv z, ?_⟩
      rw [← hz, ← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst]) hopen
  suffices h : MorphismProperty.isomorphisms Scheme i from h
  refine IsZariskiLocalAtTarget.of_openCover 𝒱 fun a => ?_
  have : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  have hA₀ : IsAffine (MonAff P (𝒰.X a)) := .of_isIso (isoOfIsAffine P (𝒰.X a)).hom
  have hA : IsAffine (𝒱.X a) := hA₀
  have hc : IsClosedImmersion (𝒱.pullbackHom i a) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback i (𝒱.f a)) inferInstance
  let ja : MonAff P' (𝒰.X a) ⟶ pullback i (𝒱.f a) :=
    pullback.lift (map (𝒰.f a) ≫ j) (reindex g (𝒰.X a)) (by
      change _ = _ ≫ map (𝒰.f a)
      rw [Category.assoc, hj, map_reindex])
  have hja : ja ≫ 𝒱.pullbackHom i a = reindex g (𝒰.X a) := pullback.lift_snd _ _ _
  apply isIso_of_closed_of_injective
  intro x y hxy
  apply reindex_appTop_injective (T := 𝒰.X a) g hg
  have e : ∀ z, (reindex g (𝒰.X a)).appTop z = ja.appTop ((𝒱.pullbackHom i a).appTop z) := by
    intro z
    rw [← hja]
    exact ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop _ _) z
  exact (e x).trans ((congrArg _ hxy).trans (e y).symm)

end MonAff

end MonAffSec

/-! ### Separated spaces: Proposition 3.29, Corollary 3.30, the end of Fact 4.3 -/

section Site

open AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `X` is separated over `S`: its diagonal is a closed immersion, tested after every representable
base change. -/
def IsSeparatedSpace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (diag X)

/-- A closed condition: two points of a separated `X` on `P` which agree on `Q → P` are equal, if
any closed immersion to `P` through which `Q → P` factors is an isomorphism. -/
theorem IsSeparatedSpace.eq_of_map_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsep : IsSeparatedSpace X) {P Q : BigFppfOver B S hS} (q : Q ⟶ P) (x y : X.obj (op P))
    (hxy : X.map q.op x = X.map q.op y)
    (H : ∀ {E : BigFppfOver B S hS} (i : E ⟶ P) (j : Q ⟶ E),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) → j ≫ i = q →
        IsIso ((BigFppfOver.toScheme B S hS).map i)) : x = y := by
  let g : yoneda.obj P ⟶ X ⨯ X := prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)
  let E := hsep.rep.pullback g
  let i : E ⟶ P := hsep.rep.snd g
  let e₀ : yoneda.obj Q ⟶ X := yonedaEquiv.symm (X.map q.op x)
  have hq : yoneda.map q ≫ yonedaEquiv.symm x = e₀ := (yonedaEquiv_symm_map _ _).symm
  have hq' : yoneda.map q ≫ yonedaEquiv.symm y = e₀ := by
    change _ = yonedaEquiv.symm (X.map q.op x)
    rw [hxy]
    exact (yonedaEquiv_symm_map _ _).symm
  have hw : e₀ ≫ diag X = yoneda.map q ≫ g := by
    apply Limits.prod.hom_ext
    · simp [g, diag, hq]
    · simp [g, diag, hq']
  let j : Q ⟶ E := hsep.rep.lift e₀ q hw
  have hj : j ≫ i = q := hsep.rep.lift_snd _ _ _
  have hc : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hsep.property_snd g
  have hiso : IsIso i := by
    have := H i j hc hj
    exact isIso_of_reflects_iso i (BigFppfOver.toScheme B S hS)
  have hpb := hsep.rep.isPullback g
  have hgd : g = inv (yoneda.map i) ≫ hsep.rep.fst g ≫ diag X := by
    rw [hpb.w]; simp [i]
  have e1 : yonedaEquiv.symm x = yonedaEquiv.symm y := by
    have a1 : g ≫ prod.fst = yonedaEquiv.symm x := by simp [g]
    have a2 : g ≫ prod.snd = yonedaEquiv.symm y := by simp [g]
    rw [← a1, ← a2, hgd]
    simp [diag]
  exact yonedaEquiv.symm.injective e1

variable {M : Type u} [AddCommMonoid M]

lemma contains_monAff (P : Type u) [AddCommMonoid P] (hP : B.Contains (Spec (ZMon P)))
    (T : BigFppfOver B S hS) : B.Contains (MonAff P ((BigFppfOver.toScheme B S hS).obj T)) :=
  lt_of_le_of_lt (Scheme.size_pullback_le _ _) (max_lt T.left.2 hP)

/-- `𝔸(P)_T` as an object of the site over `S`. -/
noncomputable def monAffObj (P : Type u) [AddCommMonoid P] (hP : B.Contains (Spec (ZMon P)))
    (T : BigFppfOver B S hS) : BigFppfOver B S hS :=
  siteObject B S hS (contains_monAff P hP T) (MonAff.π P _ ≫ structMap T)

/-- `𝔸(N)_T` is an object of the site with the universal point, given that `Spec ℤ[N]` is. -/
noncomputable def monAffUniversal (N : AddSubmonoid M) (hN : B.Contains (Spec (ZMon N)))
    (T : BigFppfOver B S hS) : UniversalPoint (fppfO B S hS) N T where
  P := monAffObj N hN T
  π := Over.homMk (ObjectProperty.homMk (MonAff.π N _)) rfl
  u := MonAff.coord N _
  lift {T'} t a := Over.homMk (ObjectProperty.homMk
    (MonAff.homOf ((BigFppfOver.toScheme B S hS).map t) a)) (by
      apply B.inclusion.map_injective
      have hw : (BigFppfOver.toScheme B S hS).map t ≫ structMap T = structMap T' :=
        congrArg (B.inclusion.map) (Over.w t)
      refine Eq.trans ?_ hw
      refine Eq.trans ?_ (MonAff.homOf_π_assoc _ a (structMap T))
      rfl)
  lift_π t a := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact MonAff.homOf_π _ _
  res_lift t a := by
    refine MonoidHom.ext fun p => ?_
    exact MonAff.homOf_coord _ _ _
  uniq t a s h₁ h₂ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine MonAff.hom_ext' ?_ fun p => ?_
    · refine Eq.trans ?_ (MonAff.homOf_π _ a).symm
      refine Eq.trans ?_ (congrArg (BigFppfOver.toScheme B S hS).map h₁)
      rfl
    · refine Eq.trans ?_ (MonAff.homOf_coord _ a p).symm
      exact congrArg (fun k => k p) h₂

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M X}

/-- **Proposition 3.29.** If `X` is separated and `N ⊆ L` are magnets, then `X^N → X^L` is a
monomorphism. The hypotheses `hN`, `hL` say that `Spec ℤ[N]`, `Spec ℤ[L]` lie below the size cutoff
of the site (so that `𝔸(N)_T`, `𝔸(L)_T` are objects of the site); they are automatic in the paper,
whose category of schemes has no cutoff. -/
theorem attractor_ofLE_injective (hsep : IsSeparatedSpace X) {N L : AddSubmonoid M} (h : N ≤ L)
    (hN : B.Contains (Spec (ZMon N))) (hL : B.Contains (Spec (ZMon L))) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.ofLE h : AttractorPt act N T → AttractorPt act L T) := by
  intro φ ψ hφψ
  let UN := monAffUniversal N hN T
  let UL := monAffUniversal L hL T
  let q : UL.P ⟶ UN.P := UN.lift UL.π (APt.restrict h UL.u)
  have hq : q ≫ UN.π = UL.π := UN.lift_π _ _
  have hu : APt.res q.op UN.u = APt.restrict h UL.u := UN.res_lift _ _
  have key : ∀ χ : AttractorPt act N T,
      X.map q.op (χ.app UN.π UN.u) = χ.app UL.π (APt.restrict h UL.u) := by
    intro χ
    have := χ.naturality q UN.π UN.u
    rw [hq, hu] at this
    exact this.symm
  have hxy : φ.app UN.π UN.u = ψ.app UN.π UN.u := by
    refine hsep.eq_of_map_eq q _ _ ?_ ?_
    · rw [key, key]
      exact congrArg (fun χ : AttractorPt act L T => χ.app UL.π UL.u) hφψ
    · intro E i j hc hj
      refine @MonAff.isIso_of_factor N _ ((BigFppfOver.toScheme B S hS).obj T) L _
        (AddSubmonoid.inclusion h) (AddSubmonoid.inclusion_injective h) _
        ((BigFppfOver.toScheme B S hS).map i) hc ((BigFppfOver.toScheme B S hS).map j) ?_
      exact ((BigFppfOver.toScheme B S hS).map_comp j i).symm.trans
        ((congrArg (BigFppfOver.toScheme B S hS).map hj).trans rfl)
  refine AttractorPt.ext ?_
  funext T' t a
  rw [φ.app_eq_of_universal UN, ψ.app_eq_of_universal UN, hxy]

/-- **Corollary 3.30.** If `X` is separated, the map `X^N → X` is a monomorphism: `toPoint` is
injective on `T`-points; it is natural by `AttractorPt.toPoint_baseChange`. The hypotheses `hN`,
`hM` are the size conditions explained in `attractor_ofLE_injective`. -/
theorem attractor_toPoint_injective (hsep : IsSeparatedSpace X) (N : AddSubmonoid M)
    (hN : B.Contains (Spec (ZMon N))) (hM : B.Contains (Spec (ZMon (⊤ : AddSubmonoid M))))
    (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.toPoint : AttractorPt act N T → X.obj (op T)) := by
  intro φ ψ h
  refine attractor_ofLE_injective hsep le_top hN hM T ?_
  exact (attractorTopEquiv act T).injective h

/-- **Fact 4.3**, last assertion: for `X` separated, `X^N_{F,Z} → X` is a monomorphism of `S`-functors,
that is, injective on points. See `attractor_toPoint_injective` for the size conditions. -/
theorem prescribedLimit_toPoint_injective (hsep : IsSeparatedSpace X) {N F : AddSubmonoid M}
    (hF : IsFace F N) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} (i : PointMap Z act F)
    (hN : B.Contains (Spec (ZMon N))) (hM : B.Contains (Spec (ZMon (⊤ : AddSubmonoid M))))
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective fun f : (prescribedLimit act hF i).obj T =>
      AttractorPt.toPoint (f.1 : AttractorPt act N (unop T)) := fun _ _ h =>
  Subtype.ext (attractor_toPoint_injective hsep N hN hM (unop T) h)

end Site

end AlgMag

#print axioms AlgMag.prescribedLimitIso
#print axioms AlgMag.attractor_ofLE_injective
#print axioms AlgMag.prescribedLimit_toPoint_injective
