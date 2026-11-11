/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
import AlgMag.GeneralBaseCore
import AlgMag.Representation
import AlgMag.Sec2Monoids

/-!
# The monoid schemes `𝔸(N)_S` over an arbitrary base

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), §2 for an arbitrary scheme `S`.
`𝔸(N)` is `Spec ℤ[N]`, and `𝔸(N)_S` its base change along `S ⟶ ⊤_ Scheme` (the terminal scheme is
`Spec ℤ`, cf. `specULiftZIsTerminal`). Its `T`-points over `S` are the monoid maps
`N → (Γ(T, ⊤), ·)` (`AlgMag.GB.pts`), and that is how all the structure below is produced.

## Main results

* `AlgMag.GB.A`, `AlgMag.GB.pts`: Definition 2.4 (ii) and its functor of points.
* `AlgMag.GB.isPullback_AZ_prod`, `AlgMag.GB.isPullback_A_prod`: Fact 2.7.
* `AlgMag.GB.monObjA`: `𝔸(N)_S` is a monoid object of `Over S`.
* `AlgMag.GB.flat_mul`, `AlgMag.GB.flat_mulZ`: Proposition 2.8 (ii), (iii).
* `AlgMag.GB.instLFP_AZ`, `AlgMag.GB.lfp_mulZ`, `AlgMag.GB.instLFP_str`, `AlgMag.GB.lfp_mul`,
  `AlgMag.GB.affine_mul`: Fact 2.10 (iii), (iv), (v).
* `AlgMag.GB.actMor`, `AlgMag.GB.pts_actMor`, `AlgMag.GB.aAction`: Fact 2.12.
* `AlgMag.GB.actionOfMor`: an action morphism on a scheme, as an `AlgMag.AAction`.
* `AlgMag.GB.universalPoint`: `𝔸(N)_T` as an object of `Over S`, so that the attractor of
  `AlgMag.Foundations` is literally Definition 3.1 (`AlgMag.attractorPtEquivOfUniversal`).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

universe u

namespace AlgMag.GB

section Absolute

variable (N : Type u) [AddCommMonoid N]

/-- Definition 2.1: the ring `ℤ[N]`. -/
abbrev zRing : CommRingCat.{u} := CommRingCat.of (AddMonoidAlgebra ℤ N)

/-- Definition 2.4 (i): the scheme `𝔸(N) = Spec ℤ[N]`. -/
abbrev AZ : Scheme.{u} := Spec (zRing N)

variable {N}

/-- The ring morphism `ℤ[N] → B` attached to a monoid map `N → (B, ·)`. -/
def liftZ {B : CommRingCat.{u}} (a : Multiplicative N →* B) : zRing N ⟶ B :=
  CommRingCat.ofHom (AddMonoidAlgebra.lift ℤ B N a).toRingHom

@[simp] lemma liftZ_X {B : CommRingCat.{u}} (a : Multiplicative N →* B) (n : N) :
    (liftZ a).hom (AddMonoidAlgebra.single n 1) = a (Multiplicative.ofAdd n) := by
  simp [liftZ, AddMonoidAlgebra.lift_single]

/-- A ring morphism out of `ℤ[N]` is determined by the images of the monomials. -/
lemma zRing_hom_ext {B : CommRingCat.{u}} {f g : zRing N ⟶ B}
    (h : ∀ n : N, f.hom (AddMonoidAlgebra.single n 1) = g.hom (AddMonoidAlgebra.single n 1)) :
    f = g := by
  refine CommRingCat.hom_ext (RingHom.ext fun (x : AddMonoidAlgebra ℤ N) => ?_)
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    have : (AddMonoidAlgebra.single n c : AddMonoidAlgebra ℤ N) = c • AddMonoidAlgebra.single n 1 := by
      simp [AddMonoidAlgebra.smul_single]
    rw [this, map_zsmul, map_zsmul, h]

/-- The monoid map `N → (B, ·)` attached to a ring morphism `ℤ[N] → B`. -/
def unliftZ {B : CommRingCat.{u}} (f : zRing N ⟶ B) : Multiplicative N →* B where
  toFun n := f.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
  map_one' := by
    change f.hom (AddMonoidAlgebra.single 0 1) = 1
    exact map_one f.hom
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    simp [AddMonoidAlgebra.single_mul_single]

/-- Monoid maps are ring morphisms out of `ℤ[N]`. -/
def liftZEquiv (B : CommRingCat.{u}) : (zRing N ⟶ B) ≃ (Multiplicative N →* B) where
  toFun := unliftZ
  invFun := liftZ
  left_inv f := zRing_hom_ext fun n => by rw [liftZ_X]; rfl
  right_inv a := by
    refine MonoidHom.ext fun n => ?_
    exact liftZ_X a (Multiplicative.toAdd n)

/-- The points of the absolute `𝔸(N)`. -/
def ptsZ (T : Scheme.{u}) : (T ⟶ AZ N) ≃ (Multiplicative N →* Γ(T, ⊤)) :=
  (homSpecEquiv T _).trans (liftZEquiv _)

lemma ptsZ_comp {T T' : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ AZ N) :
    ptsZ T' (g ≫ f) = (g.appTop.hom : Γ(T, ⊤) →+* Γ(T', ⊤)).toMonoidHom.comp (ptsZ T f) := by
  refine MonoidHom.ext fun n => ?_
  change (homSpecEquiv T' _ (g ≫ f)).hom _ = g.appTop.hom ((homSpecEquiv T _ f).hom _)
  rw [homSpecEquiv_comp]
  rfl

/-- The morphism `𝔸(Q) → 𝔸(P)` dual to `φ : P → Q`. -/
def AZmap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) : AZ Q ⟶ AZ P :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom ℤ φ))

lemma ptsZ_AZmap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) {T : Scheme.{u}}
    (f : T ⟶ AZ Q) :
    ptsZ T (f ≫ AZmap φ) = (ptsZ T f).comp (AddMonoidHom.toMultiplicative φ) := by
  refine MonoidHom.ext fun n => ?_
  change (homSpecEquiv T _ (f ≫ AZmap φ)).hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) =
    (homSpecEquiv T _ f).hom (AddMonoidAlgebra.single (φ (Multiplicative.toAdd n)) 1)
  rw [AZmap, homSpecEquiv_map]
  change (homSpecEquiv T _ f).hom (AddMonoidAlgebra.mapDomainRingHom ℤ φ _) = _
  congr 1
  simp [AddMonoidAlgebra.mapDomainRingHom]

/-- A monoid map on `N × L` from monoid maps on `N` and `L`. -/
def pairPt {N L : Type u} [AddCommMonoid N] [AddCommMonoid L] {B : Type u} [CommMonoid B]
    (a : Multiplicative N →* B) (b : Multiplicative L →* B) : Multiplicative (N × L) →* B where
  toFun p := a (Multiplicative.ofAdd (Multiplicative.toAdd p).1) *
    b (Multiplicative.ofAdd (Multiplicative.toAdd p).2)
  map_one' := by
    change a 1 * b 1 = 1
    simp
  map_mul' x y := by
    change a (Multiplicative.ofAdd (_ + _)) * b (Multiplicative.ofAdd (_ + _)) = _
    rw [ofAdd_add, ofAdd_add, map_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _

lemma pairPt_fst {N L : Type u} [AddCommMonoid N] [AddCommMonoid L] {B : Type u} [CommMonoid B]
    (a : Multiplicative N →* B) (b : Multiplicative L →* B) :
    (pairPt a b).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl N L)) = a := by
  refine MonoidHom.ext fun n => ?_
  change a n * b 1 = a n
  simp

lemma pairPt_snd {N L : Type u} [AddCommMonoid N] [AddCommMonoid L] {B : Type u} [CommMonoid B]
    (a : Multiplicative N →* B) (b : Multiplicative L →* B) :
    (pairPt a b).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr N L)) = b := by
  refine MonoidHom.ext fun n => ?_
  change a 1 * b n = b n
  simp

lemma pairPt_eta {N L : Type u} [AddCommMonoid N] [AddCommMonoid L] {B : Type u} [CommMonoid B]
    (c : Multiplicative (N × L) →* B) :
    pairPt (c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl N L)))
      (c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr N L))) = c := by
  refine MonoidHom.ext fun p => ?_
  change c _ * c _ = c p
  rw [← map_mul]
  congr 1
  refine Multiplicative.toAdd.injective ?_
  change (AddMonoidHom.inl N L) _ + (AddMonoidHom.inr N L) _ = _
  simp

/-- **Fact 2.7**, first assertion: `𝔸(N × L) = 𝔸(N) ×_{Spec ℤ} 𝔸(L)`. The two projections are dual
to the inclusions `N → N × L`, `L → N × L`. -/
theorem isPullback_AZ_prod (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] :
    IsPullback (AZmap (AddMonoidHom.inl N L)) (AZmap (AddMonoidHom.inr N L))
      (terminal.from (AZ N)) (terminal.from (AZ L)) := by
  refine ⟨⟨terminal.hom_ext _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (ptsZ s.pt).symm (pairPt (ptsZ s.pt s.fst) (ptsZ s.pt s.snd))) ?_ ?_ ?_⟩⟩
  · intro s
    refine (ptsZ s.pt).injective ?_
    rw [ptsZ_AZmap, Equiv.apply_symm_apply, pairPt_fst]
  · intro s
    refine (ptsZ s.pt).injective ?_
    rw [ptsZ_AZmap, Equiv.apply_symm_apply, pairPt_snd]
  · intro s m h1 h2
    refine (ptsZ s.pt).injective ?_
    rw [Equiv.apply_symm_apply, ← h1, ← h2, ptsZ_AZmap, ptsZ_AZmap, pairPt_eta]

/-- The structure morphism `𝔸(N) → Spec ℤ` as `Spec` of a ring morphism. -/
lemma terminal_from_AZ (N : Type u) [AddCommMonoid N] :
    terminal.from (AZ N) = Spec.map (CommRingCat.ofHom ((algebraMap ℤ (AddMonoidAlgebra ℤ N)).comp
      (ULift.ringEquiv (R := ℤ)).toRingHom)) ≫
        (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).hom :=
  terminal.hom_ext _ _

/-- **Fact 2.10 (iii)** (with (ii) from `AlgMag.finitePresentation`). -/
instance instLFP_AZ (N : Type u) [AddCommMonoid N] [AddMonoid.FG N] :
    LocallyOfFinitePresentation (terminal.from (AZ N)) := by
  rw [terminal_from_AZ]
  have h : (CommRingCat.ofHom ((algebraMap ℤ (AddMonoidAlgebra ℤ N)).comp
      (ULift.ringEquiv (R := ℤ)).toRingHom)).hom.FinitePresentation := by
    refine RingHom.FinitePresentation.comp ?_ (RingHom.FinitePresentation.of_surjective _
      (ULift.ringEquiv (R := ℤ)).surjective ?_)
    · rw [RingHom.finitePresentation_algebraMap]
      exact finitePresentation ℤ N
    · have : RingHom.ker (ULift.ringEquiv (R := ℤ)).toRingHom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 (ULift.ringEquiv (R := ℤ)).injective
      rw [this]
      exact Submodule.fg_bot
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      ((algebraMap ℤ (AddMonoidAlgebra ℤ N)).comp (ULift.ringEquiv (R := ℤ)).toRingHom))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr h
  infer_instance

/-- `𝔸(φ)` is flat when `ℤ[φ]` is. -/
lemma flat_AZmap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (h : (AddMonoidAlgebra.mapDomainRingHom ℤ φ).Flat) : Flat (AZmap φ) :=
  (HasRingHomProperty.Spec_iff (P := @Flat)).mpr h

/-- **Proposition 2.8 (ii)**: under Fact 2.7, the multiplication of `𝔸(N)` is `𝔸(diag)`; it is flat
if `N` acts freely on `N × N`. -/
theorem flat_mulZ (N : Type u) [AddCommMonoid N] (h : IsFreeAlong (diag N)) :
    Flat (AZmap (diag N)) :=
  flat_AZmap _ (flat_diag ℤ h)

/-- The ring map `ℤ[N] → ℤ[N × N]` is of finite presentation. -/
lemma finitePresentation_diag (N : Type u) [AddCommMonoid N] [AddMonoid.FG N] :
    (AddMonoidAlgebra.mapDomainRingHom ℤ (diag N)).FinitePresentation := by
  refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap ℤ (AddMonoidAlgebra ℤ N)) ?_ ?_
  · have : (AddMonoidAlgebra.mapDomainRingHom ℤ (diag N)).comp
        (algebraMap ℤ (AddMonoidAlgebra ℤ N)) = algebraMap ℤ (AddMonoidAlgebra ℤ (N × N)) :=
      RingHom.ext_int _ _
    rw [this, RingHom.finitePresentation_algebraMap]
    exact finitePresentation ℤ (N × N)
  · rw [RingHom.finiteType_algebraMap]
    infer_instance

/-- **Fact 2.10 (iv)**: the multiplication of `𝔸(N)` is of finite presentation (it is affine). -/
theorem lfp_mulZ (N : Type u) [AddCommMonoid N] [AddMonoid.FG N] :
    LocallyOfFinitePresentation (AZmap (diag N)) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr (finitePresentation_diag N)

end Absolute

section Relative

variable (N : Type u) [AddCommMonoid N] (S : Scheme.{u})

/-- **Definition 2.4 (ii)**: `𝔸(N)_S = S ×_{Spec ℤ} 𝔸(N)`, as a scheme over `S`. -/
def A : Over S := Over.mk (pullback.fst (terminal.from S) (terminal.from (AZ N)))

/-- The projection `𝔸(N)_S → 𝔸(N)`. -/
def toAZ : (A N S).left ⟶ AZ N := pullback.snd (terminal.from S) (terminal.from (AZ N))

variable {N S}

/-- The functor of points of `𝔸(N)_S`: a morphism over `S` from `T` is a monoid map
`N → (Γ(T, ⊤), ·)`. -/
def pts (T : Over S) : (T ⟶ A N S) ≃ APt (overO S) N (op T) where
  toFun f := ptsZ T.left (f.left ≫ toAZ N S)
  invFun a := Over.homMk (pullback.lift T.hom ((ptsZ T.left).symm a) (terminal.hom_ext _ _))
    (pullback.lift_fst _ _ _)
  left_inv f := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      rw [pullback.lift_fst]
      exact (Over.w f).symm
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd, Equiv.symm_apply_apply]
      rfl
  right_inv a := by
    change ptsZ T.left (pullback.lift _ _ _ ≫ pullback.snd _ _) = a
    rw [pullback.lift_snd]
    exact (ptsZ T.left).apply_symm_apply a

lemma pts_comp {T T' : Over S} (g : T' ⟶ T) (f : T ⟶ A N S) :
    pts T' (g ≫ f) = APt.res g.op (pts T f) := by
  change ptsZ T'.left ((g ≫ f).left ≫ toAZ N S) = _
  rw [Over.comp_left, Category.assoc, ptsZ_comp]
  rfl

/-- **Definition 2.4 (ii)**, functoriality: the morphism `𝔸(Q)_S → 𝔸(P)_S` dual to `φ : P → Q`. -/
def Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) (S : Scheme.{u}) :
    A Q S ⟶ A P S :=
  (pts (A Q S)).symm ((pts (A Q S) (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ))

lemma pts_comp_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    {T : Over S} (g : T ⟶ A Q S) :
    pts T (g ≫ Amap φ S) = (pts T g).comp (AddMonoidHom.toMultiplicative φ) := by
  rw [pts_comp, Amap, Equiv.apply_symm_apply]
  have : pts T g = APt.res g.op (pts (A Q S) (𝟙 _)) := by
    rw [← pts_comp, Category.comp_id]
  rw [this]
  rfl

lemma toAZ_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) :
    (Amap φ S).left ≫ toAZ P S = toAZ Q S ≫ AZmap φ := by
  refine (ptsZ _).injective ?_
  rw [ptsZ_AZmap]
  exact pts_comp_Amap φ (𝟙 _)

/-- The square exhibiting `𝔸(φ)_S` as the base change of `𝔸(φ)` along `S → Spec ℤ`. -/
theorem isPullback_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) :
    IsPullback (Amap φ S).left (toAZ Q S) (toAZ P S) (AZmap φ) := by
  refine IsPullback.of_right (h₁₂ := (A P S).hom) (h₂₂ := terminal.from (AZ P))
    (v₁₃ := terminal.from S) ?_ (toAZ_Amap φ) (IsPullback.of_hasPullback _ _)
  have h1 : (Amap φ S).left ≫ (A P S).hom = (A Q S).hom := Over.w _
  have h2 : AZmap φ ≫ terminal.from (AZ P) = terminal.from (AZ Q) := terminal.hom_ext _ _
  rw [h1, h2]
  exact IsPullback.of_hasPullback _ _

/-- **Fact 2.7**, over `S`: `𝔸(N × L)_S = 𝔸(N)_S ×_S 𝔸(L)_S`. -/
theorem isPullback_A_prod (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] (S : Scheme.{u}) :
    IsPullback (Amap (AddMonoidHom.inl N L) S).left (Amap (AddMonoidHom.inr N L) S).left
      (A N S).hom (A L S).hom := by
  have w : (Amap (AddMonoidHom.inl N L) S).left ≫ (A N S).hom =
      (Amap (AddMonoidHom.inr N L) S).left ≫ (A L S).hom := by
    rw [Over.w, Over.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s =>
    let T : Over S := Over.mk (s.fst ≫ (A N S).hom)
    let x : T ⟶ A N S := Over.homMk s.fst rfl
    let y : T ⟶ A L S := Over.homMk s.snd s.condition.symm
    ((pts T).symm (pairPt (pts T x) (pts T y))).left) ?_ ?_ ?_⟩⟩
  · intro s
    let T : Over S := Over.mk (s.fst ≫ (A N S).hom)
    let x : T ⟶ A N S := Over.homMk s.fst rfl
    let y : T ⟶ A L S := Over.homMk s.snd s.condition.symm
    change ((pts T).symm (pairPt (pts T x) (pts T y)) ≫ Amap _ S).left = x.left
    congr 1
    refine (pts T).injective ?_
    rw [pts_comp_Amap, Equiv.apply_symm_apply, pairPt_fst]
  · intro s
    let T : Over S := Over.mk (s.fst ≫ (A N S).hom)
    let x : T ⟶ A N S := Over.homMk s.fst rfl
    let y : T ⟶ A L S := Over.homMk s.snd s.condition.symm
    change ((pts T).symm (pairPt (pts T x) (pts T y)) ≫ Amap _ S).left = y.left
    congr 1
    refine (pts T).injective ?_
    rw [pts_comp_Amap, Equiv.apply_symm_apply, pairPt_snd]
  · intro s m h1 h2
    let T : Over S := Over.mk (s.fst ≫ (A N S).hom)
    let x : T ⟶ A N S := Over.homMk s.fst rfl
    let y : T ⟶ A L S := Over.homMk s.snd s.condition.symm
    have hm : m ≫ (A (N × L) S).hom = T.hom := by
      change m ≫ _ = s.fst ≫ _
      rw [← h1, Category.assoc, Over.w]
    let m' : T ⟶ A (N × L) S := Over.homMk m hm
    change m'.left = ((pts T).symm (pairPt (pts T x) (pts T y))).left
    congr 1
    refine (pts T).injective ?_
    rw [Equiv.apply_symm_apply]
    have e1 : x = m' ≫ Amap _ S := Over.OverMorphism.ext h1.symm
    have e2 : y = m' ≫ Amap _ S := Over.OverMorphism.ext h2.symm
    rw [e1, e2, pts_comp_Amap, pts_comp_Amap, pairPt_eta]

/-- `𝔸(N)_S → S` is affine (first part of Fact 2.6 (i)). -/
instance instAffine_str : IsAffineHom (A N S).hom :=
  by
    apply MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (terminal.from S) (terminal.from (AZ N))).flip
    infer_instance

/-- **Fact 2.10 (v)**: `𝔸(N)_S → S` is locally of finite presentation (and it is affine, so
quasi-compact and quasi-separated: `instAffine_str`). -/
instance instLFP_str [AddMonoid.FG N] : LocallyOfFinitePresentation (A N S).hom :=
  by
    apply MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (terminal.from S) (terminal.from (AZ N))).flip
    infer_instance

instance instAffine_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q) :
    IsAffineHom (Amap φ S).left := by
  have : IsAffineHom (AZmap φ) := inferInstance
  apply MorphismProperty.of_isPullback (isPullback_Amap φ).flip
  infer_instance

lemma flat_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (h : (AddMonoidAlgebra.mapDomainRingHom ℤ φ).Flat) : Flat (Amap φ S).left := by
  have := flat_AZmap φ h
  apply MorphismProperty.of_isPullback (isPullback_Amap φ).flip
  infer_instance

lemma lfp_Amap {P Q : Type u} [AddCommMonoid P] [AddCommMonoid Q] (φ : P →+ Q)
    (h : (AddMonoidAlgebra.mapDomainRingHom ℤ φ).FinitePresentation) :
    LocallyOfFinitePresentation (Amap φ S).left := by
  have : LocallyOfFinitePresentation (AZmap φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr h
  apply MorphismProperty.of_isPullback (isPullback_Amap φ).flip
  infer_instance

section Monoid

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

/-- The functor `T ↦ 𝔸(N)_S(T)`, with values in monoids. -/
def ptsFunctor (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ MonCat.{u} where
  obj T := MonCat.of (APt (overO S) N T)
  map f := MonCat.ofHom
    { toFun := APt.res f
      map_one' := by ext p; simp
      map_mul' := APt.res_mul f }
  map_id T := MonCat.hom_ext (MonoidHom.ext fun a => APt.res_id a)
  map_comp f g := MonCat.hom_ext (MonoidHom.ext fun a => APt.res_comp f g a)

/-- `𝔸(N)_S` represents the functor of its points. -/
def ptsRepr (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) :
    (ptsFunctor N S ⋙ forget _).RepresentableBy (A N S) where
  homEquiv {T} := pts T
  homEquiv_comp g f := pts_comp g f

/-- **Definition 2.4 (ii)**: `𝔸(N)_S` is canonically a monoid scheme over `S`: a monoid object of
`Over S`, whose product is the fibre product over `S`. -/
abbrev monObjA (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) : MonObj (A N S) :=
  MonObj.ofRepresentableBy _ (ptsFunctor N S) (ptsRepr N S)

/-- The multiplication of `𝔸(N)_S`. -/
abbrev mul (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) : A N S ⊗ A N S ⟶ A N S :=
  (monObjA N S).mul

/-- The multiplication of `𝔸(N)_S` on points is pointwise multiplication. -/
theorem pts_mul {T : Over S} (x y : T ⟶ A N S) :
    pts T (lift x y ≫ mul N S) = pts T x * pts T y := by
  rw [pts_comp]
  have : pts (A N S ⊗ A N S) (mul N S) = pts _ (fst _ _) * pts _ (snd _ _) :=
    (pts _).apply_symm_apply _
  rw [this, APt.res_mul, ← pts_comp, ← pts_comp, lift_fst, lift_snd]

/-- The comparison `𝔸(N)_S ×_S 𝔸(L)_S → 𝔸(N × L)_S`. -/
def prodHom (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] (S : Scheme.{u}) :
    A N S ⊗ A L S ⟶ A (N × L) S :=
  (pts _).symm (pairPt (pts _ (fst _ _)) (pts _ (snd _ _)))

/-- **Fact 2.7**, as an isomorphism of `S`-schemes `𝔸(N)_S ×_S 𝔸(L)_S ≅ 𝔸(N × L)_S`. -/
def prodIso (N L : Type u) [AddCommMonoid N] [AddCommMonoid L] (S : Scheme.{u}) :
    A N S ⊗ A L S ≅ A (N × L) S where
  hom := prodHom N L S
  inv := lift (Amap (AddMonoidHom.inl N L) S) (Amap (AddMonoidHom.inr N L) S)
  hom_inv_id := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · refine (pts _).injective ?_
      rw [Category.assoc, lift_fst, pts_comp_Amap, prodHom, Equiv.apply_symm_apply, pairPt_fst,
        Category.id_comp]
    · refine (pts _).injective ?_
      rw [Category.assoc, lift_snd, pts_comp_Amap, prodHom, Equiv.apply_symm_apply, pairPt_snd,
        Category.id_comp]
  inv_hom_id := by
    refine (pts _).injective ?_
    set l := lift (Amap (AddMonoidHom.inl N L) S) (Amap (AddMonoidHom.inr N L) S) with hl
    have h1 : APt.res l.op (pts _ (fst (A N S) (A L S))) =
        pts _ (Amap (AddMonoidHom.inl N L) S) := by rw [← pts_comp, hl, lift_fst]
    have h2 : APt.res l.op (pts _ (snd (A N S) (A L S))) =
        pts _ (Amap (AddMonoidHom.inr N L) S) := by rw [← pts_comp, hl, lift_snd]
    have h3 : ∀ (a : APt (overO S) N (op (A N S ⊗ A L S))) (b : APt (overO S) L (op (A N S ⊗ A L S))),
        APt.res l.op (pairPt a b) = pairPt (APt.res l.op a) (APt.res l.op b) := by
      intro a b
      refine MonoidHom.ext fun p => ?_
      simp only [APt.res_apply]
      exact map_mul _ _ _
    have h4 : ∀ {P : Type u} [AddCommMonoid P] (φ : P →+ N × L), pts (A (N × L) S) (Amap φ S) =
        (pts _ (𝟙 (A (N × L) S))).comp (AddMonoidHom.toMultiplicative φ) := fun φ =>
      Equiv.apply_symm_apply _ _
    rw [pts_comp, prodHom, Equiv.apply_symm_apply, h3, h1, h2, h4, h4, pairPt_eta]

/-- The multiplication of `𝔸(N)_S` is `𝔸(N)_S ×_S 𝔸(N)_S ≅ 𝔸(N × N)_S` followed by the morphism
dual to the diagonal `n ↦ (n, n)`. -/
theorem mul_eq (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) :
    mul N S = prodHom N N S ≫ Amap (diag N) S := by
  refine (pts _).injective ?_
  rw [pts_comp_Amap, prodHom, Equiv.apply_symm_apply]
  have : pts (A N S ⊗ A N S) (mul N S) = pts _ (fst _ _) * pts _ (snd _ _) :=
    (pts _).apply_symm_apply _
  rw [this]
  rfl

/-- **Proposition 2.8 (iii)**. If `N` acts freely on `N × N` (free `N`-set in the sense of Ogus,
`AlgMag.IsFreeAlong`), then the multiplication `𝔸(N)_S ×_S 𝔸(N)_S → 𝔸(N)_S` is flat, for an
arbitrary scheme `S`. Cancellativity is not needed. -/
theorem flat_mul (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) (h : IsFreeAlong (diag N)) :
    Flat (mul N S).left := by
  have := flat_Amap (S := S) (diag N) (flat_diag ℤ h)
  have : IsIso (prodHom N N S) := (prodIso N N S).isIso_hom
  have : IsIso (prodHom N N S).left := (inferInstance : IsIso ((Over.forget S).map (prodHom N N S)))
  rw [mul_eq, Over.comp_left]
  infer_instance

/-- **Fact 2.10 (v)**: the multiplication of `𝔸(N)_S` is locally of finite presentation. -/
theorem lfp_mul (N : Type u) [AddCommMonoid N] [AddMonoid.FG N] (S : Scheme.{u}) :
    LocallyOfFinitePresentation (mul N S).left := by
  have := lfp_Amap (S := S) (diag N) (finitePresentation_diag N)
  have : IsIso (prodHom N N S) := (prodIso N N S).isIso_hom
  have : IsIso (prodHom N N S).left := (inferInstance : IsIso ((Over.forget S).map (prodHom N N S)))
  rw [mul_eq, Over.comp_left]
  infer_instance

/-- **Fact 2.10 (v)**: the multiplication of `𝔸(N)_S` is affine, hence quasi-compact and
quasi-separated. -/
theorem affine_mul (N : Type u) [AddCommMonoid N] (S : Scheme.{u}) :
    IsAffineHom (mul N S).left := by
  have : IsIso (prodHom N N S) := (prodIso N N S).isIso_hom
  have : IsIso (prodHom N N S).left := (inferInstance : IsIso ((Over.forget S).map (prodHom N N S)))
  rw [mul_eq, Over.comp_left]
  infer_instance

variable {M : Type u} [AddCommMonoid M]

/-- **Fact 2.12**: the morphism of monoid schemes `𝔸(M)_S → 𝔸(N)_S` for a submonoid `N` of `M`. -/
abbrev restrict (N : AddSubmonoid M) (S : Scheme.{u}) : A M S ⟶ A N S := Amap N.subtype S

/-- **Fact 2.12**: the action morphism `𝔸(N)_S ×_S 𝔸(M)_S → 𝔸(N)_S`. It is the base change of the
coaction `ℤ[N] → ℤ[N] ⊗ ℤ[M]`, `X^n ↦ X^n ⊗ X^n` (`AlgMag.coact`), as `pts_actMor` shows. -/
def actMor (N : AddSubmonoid M) (S : Scheme.{u}) : A N S ⊗ A M S ⟶ A N S :=
  lift (fst _ _) (snd _ _ ≫ restrict N S) ≫ mul N S

/-- **Fact 2.12**: `x • h` is `n ↦ x(n) h(n)` on points. -/
theorem pts_actMor (N : AddSubmonoid M) {T : Over S} (x : T ⟶ A N S) (h : T ⟶ A M S) :
    pts T (lift x h ≫ actMor N S) = pts T x * APt.toMagnet N (pts T h) := by
  have : lift x h ≫ actMor N S = lift x (h ≫ restrict N S) ≫ mul N S := by
    rw [actMor, ← Category.assoc]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_ <;> simp
  rw [this, pts_mul, pts_comp_Amap]
  rfl

/-- **Fact 2.12**, on points: the action of `𝔸(M)_S` on `𝔸(N)_S`, as an `AlgMag.AAction`. -/
def aAction (N : AddSubmonoid M) (S : Scheme.{u}) :
    AAction (overO S) M (yoneda.obj (A N S)) where
  smul {U} h x := (pts (unop U)).symm (APt.toMagnet N h * pts (unop U) x)
  one_smul {U} x := by
    refine (pts (unop U)).injective ?_
    rw [Equiv.apply_symm_apply]
    have : APt.toMagnet N (1 : APt (overO S) M U) = 1 := rfl
    rw [this, _root_.one_mul]
  mul_smul {U} g h x := by
    refine (pts (unop U)).injective ?_
    simp only [Equiv.apply_symm_apply]
    have : APt.toMagnet N (g * h) = APt.toMagnet N g * APt.toMagnet N h := rfl
    rw [this, _root_.mul_assoc]
  map_smul {U V} f h x := by
    refine (pts (unop V)).injective ?_
    change pts (unop V) (f.unop ≫ _) = pts (unop V) ((pts (unop V)).symm _)
    rw [Equiv.apply_symm_apply, pts_comp, Equiv.apply_symm_apply, APt.res_mul]
    change _ = APt.toMagnet N (APt.res f h) * pts (unop V) (f.unop ≫ x)
    rw [pts_comp]
    rfl

/-- An action morphism `X ×_S 𝔸(M)_S → X` of schemes over `S`, unital and associative on points, as
an `AlgMag.AAction` (the two are equivalent by Yoneda). -/
def actionOfMor {X : Over S} (a : X ⊗ A M S ⟶ X)
    (one : ∀ {T : Over S} (x : T ⟶ X), lift x ((pts T).symm 1) ≫ a = x)
    (mul : ∀ {T : Over S} (x : T ⟶ X) (g h : APt (overO S) M (op T)),
      lift x ((pts T).symm (g * h)) ≫ a =
        lift (lift x ((pts T).symm h) ≫ a) ((pts T).symm g) ≫ a) :
    AAction (overO S) M (yoneda.obj X) where
  smul {U} h x := lift (show unop U ⟶ X from x) ((pts (unop U)).symm h) ≫ a
  one_smul {U} x := one x
  mul_smul {U} g h x := mul x g h
  map_smul {U V} f h x := by
    change f.unop ≫ lift (show unop U ⟶ X from x) ((pts (unop U)).symm h) ≫ a =
      lift (f.unop ≫ (show unop U ⟶ X from x)) ((pts (unop V)).symm (APt.res f h)) ≫ a
    rw [← Category.assoc]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp
    · simp only [Category.assoc, lift_snd]
      refine (pts (unop V)).injective ?_
      rw [Equiv.apply_symm_apply]
      have := pts_comp (N := M) (T := unop U) (T' := unop V) f.unop ((pts (unop U)).symm h)
      rw [Equiv.apply_symm_apply] at this
      exact this

/-- `𝔸(N)_T`, for `T` over `S`, as an object of the site `Over S`, with its universal point. So a
point of `AlgMag.attractor` over `T` is an equivariant `T`-morphism `𝔸(N)_T → X_T`, as in
Definition 3.1 (`AlgMag.attractorPtEquivOfUniversal`). -/
def universalPoint (N : AddSubmonoid M) (T : Over S) : UniversalPoint (overO S) N T where
  P := Over.mk ((A N T.left).hom ≫ T.hom)
  π := Over.homMk (A N T.left).hom rfl
  u := ptsZ (A N T.left).left (toAZ N T.left)
  lift {T'} t a := Over.homMk
    (pullback.lift t.left ((ptsZ T'.left).symm a) (terminal.hom_ext _ _))
    (by
      change pullback.lift t.left _ _ ≫ pullback.fst _ _ ≫ T.hom = T'.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w t)
  lift_π {T'} t a := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  res_lift {T'} t a := by
    have h := ptsZ_comp (pullback.lift t.left ((ptsZ T'.left).symm a) (terminal.hom_ext _ _))
      (toAZ N T.left)
    have e : pullback.lift t.left ((ptsZ T'.left).symm a) (terminal.hom_ext _ _) ≫ toAZ N T.left =
        (ptsZ T'.left).symm a := pullback.lift_snd _ _ _
    rw [e] at h
    exact h.symm.trans ((ptsZ T'.left).apply_symm_apply a)
  uniq {T'} t a s h1 h2 := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · refine Eq.trans (congrArg (fun k => k.left) h1) ?_
      exact (pullback.lift_fst _ _ _).symm
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      apply (ptsZ T'.left).injective
      exact (ptsZ_comp s.left (toAZ N T.left)).trans
        (h2.trans ((ptsZ T'.left).apply_symm_apply a).symm)

end Monoid

end Relative

end AlgMag.GB
