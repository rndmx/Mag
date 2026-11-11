/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11Formal
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# §11 for algebraic spaces: the part following from Corollary 10.3

Mayeux, *Algebraic Magnetism*, §11. These are the printed deductions of Propositions 11.1, 11.5
and Corollary 11.2. Corollary 10.3 for algebraic spaces, on the thickening `𝔸(N)_{T₀} → 𝔸(N)_T`
(`Lift103`), and local finite presentation of the represented morphism (Fact 3.19), are hypotheses
here: they are not proved for algebraic spaces in this file.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u w

namespace AlgMag.Sec11Spaces

section General

variable {C : Type*} [Category C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
  {X Y : Cᵒᵖ ⥤ Type u} {aX : AAction 𝒪 M X} {aY : AAction 𝒪 M Y}

/-- The conclusion of Corollary 10.3 for the square of the proof of Proposition 11.1. -/
def Lift103 (Th : ∀ {U V : C}, (U ⟶ V) → Prop) (f : EquivariantHom aX aY) (N : AddSubmonoid M) :
    Prop :=
  ∀ {T₀ T : C} (i : T₀ ⟶ T), Th i → ∃ (U₀ : UniversalPoint 𝒪 N T₀) (U : UniversalPoint 𝒪 N T),
    ∀ (x₀ : AttractorPt aX N T₀) (y : AttractorPt aY N T),
      f.hom.app _ (x₀.app U₀.π U₀.u) = Y.map (U.lift (U₀.π ≫ i) U₀.u).op (y.app U.π U.u) →
      ∃ l : AttractorPt aX N T,
        X.map (U.lift (U₀.π ≫ i) U₀.u).op (l.app U.π U.u) = x₀.app U₀.π U₀.u ∧
        f.hom.app _ (l.app U.π U.u) = y.app U.π U.u

/-- **Proposition 11.1**, the printed deduction from Corollary 10.3 (`Lift103`). -/
theorem formallySmoothFor_attractorMap_of_lift (Th : ∀ {U V : C}, (U ⟶ V) → Prop)
    (f : EquivariantHom aX aY) (N : AddSubmonoid M) (h : Lift103 Th f N) :
    FormallySmoothFor Th (attractorMap f N) := by
  intro T₀ T i hi x₀ y hc
  obtain ⟨U₀, U, hU⟩ := h i hi
  have e : f.hom.app _ (x₀.app U₀.π U₀.u) =
      Y.map (U.lift (U₀.π ≫ i) U₀.u).op (y.app U.π U.u) :=
    (congrArg (fun z : AttractorPt aY N T₀ => z.app U₀.π U₀.u) hc).trans
      (y.app_eq_of_universal U _ _)
  obtain ⟨l, h₁, h₂⟩ := hU x₀ y e
  refine ⟨l, ?_, ?_⟩
  · refine (attractorPtEquivOfUniversal (act := aX) U₀).injective (Subtype.ext ?_)
    exact (l.app_eq_of_universal U _ _).trans h₁
  · refine (attractorPtEquivOfUniversal (act := aY) U).injective (Subtype.ext ?_)
    exact h₂

end General

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

lemma isAffineThickening_of_squareZero {T T' : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) (i : T ⟶ T')
    (hi : Space.IsSquareZeroClosedImmersion B S hS i) : IsAffineThickening i := by
  have h₁ : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  refine ⟨hT, hT', (IsClosedImmersion.isAffine_surjective_of_isAffine _).2, ?_⟩
  have h2 := (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine
    ((BigFppfOver.toScheme B S hS).map i) 2).1 hi.2
  intro x y hx hy
  have : x * y ∈ RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  rw [h2] at this
  exact this

/-- A transformation of represented functors which is formally smooth on affine thickenings
is formally smooth in the sense of Stacks (Tag 049S). -/
theorem formallySmooth_of_rep {FX FY : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    {Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : FX ⟶ FY)
    (hm : IsFormallySmooth m)
    (rx : ∀ T, Zx.obj (op T) ≃ FX.obj (op T)) (ry : ∀ T, Zy.obj (op T) ≃ FY.obj (op T))
    (nx : ∀ {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (w), rx T' (Zx.map s.op w) = FX.map s.op (rx T w))
    (ny : ∀ {T T' : BigFppfOver B S hS} (s : T' ⟶ T) (w), ry T' (Zy.map s.op w) = FY.map s.op (ry T w))
    (z : Zx ⟶ Zy) (hz : ∀ T w, ry T (z.app (op T) w) = m.app (op T) (rx T w)) :
    Space.FormallySmooth z := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨l, h₁, h₂⟩ := hm i (isAffineThickening_of_squareZero hT hT' i hi) (rx T x) (ry T' y) (by
    rw [← hz, hxy, ny])
  refine ⟨(rx T').symm l, ?_, ?_⟩
  · refine (rx T).injective ?_
    rw [nx, Equiv.apply_symm_apply, h₁]
  · refine (ry T').injective ?_
    rw [hz, Equiv.apply_symm_apply, h₂]

variable {M : Type u} [AddCommGroup M] {X Y Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {aX : AAction (fppfO B S hS) M X} {aY : AAction (fppfO B S hS) M Y} (N : AddSubmonoid M)

/-- **Proposition 11.1** for functors on the big fppf site, from Corollary 10.3 (`Lift103`). -/
theorem isFormallySmooth_attractorMap (f : EquivariantHom aX aY)
    (h : Lift103 (fun {_ _} i => IsAffineThickening i) f N) :
    IsFormallySmooth (attractorMap f N) :=
  formallySmoothFor_attractorMap_of_lift _ f N h

/-- **Proposition 11.5**, from Corollary 10.3 (`Lift103`) and Proposition 11.3: formally smooth and
formally unramified. -/
theorem isFormallyEtale_attractorMap (f : EquivariantHom aX aY)
    (h : Lift103 (fun {_ _} i => IsAffineThickening i) f N) (hN : MagnetInSite N B S hS)
    (hf : IsFormallyUnramified f.hom) :
    IsFormallySmooth (attractorMap f N) ∧ IsFormallyUnramified (attractorMap f N) :=
  ⟨isFormallySmooth_attractorMap N f h, AlgMag.isFormallyUnramified_attractorMap N f hN hf⟩

/-- **Corollary 11.2**, from Corollary 10.3 (`Lift103`) and local finite presentation of `z`
(Fact 3.19), by Tag 04AM. -/
theorem isSmooth_repMap (f : EquivariantHom aX aY)
    (h : Lift103 (fun {_ _} i => IsAffineThickening i) f N)
    (rx : RepresentsAttractor aX N Zx) (ry : RepresentsAttractor aY N Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, ry.equiv T (z.app (op T) w) = AttractorPt.push f (rx.equiv T w))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS z) : Space.IsSmooth B S hS z :=
  Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth hlfp
    (formallySmooth_of_rep (attractorMap f N) (isFormallySmooth_attractorMap N f h) rx.equiv ry.equiv
      (fun s w => rx.naturality s w) (fun s w => ry.naturality s w) z hz)

/-- **Corollary 11.10**, from the conclusion of Proposition 11.7 (`hm`, not proved here for algebraic
spaces) and local finite presentation of `z`, by Tag 04AM. -/
theorem isSmooth_repFace (act : AAction (fppfO B S hS) M X) {F : AddSubmonoid M} (hF : IsFace F N)
    (hm : IsFormallySmooth (faceMap act hF))
    (rx : RepresentsAttractor act N Zx) (rf : RepresentsAttractor act F Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, rf.equiv T (z.app (op T) w) = AttractorPt.ofFace hF (rx.equiv T w))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS z) : Space.IsSmooth B S hS z :=
  Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth hlfp
    (formallySmooth_of_rep (faceMap act hF) hm rx.equiv rf.equiv
      (fun s w => rx.naturality s w) (fun s w => rf.naturality s w) z hz)

end Site

end AlgMag.Sec11Spaces
