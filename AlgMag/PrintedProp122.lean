/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesCor
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleUniversallyInjectiveOpenImmersion

/-!
# Proposition 12.2 (i) for algebraic spaces: the printed proof

Mayeux, *Algebraic Magnetism*, Proposition 12.2 (i), along the printed route: `f` is smooth, so `f^N` is
smooth by Corollary 11.2, hence locally of finite presentation and flat (Tag 04TA); it is a monomorphism by
Fact 3.18; so universally injective and unramified (Tags 05VH, 05W6); étale by Tag 06LU; an open
immersion by Tag 05W5. The direct proof `AlgMag.Sec12Spaces.isOpenImmersion_repAttractorMap` stays.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M] (N : AddSubmonoid M)
  {X Y Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

/-- **Proposition 12.2 (i)**, printed proof. -/
theorem prop122_i_printed (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZx : IsAlgebraicSpace B S hS Zx) (hZy : IsAlgebraicSpace B S hS Zy)
    (f : EquivariantHom aX aY) (hf : Space.IsOpenImmersion B S hS f.hom)
    (rx : RepresentsAttractor aX N Zx) (ry : RepresentsAttractor aY N Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, ry.equiv T (z.app (op T) w) = AttractorPt.push f (rx.equiv T w)) :
    Space.IsOpenImmersion B S hS z := by
  -- `f` is smooth, so `f^N` is smooth by Corollary 11.2
  have hs : Space.IsSmooth B S hS f.hom :=
    Space.isSmooth_of_isEtale B S hS hY (Space.isEtale_of_isOpenImmersion B S hS hf)
  have hsz := isSmooth_repMap_spaces N hX hY hZx hZy f hs rx ry z hz
  -- locally of finite presentation and flat, Tag 04TA
  have hlfp := Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsz
  have hflat := Space.isFlat_of_isSmooth B S hS z hsz
  -- a monomorphism by Fact 3.18
  have hmf : Mono f.hom := Space.mono_of_isOpenImmersion B S hS f.hom hf
  have hinj : ∀ U, Function.Injective (f.hom.app U) := fun U =>
    (mono_iff_injective (f.hom.app U)).1 inferInstance
  have hmz : Mono z := by
    refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun a b h => ?_
    apply (rx.equiv (unop T)).injective
    apply attractorMap_injective f N hinj T
    change AttractorPt.push f _ = AttractorPt.push f _
    rw [← hz, ← hz]
    exact congrArg _ h
  -- universally injective and unramified, Tags 05VH, 05W6
  have hunr := Space.isUnramified_of_isLocallyOfFiniteType_of_mono B S hS z
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp) hmz
  have hui := ((Space.isUnramified_mono_iff_isUnramified_universallyInjective B S hS hZx hZy z).1
    ⟨hunr, hmz⟩).2
  -- étale by Tag 06LU, open immersion by Tag 05W5
  have he := Space.isEtale_of_isFlat_of_isUnramified B S hS hZx hZy z hlfp hflat hunr
  exact Space.isOpenImmersion_of_isEtale_of_universallyInjective B S hS hZx hZy z he hui

end AlgMag.SpacesLift

#print axioms AlgMag.SpacesLift.prop122_i_printed
