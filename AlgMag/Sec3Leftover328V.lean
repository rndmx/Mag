/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover328
import AlgMag.Representation
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints

/-!
# Algebraic Magnetism, Proposition 3.28 for the scheme `V(E) = Spec_S (Sym E)`

`S` is any scheme and `E = ⨁_m E_m` a quasi-coherent `M`-graded `𝒪_S`-module. The scheme is the vector
bundle of the Stacks library, whose functor of points is `vectorBundleHomEquiv` (Tags 01M2, 01LQ).

* `AlgMag.VB.vActionS`: `𝔸(M)_S` acts linearly on `V(E)`.
* `AlgMag.VB.prop328`: `V(E_N)` represents `V(E)^N`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Scheme.Modules

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- The canonical map of the library is `resO`. -/
lemma underlying_eq_resO {W W' : Over S} (a : W' ⟶ W) :
    (AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap a) : pO W ⟶ pO W') = resO a := by
  refine pO_ext fun U x => ?_
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (pushforwardAlgebraMap_app a U (preimage_le a U))) x

variable (G : GrMod S M) [hq : ∀ m, (G.P m).IsQuasicoherent]

include hq in
theorem GrMod.isQuasicoherent_E : G.E.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit (D := Discrete.functor G.P)
    (fun k => hq k.as) G.isColimit

include hq in
theorem GrMod.isQuasicoherent_EN (N : AddSubmonoid M) : (G.EN N).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_colimit (Discrete.functor fun n : N => G.P n) (fun k => hq k.as)

/-- `V(E) = Spec_S (Sym E)`. -/
abbrev VE : Over S :=
  haveI := G.isQuasicoherent_E
  vectorBundleOver S (F := G.E)

/-- `V(E)(T) = Hom_{𝒪_S}(E, p_* 𝒪_T)`. -/
def eV (T : Over S) : (T ⟶ VE G) ≃ (G.E ⟶ pO T) :=
  haveI := G.isQuasicoherent_E
  vectorBundleHomEquiv G.E T

lemma eV_comp {T T' : Over S} (a : T' ⟶ T) (u : T ⟶ VE G) :
    eV G T' (a ≫ u) = eV G T u ≫ resO a := by
  haveI := G.isQuasicoherent_E
  exact (vectorBundleHomEquiv_comp G.E a u).trans (congrArg _ (underlying_eq_resO a))

/-- **Proposition 3.28**, first assertion: `𝔸(M)_S` acts linearly on `V(E)`. -/
def vActionS : AAction (overO S) M (yoneda.obj (VE G)) where
  smul {U} h u := (eV G (unop U)).symm (vSmul G (T := unop U) h (eV G (unop U) u))
  one_smul {U} u := by
    apply (eV G (unop U)).injective
    rw [Equiv.apply_symm_apply]
    exact vSmul_one G (T := unop U) _
  mul_smul {U} g h u := by
    apply (eV G (unop U)).injective
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact vSmul_mul G (T := unop U) g h _
  map_smul {U V} f h u := by
    apply (eV G (unop V)).injective
    change eV G (unop V) (f.unop ≫ (eV G (unop U)).symm _) =
      eV G (unop V) ((eV G (unop V)).symm (vSmul G (T := unop V) _ (eV G (unop V) (f.unop ≫ u))))
    rw [eV_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, eV_comp]
    exact vSmul_res G (T := unop U) (T' := unop V) f.unop h _

variable (N : AddSubmonoid M) {T : Over S}

/-- Attractor points for the scheme and for the module functor are the same. -/
def attrTransport : AttractorPt (vActionS G) N T ≃ AttractorPt (vAction G) N T where
  toFun φ :=
    { app := fun {T'} t a => eV G T' (φ.app t a)
      naturality := fun {T' T''} s t a => by
        rw [φ.naturality]
        exact eV_comp G s _
      equivariant := fun {T'} t h a => by
        rw [φ.equivariant]
        exact (eV G T').apply_symm_apply _ }
  invFun φ :=
    { app := fun {T'} t a => (eV G T').symm (φ.app t a)
      naturality := fun {T' T''} s t a => by
        apply (eV G T'').injective
        refine ((eV G T'').apply_symm_apply _).trans ((φ.naturality s t a).trans ?_)
        refine Eq.trans ?_ (eV_comp G s _).symm
        exact congrArg (· ≫ resO s) ((eV G T').apply_symm_apply _).symm
      equivariant := fun {T'} t h a => by
        apply (eV G T').injective
        refine ((eV G T').apply_symm_apply _).trans ((φ.equivariant t h a).trans ?_)
        refine Eq.trans ?_ ((eV G T').apply_symm_apply _).symm
        exact congrArg (vSmul G h) ((eV G T').apply_symm_apply _).symm }
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact (eV G T').symm_apply_apply _
  right_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    exact (eV G T').apply_symm_apply _

lemma attrTransport_baseChange {T T' : Over S} (s : T' ⟶ T) (ψ : AttractorPt (vActionS G) N T) :
    attrTransport G N (ψ.baseChange s) = (attrTransport G N ψ).baseChange s := rfl

/-- `V(E_N)`. -/
abbrev VEN : Over S :=
  haveI := G.isQuasicoherent_EN N
  vectorBundleOver S (F := G.EN N)

/-- **Proposition 3.28.** Let `S` be a scheme and `E` a quasi-coherent `M`-graded `𝒪_S`-module. Then
`V(E)^N` is canonically `V(E_N)`, with `E_N = ⨁_{n ∈ N} E_n`. -/
def prop328 : RepresentsAttractor (vActionS G) N (yoneda.obj (VEN G N)) where
  equiv T :=
    haveI := G.isQuasicoherent_EN N
    ((vectorBundleHomEquiv (G.EN N) T).trans (vAttractorEquiv G N T).symm).trans
      (attrTransport G N).symm
  naturality {T T'} s z := by
    haveI := G.isQuasicoherent_EN N
    have h1 := (vectorBundleHomEquiv_comp (G.EN N) s z).trans (congrArg _ (underlying_eq_resO s))
    apply (attrTransport G N).injective
    refine ((attrTransport G N).apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (attrTransport_baseChange G N s _).symm
    refine Eq.trans ?_ (congrArg (AttractorPt.baseChange s)
      ((attrTransport G N).apply_symm_apply _).symm)
    apply (vAttractorEquiv G N T').injective
    refine ((vAttractorEquiv G N T').apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (vAttractorEquiv_baseChange G N s _).symm
    refine h1.trans ?_
    exact congrArg (· ≫ resO s) ((vAttractorEquiv G N T).apply_symm_apply _).symm

end AlgMag.VB
