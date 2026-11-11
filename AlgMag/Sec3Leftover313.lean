/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Final

/-!
# Algebraic Magnetism, Remark 3.13, second assertion

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026): the sanitary check
`(X^N_M)^L_M = (X^N_M)^{(N ∩ L)}_N`, under the working assumption `X` affine over `S`, by Proposition 3.31.
On the left `X^N` carries the action of Remark 3.11, on the right that of Remark 3.12.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag

namespace GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N L : AddSubmonoid M)

instance instAffineZatt : IsAffineHom (Zatt act N).hom := by
  have h : (iAtt act N).left ≫ X.hom = (Zatt act N).hom := Over.w (iAtt act N)
  rw [← h]
  infer_instance

/-- `yoneda (Zatt) ≅ X^N` on points. -/
def zE (U : (Over S)ᵒᵖ) : (yoneda.obj (Zatt act N)).obj U ≃ (attractor act N).obj U :=
  (representsAttractor act N).equiv (unop U)

/-- The action of `𝔸(N)_S` of Remark 3.12, on the scheme `X^N`. -/
def zAct : AAction (overO S) N (yoneda.obj (Zatt act N)) where
  smul {U} h x := (zE act N U).symm ((magnetAction act N).smul h (zE act N U x))
  one_smul {U} x := by simp [(magnetAction act N).one_smul]
  mul_smul {U} g h x := by simp [(magnetAction act N).mul_smul]
  map_smul {U V} s h x := by
    apply (zE act N V).injective
    have he : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x : (yoneda.obj (Zatt act N)).obj U),
        zE act N V ((yoneda.obj (Zatt act N)).map s x) =
          (attractor act N).map s (zE act N U x) := fun {U V} s x =>
      (representsAttractor act N).naturality s.unop x
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, he]
    exact (magnetAction act N).map_smul s h _

lemma zE_natural {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x : (yoneda.obj (Zatt act N)).obj U) :
    zE act N V ((yoneda.obj (Zatt act N)).map s x) = (attractor act N).map s (zE act N U x) :=
  (representsAttractor act N).naturality s.unop x

/-- The action of `𝔸(M)_S` of Remark 3.11, on the scheme `X^N`: pull back along `N → M`. -/
abbrev zActM : AAction (overO S) M (yoneda.obj (Zatt act N)) := (zAct act N).comap N.subtype

/-- `zAct` is the action of Remark 3.12 under `X^N = Zatt`. -/
lemma zE_zAct {U : (Over S)ᵒᵖ} (h : APt (overO S) N U) (x : (yoneda.obj (Zatt act N)).obj U) :
    zE act N U ((zAct act N).smul h x) = (magnetAction act N).smul h (zE act N U x) :=
  (zE act N U).apply_symm_apply _

/-- **Remark 3.13**, first assertion on the scheme: `zActM` is the action of Remark 3.11. -/
lemma zE_zActM {U : (Over S)ᵒᵖ} (h : APt (overO S) M U) (x : (yoneda.obj (Zatt act N)).obj U) :
    zE act N U ((zActM act N).smul h x) = (attractorAction act N).smul h (zE act N U x) := by
  refine ((zE act N U).apply_symm_apply _).trans ?_
  exact (attractorAction_smul_eq act N h _).symm

/-- **Remark 3.13**, second assertion, `X` affine over `S`, with `S` any scheme and `T` any `S`-scheme:
`(X^N)^{N ∩ L}_N = (X^N)^L_M` on `T`-points. `X^N` is the scheme `Zatt` of Theorem 3.20; `N ∩ L` is the magnet
`L.comap N.subtype` of `N`; the action on the left is that of Remark 3.12, on the right that of Remark 3.11.
This is the canonical map of Proposition 3.31 (i). -/
def rem313 (T : Over S) :
    AttractorPt (zAct act N) (L.comap N.subtype) T ≃ AttractorPt (zActM act N) L T :=
  Equiv.ofBijective _ (prop331_i (zAct act N) N.subtype L T)

/-- The identification of Remark 3.13 preserves the underlying point of `X^N`. -/
theorem rem313_toPoint (T : Over S) (φ : AttractorPt (zAct act N) (L.comap N.subtype) T) :
    (rem313 act N L T φ).toPoint = φ.toPoint :=
  AttractorPt.toPoint_along _ _ φ

end GB

end AlgMag
