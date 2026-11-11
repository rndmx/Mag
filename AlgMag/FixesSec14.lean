/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec14Strong

/-!
# Algebraic Magnetism, §14: the statements to cite

* `AlgMag.remark142`: **Remark 14.2**, `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)`, the bijection being the
  canonical map `AlgMag.indHomCanon`. `AlgMag.indHomEquiv_eq_canon`: the older `AlgMag.indHomEquiv` agrees.
* `AlgMag.remark142_of_quasiCompact`: the same with the printed hypothesis, `X_i` quasi-compact.
* `AlgMag.prop144_closed_corrected`: **Proposition 14.4**, last assertion, corrected: it is false as printed
  (`AlgMag/Sec14Counterexample.lean`), and holds with a `Z`-FPR atlas on each term.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section HomBijection

variable {P Q : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop} {X Y : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u}
  (pX : IndPresentation.{u, v, u} P X) (pY : IndPresentation.{u, v, u} Q Y)

/-- **Remark 14.2**: `Hom(X, Y) = lim_i colim_j Hom(X_i, Y_j)`, by the canonical map. -/
noncomputable def remark142
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) :
    (X ⟶ Y) ≃ IndHomLim pX pY :=
  Equiv.ofBijective (indHomCanon pX pY hZ hX) (indHomCanon_bijective pX pY hZ hX)

/-- **Remark 14.2**: the bijection sends `f` to the class of any factorization of `X_i → X → Y`
through `Y_j`. -/
theorem remark142_apply
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) (i : pX.I)
    (j : pY.I) (ψ : pX.obj i ⟶ pY.obj j)
    (h : ∀ (A : BigAffineFppf B S hS) (x : (pX.obj i).obj (op ((BigAffineFppf.inclusion B S hS).obj A))),
      pY.π j A (ψ.app _ x) = f.app _ (pX.π i A x)) :
    (remark142 pX pY hZ hX f).1 i = Quotient.mk (indHomRel pY _) ⟨j, ψ⟩ :=
  indHomCanon_eq_mk hZ hX f i j ψ h

/-- The older bijection `AlgMag.indHomEquiv` is the canonical map. -/
theorem indHomEquiv_eq_canon
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hX : ∀ i, IsFinitelyCovered (B := B) (S := S) (hS := hS) (pX.obj i)) (f : X ⟶ Y) :
    indHomEquiv pX pY hZ hX f = indHomCanon pX pY hZ hX f := by
  refine Subtype.ext (funext fun i => IndHomColim.ext_eval hZ fun A x => ?_)
  rw [indHomCanon_eval]
  exact Exists.choose_spec (p := fun c : IndHomColim pY (pX.obj i) =>
    ∀ (A : BigAffineFppf B S hS) (x : (pX.obj i).obj (op ((BigAffineFppf.inclusion B S hS).obj A))),
      c.eval pY A x = f.app _ (pX.π i A x)) _ A x

/-- **Remark 14.2** with its printed hypothesis: the terms `X_i` are quasi-compact algebraic spaces. -/
noncomputable def remark142_of_quasiCompact
    (hZ : ∀ j, Presieve.IsSheaf (BigFppfOver.topology B S hS) (pY.obj j))
    (hA : ∀ i, IsAlgebraicSpace B S hS (pX.obj i))
    (hq : ∀ i, Space.IsQuasiCompactSpace B S hS (pX.obj i)) :
    (X ⟶ Y) ≃ IndHomLim pX pY :=
  remark142 pX pY hZ fun i => isFinitelyCovered_of_isQuasiCompactSpace (hA i) (hq i)

end HomBijection

section Attractor

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M] [Countable M]
  {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
  {X : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P X}

/-- **Proposition 14.4**, last assertion, corrected: `Z` a subgroup of `M` and each `X_i` has a `Z`-FPR
atlas, the hypothesis of Proposition 8.1. Then `X^Z → X` is representable by a closed immersion: for
affine `T → X` the pullback `T ×_X X^Z` is a closed subspace of `T`, its `T'`-points over `t : T' → T`
being the points of `X^Z` above `T' → T → X`, naturally in `T'`.

As printed, without the atlas, the assertion is false: `AlgMag/Sec14Counterexample.lean`. -/
theorem prop144_closed_corrected (a : IndAction M p) (Z : AddSubgroup M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i)) (hat : ∀ i, ExistsZFPRAtlas (a.act i) Z) :
    IndAttractorMapHasPropNat a Z.toAddSubmonoid (fun f => IsClosedImm f) :=
  indAttractorMap_isClosedImm_nat a Z hX hat

end Attractor

end AlgMag

#print axioms AlgMag.remark142
#print axioms AlgMag.remark142_apply
#print axioms AlgMag.indHomEquiv_eq_canon
#print axioms AlgMag.remark142_of_quasiCompact
#print axioms AlgMag.prop144_closed_corrected
