/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCBaseLocal2
import AlgMag.FinalNonQCSmallAtlas

/-!
# The attractor functor restricted to the site of an object

For `X` separated, the restriction of `X^K` to the site of `T₀` represents the attractor of the restriction of `X`, so it is
identified with any presheaf representing that attractor, compatibly with the maps of Theorem 8.3.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {act : AAction (fppfO B S hS) M X}

noncomputable section

/-- The map `X^K ⟶ X`. -/
def attToX (act : AAction (fppfO B S hS) M X) (K : AddSubmonoid M) : attP act K ⟶ X where
  app T := ↾ fun p => ((attPRep act K).equiv (unop T) p).toPoint
  naturality T T' s := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    change ((attPRep act K).equiv (unop T') ((attP act K).map s p)).toPoint =
      X.map s ((attPRep act K).equiv (unop T) p).toPoint
    have := (attPRep act K).naturality s.unop p
    rw [show (attP act K).map s = (attP act K).map s.unop.op from rfl, this,
      AttractorPt.toPoint_baseChange]
    rfl

/-- The map `X^N ⟶ X^L` for a face `L`. -/
def attFace (act : AAction (fppfO B S hS) M X) {L N : AddSubmonoid M} (hF : IsFace L N) :
    attP act N ⟶ attP act L where
  app T := ↾ fun p => ((attPRep act L).equiv (unop T)).symm
    (AttractorPt.ofFace hF ((attPRep act N).equiv (unop T) p))
  naturality T T' s := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    refine ((attPRep act L).equiv (unop T')).injective ?_
    have h1 := (attPRep act L).naturality s.unop
      (((attPRep act L).equiv (unop T)).symm (AttractorPt.ofFace hF ((attPRep act N).equiv (unop T) p)))
    have h2 := (attPRep act N).naturality s.unop p
    change (attPRep act L).equiv (unop T') (((attPRep act L).equiv (unop T')).symm
        (AttractorPt.ofFace hF ((attPRep act N).equiv (unop T') ((attP act N).map s.unop.op p)))) =
      (attPRep act L).equiv (unop T') ((attP act L).map s.unop.op
        (((attPRep act L).equiv (unop T)).symm (AttractorPt.ofFace hF ((attPRep act N).equiv (unop T) p))))
    rw [Equiv.apply_symm_apply, h1, h2, Equiv.apply_symm_apply, ofFace_baseChange]

variable (T₀ : BigFppfOver B S hS) {K : AddSubmonoid M} {Q : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ ⥤ Type u}

/-- Injectivity of `toPoint`, on both sites. -/
structure InjData (act : AAction (fppfO B S hS) M X) (T₀ : BigFppfOver B S hS) : Prop where
  S_inj : ∀ (K : AddSubmonoid M) (T : BigFppfOver B S hS),
    Function.Injective (AttractorPt.toPoint (act := act) (N := K) (T := T))
  R_inj : ∀ (K : AddSubmonoid M) (T : BigFppfOver B T₀.left.1 T₀.left.2),
    Function.Injective (AttractorPt.toPoint (act := resAct (T₀ := T₀) act) (N := K) (T := T))

variable {T₀}

theorem injData (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X) :
    InjData act T₀ :=
  ⟨fun K T => attractor_toPoint_injective_sep (aX := act) hX (isSeparatedOver_iff_space.1 hsep) K T,
    fun K T => attractor_toPoint_injective_sep (aX := resAct (T₀ := T₀) act) (res_alg T₀ hX)
      (isSeparatedOver_iff_space.1 (res_sep T₀ hX hsep)) K T⟩

lemma attrDown_baseChange (hI : InjData act T₀) {W W' : BigFppfOver B T₀.left.1 T₀.left.2} (s : W' ⟶ W)
    (φ : AttractorPt act K ((Over.map T₀.hom).obj W)) :
    attrDown (AttractorPt.baseChange ((Over.map T₀.hom).map s) φ) =
      AttractorPt.baseChange s (attrDown φ) := by
  refine hI.R_inj K W' (Subtype.ext ?_)
  rw [attrDown_toPoint, AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange]
  change _ = ((Res X T₀).map s.op (attrDown φ).toPoint).1
  rw [fibreOfSection_map_val, attrDown_toPoint]
  rfl

/-- The fibrewise bijection. -/
def attResEquiv (hI : InjData act T₀) (rep : RepresentsAttractor (resAct (T₀ := T₀) act) K Q)
    (W : BigFppfOver B T₀.left.1 T₀.left.2) :
    (attP act K).obj (op ((Over.map T₀.hom).obj W)) ≃ Q.obj (op W) where
  toFun p := (rep.equiv W).symm (attrDown ((attPRep act K).equiv _ p))
  invFun q := ((attPRep act K).equiv _).symm (attrUp (rep.equiv W q))
  left_inv p := by
    refine ((attPRep act K).equiv _).injective ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine hI.S_inj K _ ?_
    rw [attrUp_toPoint, attrDown_toPoint]
  right_inv q := by
    refine (rep.equiv W).injective ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine hI.R_inj K W (Subtype.ext ?_)
    rw [attrDown_toPoint, attrUp_toPoint]

/-- The restriction of `X^K` to the site of `T₀` is any presheaf representing the attractor of the restriction. -/
def attResIso (hI : InjData act T₀) (rep : RepresentsAttractor (resAct (T₀ := T₀) act) K Q) :
    (relocalizeRestrict T₀.hom).obj (attP act K) ≅ Q :=
  NatIso.ofComponents (fun W => (attResEquiv hI rep W.unop).toIso) (by
    intro W W' s
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    refine (rep.equiv W'.unop).injective ?_
    change rep.equiv W'.unop ((rep.equiv W'.unop).symm (attrDown ((attPRep act K).equiv _
        ((attP act K).map ((Over.map T₀.hom).map s.unop).op p)))) =
      rep.equiv W'.unop (Q.map s.unop.op ((rep.equiv W.unop).symm (attrDown ((attPRep act K).equiv _ p))))
    rw [Equiv.apply_symm_apply, rep.naturality, Equiv.apply_symm_apply, (attPRep act K).naturality,
      attrDown_baseChange hI])

lemma attResIso_spec (hI : InjData act T₀) (rep : RepresentsAttractor (resAct (T₀ := T₀) act) K Q)
    (W : BigFppfOver B T₀.left.1 T₀.left.2) (p : (attP act K).obj (op ((Over.map T₀.hom).obj W))) :
    rep.equiv W ((attResIso hI rep).hom.app (op W) p) = attrDown ((attPRep act K).equiv _ p) :=
  Equiv.apply_symm_apply _ _

end

end AlgMag.Final
