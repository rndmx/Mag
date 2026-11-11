/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAttAlg

/-!
# Theorem 8.3 and Proposition 14.4 with `S` arbitrary, no atlas

`X` separated, locally of finite presentation, not necessarily quasi-compact, `S` not necessarily separated. The attractor functors are
algebraic spaces by `attP_alg`; "affine" and "closed immersion" are checked over the affine opens of `S` by `presheaf_of_openBase`, where
they are `thm83_nonqc`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe v u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (hZ : B.Contains (⊤_ Scheme.{u}))

noncomputable section

/-- `X` restricted to the site of `T₀`, in the two presentations. -/
def resIso (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T₀ : BigFppfOver B S hS) :
    (relocalizeRestrict T₀.hom).obj X ≅ Res X T₀ :=
  NatIso.ofComponents (fun W =>
    (show X.obj (op ((Over.map T₀.hom).obj W.unop)) ≃ (Res X T₀).obj W from
      { toFun := fun x => resMk x
        invFun := fun x => x.1
        left_inv := fun _ => rfl
        right_inv := fun _ => Subtype.ext rfl }).toIso)
    (fun {W W'} s => by
      refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
      rfl)

lemma attrDown_ofFace {act : AAction (fppfO B S hS) M X} {T₀ : BigFppfOver B S hS}
    {L N : AddSubmonoid M} (hF : IsFace L N) {W : BigFppfOver B T₀.left.1 T₀.left.2}
    (φ : AttractorPt act N ((Over.map T₀.hom).obj W)) :
    attrDown (AttractorPt.ofFace hF φ) = AttractorPt.ofFace hF (attrDown φ) :=
  AttractorPt.ext (by
    funext t c
    rfl)

include hZ in
/-- The representability part of **Theorem 8.3**: `S` arbitrary, `X` separated, locally of finite presentation, arbitrary magnet, no atlas. -/
theorem thm83_repr_general (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) : Nonempty (Thm83Repr act N) := by
  have hF := isFace_unitsSub N
  have hP := attP_alg hZ hM hX hsep hfp act N
  have hY := attP_alg hZ hM hX hsep hfp act (unitsSub N).toAddSubmonoid
  have hloc : ∀ O : S.affineOpens, ∃ r : Thm83Repr (resAct (T₀ := openBase (B := B) (hS := hS) O.1) act) N, True := by
    intro O
    let T₀ := openBase (B := B) (hS := hS) O.1
    have hA : IsAffine T₀.left.1 := isAffine_openBase (B := B) (hS := hS) O.2
    have hR := res_alg T₀ hX
    obtain ⟨r, -⟩ := thm83_nonqc hZ hM hR (res_sep T₀ hX hsep)
      ((lfp_toT1_iff hR).1 (res_lfp T₀ hX ((lfp_toT1_iff hX).2 hfp))) (resAct (T₀ := T₀) act) N
    exact ⟨r, trivial⟩
  refine ⟨{
    P := attP act N
    Y := attP act (unitsSub N).toAddSubmonoid
    c := attFace act hF
    i := attToX act _
    rP := attPRep act N
    rY := attPRep act _
    algP := hP
    algY := hY
    affine_c := ?_
    closed_i := ?_
    i_eq := fun _ _ => rfl
    c_eq := fun T p => Equiv.apply_symm_apply _ _ }⟩
  · refine presheaf_of_openBase (@HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine) hP hY _ fun O => ?_
    obtain ⟨r, -⟩ := hloc O
    have hI : InjData act (openBase (B := B) (hS := hS) O.1) := injData hX hsep
    let eP := attResIso hI r.rP
    let eY := attResIso hI r.rY
    have comm : eP.hom ≫ r.c = (relocalizeRestrict _).map (attFace act hF) ≫ eY.hom := by
      ext W p
      refine (r.rY.equiv W.unop).injective ?_
      have h1 := r.c_eq W.unop (eP.hom.app W p)
      have h2 := attResIso_spec hI r.rP W.unop p
      have h3 := attResIso_spec hI r.rY W.unop ((attFace act hF).app _ p)
      refine (h1.trans ?_).trans h3.symm
      refine (congrArg (AttractorPt.ofFace hF) h2).trans ?_
      have hc : (attPRep act (unitsSub N).toAddSubmonoid).equiv ((Over.map _).obj W.unop)
          ((attFace act hF).app (op ((Over.map (openBase (B := B) (hS := hS) O.1).hom).obj W.unop)) p) =
          AttractorPt.ofFace hF ((attPRep act N).equiv _ p) := Equiv.apply_symm_apply _ _
      exact (attrDown_ofFace hF _).symm.trans (congrArg attrDown hc.symm)
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso ⟨comm⟩) r.affine_c
  · refine presheaf_of_openBase inferInstance hY hX _ fun O => ?_
    obtain ⟨r, -⟩ := hloc O
    have hI : InjData act (openBase (B := B) (hS := hS) O.1) := injData hX hsep
    let eY := attResIso hI r.rY
    have comm : eY.hom ≫ r.i = (relocalizeRestrict _).map (attToX act _) ≫ (resIso X _).hom := by
      ext W p
      refine Subtype.ext ?_
      have h := attResIso_spec hI r.rY W.unop p
      change (r.i.app (op W.unop) (eY.hom.app (op W.unop) p)).1 = ((attPRep act _).equiv _ p).toPoint
      rw [r.i_eq, h, attrDown_toPoint]
    exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso ⟨comm⟩) r.closed_i

end

include hZ in
/-- **Theorem 8.3**, `X` separated, locally of finite presentation, not necessarily quasi-compact, arbitrary magnet, `S` arbitrary, no atlas
in the hypotheses. Representability; `X^N → X^{N^×}` affine; `X^{N^×} → X` closed immersion; quasi-separated, separated, quasi-compact and
locally of finite presentation conclusions. -/
theorem thm83_general (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (N : AddSubmonoid M) :
    ∃ r : Thm83Repr act N,
      Space.IsQuasiSeparated B S hS (toBase r.P) ∧ IsSeparatedOver r.P ∧
      (Space.IsQuasiCompactSpace B S hS X → Space.IsQuasiCompactSpace B S hS r.P) ∧
      Space.IsLocallyOfFinitePresentation B S hS (terminal.from r.P) := by
  obtain ⟨r⟩ := thm83_repr_general hZ hM hX hsep hfp act N
  have hs := thm83_sep hX (isSeparatedOver_iff_space.1 hsep) r
  exact ⟨r, Space.isQuasiSeparated_of_isSeparated B S hS hs, hs, fun hq =>
    isQuasiCompactSpace_of_presheaf (P := @AlgebraicGeometry.IsAffineHom) (fun g _ => inferInstance) r.affine_c
      (isQuasiCompactSpace_of_presheaf (P := @IsClosedImmersion) (fun g _ => inferInstance) r.closed_i hq),
    thm83_iv hX hfp r⟩

include hZ in
/-- **Proposition 14.4**, terms separated, locally of finite presentation, not necessarily quasi-compact, `S` arbitrary, no atlas. -/
theorem prop144_general (hM : B.Contains (Spec (ZMon M)))
    {P : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → Prop}
    {Xi : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type u} {p : IndPresentation.{u, v, u} P Xi}
    (a : IndAction M p) (N : AddSubmonoid M)
    (hX : ∀ i, IsAlgebraicSpace B S hS (p.obj i))
    (hsep : ∀ i, Space.IsSeparatedOver B S hS (p.obj i))
    (hfp : ∀ i, Space.IsLocallyOfFinitePresentation B S hS (terminal.from (p.obj i))) :
    IsIndAlgebraicSpace.{u, v} (attractor a.toAction N) :=
  haveI : Countable M := countable_of_fg83
  isIndAlgebraicSpace_attractor a N (fun i => attPRep (a.act i) N)
    (fun i => attP_alg hZ hM (hX i) (hsep i) (hfp i) (a.act i) N)

end AlgMag.Final

#print axioms AlgMag.Final.attP_alg
#print axioms AlgMag.Final.thm83_general
#print axioms AlgMag.Final.prop144_general
