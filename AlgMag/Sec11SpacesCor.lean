/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesFact
import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationCancellation

/-!
# §11 for algebraic spaces: the statements

Mayeux, *Algebraic Magnetism*, Propositions 11.1, 11.5, 11.7 and Corollaries 11.2, 11.6, 11.10, for
algebraic spaces `X`, `Y`. The only condition beyond the printed statements is the site cutoff
`SM B M`: `#M` is below the cutoff of the site. `M` is any commutative group and `N` any magnet.

Proposition 11.1 is `AlgMag.SpacesLift.isFormallySmooth_attractorMap_spaces`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M] (N : AddSubmonoid M)

lemma magnetInSite : MagnetInSite N B S hS := fun T hT => by
  haveI : IsAffine (τS T) := hT
  exact (inferInstance : SR B (RS N (τS T))).contains

lemma squareZero_of_thick {T T' : BigFppfOver B S hS} {i : T ⟶ T'} (hi : IsAffineThickening i) :
    Space.IsSquareZeroClosedImmersion B S hS i := by
  have := hi.affine₀
  have := hi.affine
  have hc : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    IsClosedImmersion.of_surjective_of_isAffine _ hi.surjective
  refine ⟨hc, (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ 2).2 ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx z hz
  exact hi.sq_zero x z hx hz

variable {X Y Zx Zy : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {aY : AAction (fppfO B S hS) M Y}

lemma unram_of_etale (f : EquivariantHom aX aY) (hf : Space.FormallyEtale f.hom) :
    IsFormallyUnramified f.hom := by
  intro T₀ T i hi x y h₀ h₁
  have hc : f.hom.app _ (X.map i.op x) = Y.map i.op (f.hom.app _ y) := by
    rw [NatTrans.naturality_apply, h₁]
  exact (hf _ _ hi.affine₀ hi.affine i (squareZero_of_thick hi) (X.map i.op x) _ hc).unique
    ⟨rfl, h₁⟩ ⟨h₀.symm, rfl⟩

/-- **Proposition 11.5** for algebraic spaces: if `f` is formally étale, `f^N` is formally étale as a
transformation of functors, i.e. formally smooth and formally unramified. -/
theorem isFormallyEtale_attractorMap_spaces (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : EquivariantHom aX aY)
    (hf : Space.FormallyEtale f.hom) :
    IsFormallySmooth (attractorMap f N) ∧ IsFormallyUnramified (attractorMap f N) :=
  isFormallyEtale_attractorMap N f
    (lift103 N hX hY f fun T T' hT hT' i hi x y h => (hf T T' hT hT' i hi x y h).exists)
    (magnetInSite N) (unram_of_etale f hf)

/-- **Corollary 11.2** for algebraic spaces: if `f : X → Y` is smooth and `X^N`, `Y^N` are representable
by algebraic spaces, then `X^N → Y^N` is smooth. -/
theorem isSmooth_repMap_spaces (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZx : IsAlgebraicSpace B S hS Zx) (hZy : IsAlgebraicSpace B S hS Zy)
    (f : EquivariantHom aX aY) (hf : Space.IsSmooth B S hS f.hom)
    (rx : RepresentsAttractor aX N Zx) (ry : RepresentsAttractor aY N Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, ry.equiv T (z.app (op T) w) = AttractorPt.push f (rx.equiv T w)) :
    Space.IsSmooth B S hS z := by
  obtain ⟨h₁, h₂⟩ := (Space.isSmooth_iff_isLocallyOfFinitePresentation_and_formallySmooth hX hY _).1 hf
  exact isSmooth_repMap N f (lift103 N hX hY f h₂) rx ry z hz
    (isLocallyOfFinitePresentation_repMap_spaces N hX hY hZx hZy f h₁ rx ry z hz)

/-- **Corollary 11.6** for algebraic spaces: if `f : X → Y` is étale and `X^N`, `Y^N` are representable
by algebraic spaces, then `X^N → Y^N` is étale. -/
theorem isEtale_repMap_spaces (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZx : IsAlgebraicSpace B S hS Zx) (hZy : IsAlgebraicSpace B S hS Zy)
    (f : EquivariantHom aX aY) (hf : Space.IsEtale B S hS f.hom)
    (rx : RepresentsAttractor aX N Zx) (ry : RepresentsAttractor aY N Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, ry.equiv T (z.app (op T) w) = AttractorPt.push f (rx.equiv T w)) :
    Space.IsEtale B S hS z := by
  obtain ⟨h₁, h₂⟩ :=
    (Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS hX hY _).1 hf
  have hs : IsFormallySmooth (attractorMap f N) ∧ IsFormallyUnramified (attractorMap f N) :=
    isFormallyEtale_attractorMap_spaces N hX hY f h₂
  have hfs : Space.FormallySmooth z :=
    formallySmooth_of_rep (attractorMap f N) hs.1 rx.equiv ry.equiv
      (fun s w => rx.naturality s w) (fun s w => ry.naturality s w) z hz
  have hfu : IsFormallyUnramified z :=
    isFormallyUnramified_of_represents N f (magnetInSite N) (unram_of_etale f h₂) rx ry z hz
  refine (Space.isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS hZx hZy _).2
    ⟨isLocallyOfFinitePresentation_repMap_spaces N hX hY hZx hZy f h₁ rx ry z hz, ?_⟩
  intro T T' hT hT' i hi x y hxy
  obtain ⟨w, hw⟩ := hfs T T' hT hT' i hi x y hxy
  exact ⟨w, hw, fun v hv => hfu i (isAffineThickening_of_squareZero hT hT' i hi) _ _
    (hv.1.trans hw.1.symm) (hv.2.trans hw.2.symm)⟩

section Face

variable (B S hS) in
lemma isAlgebraicSpace_top : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) := by
  let t : IsTerminal (yoneda.obj (Ter B S hS)) := IsTerminal.isTerminalObj yoneda _
    (Over.mkIdTerminal (X := B.obj hS))
  let e : yoneda.obj (Ter B S hS) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    t.uniqueUpToIso terminalIsTerminal
  exact isAlgebraicSpace_of_relativelyRepresentable B S hS e.inv
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv) (isAlgebraicSpace_yoneda B S hS _)

/-- The trivial action on the terminal presheaf. -/
noncomputable def topAct : AAction (fppfO B S hS) M (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := top_eq _ _

/-- The terminal presheaf represents its own attractors. -/
noncomputable def repTop : RepresentsAttractor (topAct (B := B) (S := S) (hS := hS) (M := M)) N
    (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) where
  equiv T :=
    { toFun := fun w =>
        { app := fun {T'} t _ => (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).map t.op w
          naturality := fun _ _ _ => top_eq _ _
          equivariant := fun _ _ _ => top_eq _ _ }
      invFun := fun φ => (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).map (𝟙 _) (φ.app (𝟙 T) 1)
      left_inv := fun _ => top_eq _ _
      right_inv := fun φ => by
        refine AttractorPt.ext ?_
        funext T₁ t a
        exact top_eq _ _ }
  naturality _ _ := by
    refine AttractorPt.ext ?_
    funext T₁ t a
    exact top_eq _ _

/-- A representing space of an attractor of a space locally of finite presentation over `S` is locally
of finite presentation over `S` (Fact 3.19). -/
theorem isLocallyOfFinitePresentation_rep_spaces (hX : IsAlgebraicSpace B S hS X)
    (hZx : IsAlgebraicSpace B S hS Zx) (act : AAction (fppfO B S hS) M X)
    (hf : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (rx : RepresentsAttractor act N Zx) :
    Space.IsLocallyOfFinitePresentation B S hS (terminal.from Zx) := by
  let eqT : EquivariantHom act (topAct (B := B) (S := S) (hS := hS) (M := M)) :=
    { hom := terminal.from X
      map_smul := fun _ _ => top_eq _ _ }
  refine isLocallyOfFinitePresentation_repMap_spaces N hX (isAlgebraicSpace_top B S hS) hZx
    (isAlgebraicSpace_top B S hS) eqT hf rx (repTop N) _ fun T w => ?_
  refine AttractorPt.ext ?_
  funext T₁ t a
  exact top_eq _ _

variable {F : AddSubmonoid M} (hF : IsFace F N)

/-- **Proposition 11.7** for algebraic spaces: if `X → S` is smooth and `F` is a face of `N`, then
`X^N → X^F` is formally smooth as a transformation of functors. -/
theorem isFormallySmooth_faceMap_of_isSmooth (hX : IsAlgebraicSpace B S hS X)
    (act : AAction (fppfO B S hS) M X)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) : IsFormallySmooth (faceMap act hF) :=
  isFormallySmooth_faceMap_spaces N hF hX act
    ((Space.isSmooth_iff_isLocallyOfFinitePresentation_and_formallySmooth hX
      (isAlgebraicSpace_top B S hS) _).1 hsm).2

/-- **Corollary 11.10** for algebraic spaces: if `X → S` is smooth, `F` a face of `N`, and `X^N`, `X^F`
are representable by algebraic spaces, then `X^N → X^F` is smooth. -/
theorem isSmooth_repFace_spaces (hX : IsAlgebraicSpace B S hS X)
    (hZx : IsAlgebraicSpace B S hS Zx) (hZy : IsAlgebraicSpace B S hS Zy)
    (act : AAction (fppfO B S hS) M X) (hsm : Space.IsSmooth B S hS (terminal.from X))
    (rx : RepresentsAttractor act N Zx) (rf : RepresentsAttractor act F Zy) (z : Zx ⟶ Zy)
    (hz : ∀ T w, rf.equiv T (z.app (op T) w) = AttractorPt.ofFace hF (rx.equiv T w)) :
    Space.IsSmooth B S hS z := by
  obtain ⟨h₁, h₂⟩ := (Space.isSmooth_iff_isLocallyOfFinitePresentation_and_formallySmooth hX
    (isAlgebraicSpace_top B S hS) _).1 hsm
  have hx := isLocallyOfFinitePresentation_rep_spaces N hX hZx act h₁ rx
  have hy := isLocallyOfFinitePresentation_rep_spaces F hX hZy act h₁ rf
  have hcomp : z ≫ terminal.from Zy = terminal.from Zx := terminal.hom_ext _ _
  have hlfp : Space.IsLocallyOfFinitePresentation B S hS z :=
    Space.isLocallyOfFinitePresentation_of_comp B S hS hZx hZy (isAlgebraicSpace_top B S hS) z
      (terminal.from Zy) (by rw [hcomp]; exact hx)
      (fun U V a b h ha hb hsq => by
        have := hy U V a b h ha hb hsq
        infer_instance)
  exact Space.isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth hlfp
    (formallySmooth_of_rep (faceMap act hF) (isFormallySmooth_faceMap_spaces N hF hX act h₂)
      rx.equiv rf.equiv (fun s w => rx.naturality s w) (fun s w => rf.naturality s w) z hz)

end Face

end AlgMag.SpacesLift
