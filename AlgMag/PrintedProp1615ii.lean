/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftover1615Spaces
import AlgMag.SecLeftover1615

/-!
# Proposition 16.15 (ii) of *Algebraic Magnetism*, no representability

The printed proof of (ii) invokes Corollary 11.10, whose statement assumes `X^N`, `X^F` representable. What
the proof needs without that assumption is its source, Proposition 11.1 and Proposition 11.7: formal
smoothness as transformations of functors. So here `G` is a smooth group algebraic space and nothing is
assumed on the attractors. The site cutoff is `SM B M`, as in `AlgMag.Sec11SpacesCor`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag.Leftover

open AlgMag.GB AlgMag.SpacesLift AlgMag.Sec11Spaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M]

/-- The constant presheaf on a point is terminal. -/
noncomputable def constTerminal (C : Type*) [Category C] : IsTerminal ((Functor.const Cᵒᵖ).obj PUnit.{v + 1}) :=
  IsTerminal.ofUniqueHom (fun F => { app := fun _ => ↾ fun _ => PUnit.unit })
    (fun F m => by ext U x; rfl)

noncomputable def topIso (C : Type*) [Category C] :
    (⊤_ (Cᵒᵖ ⥤ Type v)) ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  terminalIsoIsTerminal (constTerminal C)

/-- Two points of the terminal presheaf agree, in any universe. -/
lemma top_ext {C : Type*} [Category C] {U : Cᵒᵖ} (a b : (⊤_ (Cᵒᵖ ⥤ Type v)).obj U) : a = b := by
  have h : ((topIso C).hom ≫ (topIso C).inv).app U a = ((topIso C).hom ≫ (topIso C).inv).app U b := rfl
  simpa using h

/-- The point of the terminal presheaf. -/
noncomputable def topPt {C : Type*} [Category C] (U : Cᵒᵖ) : (⊤_ (Cᵒᵖ ⥤ Type v)).obj U :=
  (topIso C).inv.app U PUnit.unit

/-- `X^N → S` is formally smooth as a transformation of functors, if `X → S` is smooth (Proposition 11.1
with target `S`). No representability of `X^N`. -/
theorem isFormallySmooth_attractor_terminal (N : AddSubmonoid M) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (act : AAction (fppfO B S hS) M X)
    (hsm : Space.IsSmooth B S hS (terminal.from X)) :
    IsFormallySmooth (terminal.from (attractor act N)) := by
  let eqT : EquivariantHom act (topAct (B := B) (S := S) (hS := hS) (M := M)) :=
    { hom := terminal.from X
      map_smul := fun _ _ => top_eq _ _ }
  have h : IsFormallySmooth (attractorMap eqT N) := isFormallySmooth_attractorMap_spaces N hX (isAlgebraicSpace_top B S hS) eqT hsm
  intro T₀ T i hi x₀ y hc
  obtain ⟨x, hx, -⟩ := h i hi x₀ ((repTop (B := B) (S := S) (hS := hS) (M := M) N).equiv T (topPt _)) (by
      refine AttractorPt.ext ?_
      funext T₁ t a
      exact top_eq _ _)
  exact ⟨x, hx, top_ext _ _⟩

/-- **Proposition 16.15 (ii)**, as transformations of functors. `G → S` a smooth group algebraic space,
`D(M)` acting by group morphisms, `α ∈ M`: `G^{[α⟩} → S` and `G^{[α⟩}_{e_S} → S` are formally smooth. The
attractors are not assumed representable. The printed argument is kept: Proposition 11.7 for
`G^{[α⟩} → G^0`, and `G^{[α⟩}_{e_S}` is its fibre over the unit section. -/
theorem prop1615_ii_formal [DecidableEq M]
    (G : GrpFunctor.{u} (BigFppfOver B S hS)) (hG : IsAlgebraicSpace B S hS G.F)
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M)
    (hsm : Space.IsSmooth B S hS (terminal.from G.F)) :
    IsFormallySmooth (terminal.from (attractor act (AddSubmonoid.closure {α}))) ∧
      IsFormallySmooth (terminal.from (rootKernel act ha α).F) := by
  refine ⟨isFormallySmooth_attractor_terminal _ hG act hsm, ?_⟩
  have hF := unitsIsFace (AddSubmonoid.closure {α})
  have hf : IsFormallySmooth (faceMap act hF) := isFormallySmooth_faceMap_of_isSmooth (AddSubmonoid.closure {α}) hF hG act hsm
  let G' := attrGrp G act ha (unitsFace (AddSubmonoid.closure {α}))
  intro T₀ T i hi x₀ y hc
  obtain ⟨x, hx, hxf⟩ := hf i hi x₀.1.1 (1 : G'.F.obj (op T)) (by
    refine (x₀.2 : _).trans ?_
    exact (GrpFunctor.map_one G' i.op).symm)
  refine ⟨⟨(x, PUnit.unit), hxf⟩, ?_, top_ext _ _⟩
  exact Subtype.ext (Prod.ext hx rfl)

section Schemes

open AlgMag.SmoothSchemes

variable {S' : Scheme.{u}} {M' : Type u} [AddCommGroup M']

/-- **Proposition 16.15 (ii)**, `G → S` a smooth group scheme as printed, as transformations of functors:
`G^{[α⟩} → S` and `G^{[α⟩}_{e_S} → S` are formally smooth. The attractors are not assumed representable, and no
site cutoff on `M`. -/
theorem prop1615_ii_formal_scheme [DecidableEq M'] {X : Over S'} [Smooth X.hom]
    {grp : ∀ U : (Over S')ᵒᵖ, Group ((yoneda.obj X).obj U)}
    {map_mul : ∀ {U V : (Over S')ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y}
    (act : AAction (AlgMag.overO S') M' (schemeGrp X grp map_mul).F)
    (ha : ActsByMonoidEnd act) (α : M') :
    FormallySmoothFor (fun {_ _} i => IsAffineThick i)
        (terminal.from (attractor (F := yoneda.obj X) act (AddSubmonoid.closure {α}))) ∧
      FormallySmoothFor (fun {_ _} i => IsAffineThick i)
        (terminal.from (rootKernel act ha α).F) := by
  let act' : AAction (GB.overO S') M' (yoneda.obj X) := act
  constructor
  · let g : X ⟶ Over.mk (𝟙 S') := Over.homMk X.hom (Category.comp_id _)
    have : Smooth g.left := inferInstanceAs (Smooth X.hom)
    have h : FormallySmoothFor (fun {_ _} i => IsAffineThick i)
        (attractorMap (eqHom (aX := act') (aY := trivAction) g (fun _ _ => term_ext _ _))
          (AddSubmonoid.closure {α})) :=
      isFormallySmooth_attractorMap_scheme (AddSubmonoid.closure {α}) g (fun _ _ => term_ext _ _)
    intro T₀ T i hi x₀ y hc
    obtain ⟨x, hx, -⟩ := h i hi x₀ ((repTerminal (S := S') (M := M') _).equiv T
      (Over.homMk T.hom (Category.comp_id _))) (by
        refine AttractorPt.ext ?_
        funext T₁ t a
        exact term_ext _ _)
    exact ⟨x, hx, top_ext _ _⟩
  · have hF := unitsIsFace (AddSubmonoid.closure {α})
    have hf : FormallySmoothFor (fun {_ _} i => IsAffineThick i) (faceMap act' hF) :=
      isFormallySmooth_faceMap_scheme (AddSubmonoid.closure {α}) hF act'
    let G' := attrGrp (schemeGrp X grp map_mul) act ha (unitsFace (AddSubmonoid.closure {α}))
    intro T₀ T i hi x₀ y hc
    obtain ⟨x, hx, hxf⟩ := hf i hi x₀.1.1 (1 : G'.F.obj (op T)) (by
      refine (x₀.2 : _).trans ?_
      exact (GrpFunctor.map_one G' i.op).symm)
    refine ⟨⟨(x, PUnit.unit), hxf⟩, ?_, top_ext _ _⟩
    exact Subtype.ext (Prod.ext hx rfl)

end Schemes

end AlgMag.Leftover

#print axioms AlgMag.Leftover.isFormallySmooth_attractor_terminal
#print axioms AlgMag.Leftover.prop1615_ii_formal
#print axioms AlgMag.Leftover.prop1615_ii_formal_scheme
