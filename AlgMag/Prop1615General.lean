/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Prop1615Free
import AlgMag.FinalNonQCGeneral
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# Proposition 16.15 (ii), `G` not necessarily quasi-compact, `S` arbitrary

As `prop1615_ii_free`, with Theorem 8.3 in the form `thm83_general` (separated, locally of finite
presentation, no quasi-compactness, `S` arbitrary, no atlas) in place of `thm83_free`. Local finite
presentation of `G` is not assumed: it follows from smoothness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

open AlgMag.GB AlgMag.SpacesLift AlgMag.Sec11Spaces AlgMag.Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [SM B M]

/-- **Proposition 16.15 (ii)**, no representability assumed, `G` not necessarily quasi-compact, `S`
arbitrary. Let `M` be a finitely generated abelian group, `G → S` a smooth group algebraic space,
separated (locally of finite presentation follows from smoothness), with an action of `D(M)` by group morphisms. Then `G^{[α⟩}` is represented by an
algebraic space `Y`, smooth over `S`, and `G^{[α⟩}_{e_S}` is an algebraic space, smooth over `S`. -/
theorem prop1615_ii_general [DecidableEq M] [AddGroup.FG M]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hM : B.Contains (Spec (ZMon M)))
    (G : GrpFunctor.{u} (BigFppfOver B S hS)) (hG : IsAlgebraicSpace B S hS G.F)
    (hsep : Space.IsSeparatedOver B S hS G.F)
    (act : AAction (fppfO B S hS) M G.F) (ha : ActsByMonoidEnd act) (α : M)
    (hsm : Space.IsSmooth B S hS (terminal.from G.F)) :
    (∃ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Nonempty (RepresentsAttractor act (AddSubmonoid.closure {α}) Y) ∧
      IsAlgebraicSpace B S hS Y ∧ Space.IsSmooth B S hS (terminal.from Y)) ∧
    (∃ (K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (eK : ∀ T, K.obj (op T) ≃ (rootKernel act ha α).F.obj (op T)),
      (∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
        eK T' (K.map s.op w) = (rootKernel act ha α).F.map s.op (eK T w)) ∧
      IsAlgebraicSpace B S hS K ∧ Space.IsSmooth B S hS (terminal.from K)) := by
  have hfp := Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm
  obtain ⟨r, -⟩ := thm83_general hZ hM hG hsep hfp act (AddSubmonoid.closure {α})
  obtain ⟨r0, -⟩ := thm83_general hZ hM hG hsep hfp act (unitsFace (AddSubmonoid.closure {α}))
  refine ⟨⟨r.P, ⟨r.rP⟩, r.algP, isSmooth_rep_spaces _ hG r.algP act hsm r.rP⟩, ?_⟩
  let hF := unitsIsFace (AddSubmonoid.closure {α})
  let G' := attrGrp G act ha (unitsFace (AddSubmonoid.closure {α}))
  let σ : ∀ T, AttractorPt act (unitsFace (AddSubmonoid.closure {α})) T :=
    fun T => (1 : G'.F.obj (op T))
  have hσ : ∀ {T T'} (s : T' ⟶ T), (σ T).baseChange s = σ T' :=
    fun {T T'} s => GrpFunctor.map_one G' s.op
  let K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj := fun U => {w : r.P.obj U // AttractorPt.ofFace hF (r.rP.equiv (unop U) w) = σ (unop U)}
      map := fun {U V} s => TypeCat.ofHom fun w => ⟨r.P.map s w.1, by
        rw [show r.P.map s = r.P.map s.unop.op from rfl, r.rP.naturality]
        exact (congrArg (fun x => x.baseChange s.unop) w.2).trans (hσ s.unop)⟩
      map_id := fun U => by
        ext w
        change r.P.map (𝟙 U) w.1 = w.1
        simp
      map_comp := fun f g => by
        ext w
        change r.P.map (f ≫ g) w.1 = r.P.map g (r.P.map f w.1)
        simp }
  let eS : ∀ T, K.obj (op T) ≃ {x : AttractorPt act (AddSubmonoid.closure {α}) T //
      AttractorPt.ofFace hF x = σ T} := fun T => (r.rP.equiv T).subtypeEquiv fun _ => Iff.rfl
  let E : ∀ T, (rootKernel act ha α).F.obj (op T) ≃ {x : AttractorPt act (AddSubmonoid.closure {α}) T //
      AttractorPt.ofFace hF x = σ T} := fun T =>
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨(x.1, PUnit.unit), x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  have nK : ∀ {T T'} (s : T' ⟶ T) (w : K.obj (op T)),
      (eS T' (K.map s.op w)).1 = (eS T w).1.baseChange s := fun s w => r.rP.naturality s w.1
  obtain ⟨hK, hKs⟩ := isAlgebraicSpace_isSmooth_fibre hF hG r.algP r0.algP act hsm r.rP r0.rP σ hσ
    eS nK
  refine ⟨K, fun T => (eS T).trans (E T).symm, fun {T T'} s w => ?_, hK, hKs⟩
  apply (E T').injective
  apply Subtype.ext
  exact nK s w

end AlgMag.Leftover

#print axioms AlgMag.Leftover.prop1615_ii_general
