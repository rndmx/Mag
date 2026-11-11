/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Remaining
import AlgMag.Sec11SchemesRep
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Proposition 16.15 (ii) of *Algebraic Magnetism*

The printed proof: by Corollary 11.10, `G^{[α⟩} → S` and `G^{[α⟩} → G^0` are smooth, and
`G^{[α⟩}_{e_S} = G^{[α⟩} ×_{G^0} e_S`. As Corollary 11.10 is available for schemes, the attractors are
schemes here. Smoothness of `G^{[α⟩} → S` uses Corollary 11.2 (`smooth_repMap`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

open AlgMag.GB AlgMag.SmoothSchemes

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-- Corollary 11.2 for `X → S`: if `X → S` is smooth, so is the scheme representing `X^N`. -/
theorem smooth_rep (N : AddSubmonoid M) {X Zx : Over S} (aX : AAction (GB.overO S) M (yoneda.obj X))
    [Smooth X.hom] (rx : RepresentsAttractor aX N (yoneda.obj Zx)) : Smooth Zx.hom := by
  let g : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (Category.comp_id _)
  have : Smooth g.left := inferInstanceAs (Smooth X.hom)
  have := smooth_repMap N (aY := trivAction) g (fun _ _ => term_ext _ _) rx
    (repTerminal N) (Over.homMk Zx.hom (Category.comp_id _)) (fun T w => by
      refine AttractorPt.ext ?_
      funext T₁ t a
      exact term_ext _ _)
  exact this

/-- The fibre of `X^N → X^F` over a section `σ` of `X^F` is smooth over `S`, if `X → S` is smooth. -/
theorem smooth_fibre {N F : AddSubmonoid M} (hF : IsFace F N) {X Zx Zf K : Over S}
    (aX : AAction (GB.overO S) M (yoneda.obj X)) [Smooth X.hom]
    (rx : RepresentsAttractor aX N (yoneda.obj Zx)) (rf : RepresentsAttractor aX F (yoneda.obj Zf))
    (σ : ∀ T : Over S, AttractorPt aX F T)
    (hσ : ∀ {T T' : Over S} (s : T' ⟶ T), (σ T).baseChange s = σ T')
    (eK : ∀ T : Over S, (T ⟶ K) ≃ {x : AttractorPt aX N T // AttractorPt.ofFace hF x = σ T})
    (hK : ∀ {T T' : Over S} (s : T' ⟶ T) (w : T ⟶ K), (eK T' (s ≫ w)).1 = (eK T w).1.baseChange s) :
    Smooth K.hom := by
  have nx : ∀ {T T' : Over S} (s : T' ⟶ T) (w : T ⟶ Zx),
      rx.equiv T' (s ≫ w) = (rx.equiv T w).baseChange s := fun s w => rx.naturality s w
  have nf : ∀ {T T' : Over S} (s : T' ⟶ T) (w : T ⟶ Zf),
      rf.equiv T' (s ≫ w) = (rf.equiv T w).baseChange s := fun s w => rf.naturality s w
  let z : Zx ⟶ Zf := (rf.equiv Zx).symm (AttractorPt.ofFace hF (rx.equiv Zx (𝟙 Zx)))
  have hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace hF (rx.equiv T w) := by
    intro T w
    rw [nf, Equiv.apply_symm_apply]
    have : rx.equiv T w = (rx.equiv Zx (𝟙 Zx)).baseChange w := by
      rw [← nx, Category.comp_id]
    rw [this]
    rfl
  have hzs : Smooth z.left := smooth_repFace N aX hF rx rf z hz
  let Sobj : Over S := Over.mk (𝟙 S)
  let u : Sobj ⟶ Zf := (rf.equiv Sobj).symm (σ Sobj)
  have hu : ∀ {T : Over S} (τ : T ⟶ Sobj), rf.equiv T (τ ≫ u) = σ T := by
    intro T τ
    rw [nf, Equiv.apply_symm_apply, hσ]
  let toS : ∀ T : Over S, T ⟶ Sobj := fun T => Over.homMk T.hom (Category.comp_id _)
  have hτ : ∀ {T : Over S} (a b : T ⟶ Sobj), a = b := by
    intro T a b
    refine Over.OverMorphism.ext ?_
    have ha := Over.w a
    have hb := Over.w b
    simp only [Sobj, Over.mk_hom, Category.comp_id] at ha hb
    exact ha.trans hb.symm
  let j : K ⟶ Zx := (rx.equiv K).symm (eK K (𝟙 K)).1
  have hj : ∀ {T : Over S} (w : T ⟶ K), rx.equiv T (w ≫ j) = (eK T w).1 := by
    intro T w
    rw [nx, Equiv.apply_symm_apply, ← hK, Category.comp_id]
  have hcomm : j ≫ z = toS K ≫ u := by
    apply (rf.equiv K).injective
    rw [hz, hu, Equiv.apply_symm_apply]
    exact (eK K (𝟙 K)).2
  have hpb : IsPullback j (toS K) z u := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk j (toS K) hcomm) ?_
    refine PullbackCone.IsLimit.mk hcomm
      (fun s => (eK s.pt).symm ⟨rx.equiv s.pt s.fst, ?_⟩) ?_ ?_ ?_
    · rw [← hz, s.condition, hu]
    · intro s
      apply (rx.equiv s.pt).injective
      rw [hj, Equiv.apply_symm_apply]
    · intro s
      exact hτ _ _
    · intro s m h1 h2
      apply (eK s.pt).injective
      rw [Equiv.apply_symm_apply]
      refine Subtype.ext ?_
      change _ = rx.equiv s.pt s.fst
      rw [← h1, hj]
  have hpb' : IsPullback j.left (toS K).left z.left u.left := hpb.map (Over.forget S)
  exact MorphismProperty.of_isPullback (P := @Smooth) hpb' hzs

/-- **Proposition 16.15 (ii).** Let `G → S` be a smooth group scheme, with `G^{[α⟩}`, `G^{[α⟩^×}` and
`G^{[α⟩}_{e_S}` represented by schemes `Y`, `Y0`, `K`. Then `Y` and `K` are smooth over `S`. -/
theorem prop1615_ii {X Y Y0 K : Over S} [Smooth X.hom]
    {grp : ∀ U : (Over S)ᵒᵖ, Group ((yoneda.obj X).obj U)}
    {map_mul : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y}
    (act : AAction (AlgMag.overO S) M (schemeGrp X grp map_mul).F)
    (ha : ActsByMonoidEnd act) (α : M)
    (rY : RepresentsAttractor (F := yoneda.obj X) act (AddSubmonoid.closure {α}) (yoneda.obj Y))
    (rY0 : RepresentsAttractor (F := yoneda.obj X) act (unitsFace (AddSubmonoid.closure {α}))
      (yoneda.obj Y0))
    (eK : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T))
    (hK : ∀ {T T' : Over S} (s : T' ⟶ T) (w : T ⟶ K),
      eK T' (s ≫ w) = (rootKernel act ha α).F.map s.op (eK T w)) :
    Smooth Y.hom ∧ Smooth K.hom := by
  let act' : AAction (GB.overO S) M (yoneda.obj X) := act
  refine ⟨smooth_rep _ act' rY, ?_⟩
  let G' := attrGrp (schemeGrp X grp map_mul) act ha (unitsFace (AddSubmonoid.closure {α}))
  refine smooth_fibre (unitsIsFace (AddSubmonoid.closure {α})) act' rY rY0
    (fun T => (1 : G'.F.obj (op T))) (fun {T T'} s => GrpFunctor.map_one G' s.op)
    (fun T => (eK T).trans
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun x => ⟨(x.1, PUnit.unit), x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }) ?_
  intro T T' s w
  have := congrArg (fun x => x.1.1) (hK s w)
  exact this

end AlgMag.Leftover

#print axioms AlgMag.Leftover.prop1615_ii
