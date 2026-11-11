/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SchemesFace
import AlgMag.Sec11SchemesLimit
import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Smoothness of `X^N → Y^N` when the attractors are schemes

Mayeux, *Algebraic Magnetism*, Corollaries 11.2, 11.6, 11.10, Proposition 12.2(i), schemes only.
Representability of `X^N` and `Y^N` by schemes is a hypothesis, as in the paper.
-/

open CategoryTheory Opposite AlgebraicGeometry

universe u w

namespace AlgMag.SmoothSchemes

open AlgMag.GB AlgMag.Lifts

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

lemma isAffineThick_of_thickening {T T₁ : Over S} (i : T ⟶ T₁) (hT : IsAffine T.left)
    (hT₁ : IsAffine T₁.left)
    (hi : Stacks.Thickenings.IsFirstOrderThickening i.left) : IsAffineThick i := by
  have := hi.1
  refine ⟨hT, hT₁, (IsClosedImmersion.isAffine_surjective_of_isAffine i.left).2, ?_⟩
  have h2 := (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine i.left 2).1 hi.2
  intro x y hx hy
  have : x * y ∈ RingHom.ker i.left.appTop.hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  rw [h2] at this
  exact this

/-- Formal smoothness of a transformation between represented functors gives formal smoothness of
the morphism of schemes. -/
theorem formallySmoothScheme_of_rep {Zx Zy : Over S}
    {FX FY : (Over S)ᵒᵖ ⥤ Type w} (m : FX ⟶ FY)
    (hm : FormallySmoothFor (fun {_ _} i => IsAffineThick i) m)
    (rx : ∀ T : Over S, (T ⟶ Zx) ≃ FX.obj (op T)) (ry : ∀ T : Over S, (T ⟶ Zy) ≃ FY.obj (op T))
    (nx : ∀ {T T₁ : Over S} (s : T₁ ⟶ T) (w : T ⟶ Zx), rx T₁ (s ≫ w) = FX.map s.op (rx T w))
    (ny : ∀ {T T₁ : Over S} (s : T₁ ⟶ T) (w : T ⟶ Zy), ry T₁ (s ≫ w) = FY.map s.op (ry T w))
    (z : Zx ⟶ Zy) (hz : ∀ (T : Over S) (w : T ⟶ Zx), ry T (w ≫ z) = m.app _ (rx T w)) :
    Stacks.Smooth.FormallySmoothScheme z.left := by
  intro T T₁ hT hT₁ i hi a₀ h w
  let T₁o : Over S := Over.mk (h ≫ Zy.hom)
  let To : Over S := Over.mk (i ≫ h ≫ Zy.hom)
  let io : To ⟶ T₁o := Over.homMk i rfl
  have hth : IsAffineThick io := isAffineThick_of_thickening io hT hT₁ hi
  let a₀' : To ⟶ Zx := Over.homMk a₀ (by
    change a₀ ≫ Zx.hom = i ≫ h ≫ Zy.hom
    rw [← Over.w z, ← Category.assoc, w, Category.assoc])
  let h' : T₁o ⟶ Zy := Over.homMk h rfl
  have hc : m.app _ (rx To a₀') = FY.map io.op (ry T₁o h') := by
    rw [← hz, ← ny]
    exact congrArg _ (Over.OverMorphism.ext w)
  obtain ⟨x, hx₁, hx₂⟩ := hm io hth (rx To a₀') (ry T₁o h') hc
  let l := (rx T₁o).symm x
  have hl : rx T₁o l = x := Equiv.apply_symm_apply _ _
  have e₁ : l ≫ z = h' := by
    refine (ry T₁o).injective ?_
    rw [hz, hl, hx₂]
  have e₂ : io ≫ l = a₀' := by
    refine (rx To).injective ?_
    rw [nx, hl, hx₁]
  exact ⟨l.left, congrArg (fun k => k.left) e₁, congrArg (fun k => k.left) e₂⟩

section Rep

variable {X Y Zx Zy : Over S} {aX : AAction (overO S) M (yoneda.obj X)}
  {aY : AAction (overO S) M (yoneda.obj Y)} (g : X ⟶ Y)
  (hg : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ X), sm aX h x ≫ g = sm aY h (x ≫ g))
  (rx : RepresentsAttractor aX N (yoneda.obj Zx)) (ry : RepresentsAttractor aY N (yoneda.obj Zy))
  (z : Zx ⟶ Zy) (hz : ∀ (T : Over S) (w : T ⟶ Zx),
    ry.equiv T (w ≫ z) = AttractorPt.push (eqHom g hg) (rx.equiv T w))

include hz in
/-- **Corollary 11.2**, schemes only: if `g : X → Y` is smooth and `X^N`, `Y^N` are representable by
schemes, then `X^N → Y^N` is smooth. -/
theorem smooth_repMap [Smooth g.left] : Smooth z.left :=
  (Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth z.left).2
    ⟨locallyOfFinitePresentation_repMap N g hg rx ry z hz,
      formallySmoothScheme_of_rep (attractorMap (eqHom g hg) N)
        (isFormallySmooth_attractorMap_scheme N g hg) rx.equiv ry.equiv
        (fun s w => rx.naturality s w) (fun s w => ry.naturality s w) z hz⟩

include hz in
/-- **Corollary 11.6**, schemes only: if `g` is étale and `X^N`, `Y^N` are representable by schemes,
then `X^N → Y^N` is étale. -/
theorem etale_repMap [Etale g.left] : Etale z.left := by
  have := smooth_repMap N g hg rx ry z hz
  have : FormallyUnramified z.left := FormallyUnramified.of_hom_ext z.left
    fun R R₀ φ hs hq g₁ g₂ h₁ h₂ => by
      let T₁ : Over S := Over.mk (g₁ ≫ Zx.hom)
      let T₀ : Over S := Over.mk (Spec.map φ ≫ g₁ ≫ Zx.hom)
      let io : T₀ ⟶ T₁ := Over.homMk (Spec.map φ) rfl
      have hg₂ : g₂ ≫ Zx.hom = g₁ ≫ Zx.hom := by
        rw [← Over.w z, ← Category.assoc, ← Category.assoc, h₂]
      let u₁ : T₁ ⟶ Zx := Over.homMk g₁ rfl
      let u₂ : T₁ ⟶ Zx := Over.homMk g₂ hg₂
      have hth : IsAffineThick io := isAffineThick_of_thickening io (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _)))
        (Stacks.Smooth.isFirstOrderThickening_specMap φ hs hq)
      have := isFormallyUnramified_attractorMap_scheme N g hg io hth (rx.equiv T₁ u₁) (rx.equiv T₁ u₂)
        (by
          refine (rx.naturality io u₁).symm.trans (Eq.trans (congrArg _ ?_) (rx.naturality io u₂))
          exact Over.OverMorphism.ext h₁)
        (by
          refine (hz T₁ u₁).symm.trans (Eq.trans (congrArg _ ?_) (hz T₁ u₂))
          exact Over.OverMorphism.ext h₂)
      exact congrArg (fun k => k.left) ((rx.equiv T₁).injective this)
  exact Etale.of_formallyUnramified_of_flat z.left

include hz in
/-- **Proposition 12.2(i)**, schemes only: if `g` is an open immersion and `X^N`, `Y^N` are
representable by schemes, then `X^N → Y^N` is an open immersion. -/
theorem isOpenImmersion_repMap [IsOpenImmersion g.left] : IsOpenImmersion z.left := by
  have := smooth_repMap N g hg rx ry z hz
  have : Mono z.left := by
    refine ⟨fun {W} u v h => ?_⟩
    let T : Over S := Over.mk (u ≫ Zx.hom)
    have hv : v ≫ Zx.hom = u ≫ Zx.hom := by
      rw [← Over.w z, ← Category.assoc, ← Category.assoc, h]
    let u₁ : T ⟶ Zx := Over.homMk u rfl
    let u₂ : T ⟶ Zx := Over.homMk v hv
    have hinj : u₁ = u₂ := by
      refine (rx.equiv T).injective ?_
      refine AttractorPt.ext ?_
      funext T₁ t a
      have e0 : u₁ ≫ z = u₂ ≫ z := Over.OverMorphism.ext h
      have e := congrArg (fun χ : AttractorPt aY N T => χ.app t a)
        ((hz T u₁).symm.trans (Eq.trans (congrArg _ e0) (hz T u₂)))
      have hmono : Mono g.left := inferInstance
      refine Over.OverMorphism.ext ((cancel_mono g.left).1 ?_)
      exact congrArg (fun k => k.left) e
    exact congrArg (fun k => k.left) hinj
  exact IsOpenImmersion.of_flat_of_mono z.left

end Rep

/-- The attractor of `S` with trivial action is `S`. -/
noncomputable def repTerminal : RepresentsAttractor (trivAction (S := S) (M := M)) N
    (yoneda.obj (Over.mk (𝟙 S))) where
  equiv T :=
    { toFun := fun w =>
        { app := fun {T₁} t _ => t ≫ w
          naturality := fun s t a => term_ext _ _
          equivariant := fun t h a => term_ext _ _ }
      invFun := fun _ => Over.homMk T.hom (Category.comp_id _)
      left_inv := fun w => term_ext _ _
      right_inv := fun φ => by
        refine AttractorPt.ext ?_
        funext T₁ t a
        exact term_ext _ _ }
  naturality s w := by
    refine AttractorPt.ext ?_
    funext T₁ t a
    exact term_ext _ _

/-- If `X → S` is locally of finite presentation, so is the scheme representing `X^N`. Fact 3.19
for `X → S`, schemes only. -/
theorem locallyOfFinitePresentation_rep {X Zx : Over S} (aX : AAction (overO S) M (yoneda.obj X))
    [LocallyOfFinitePresentation X.hom] (rx : RepresentsAttractor aX N (yoneda.obj Zx)) :
    LocallyOfFinitePresentation Zx.hom := by
  let g : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (Category.comp_id _)
  have : LocallyOfFinitePresentation g.left := inferInstanceAs (LocallyOfFinitePresentation X.hom)
  have := locallyOfFinitePresentation_repMap N (aY := trivAction) g (fun _ _ => term_ext _ _) rx
    (repTerminal N) (Over.homMk Zx.hom (Category.comp_id _)) (fun T w => by
      refine AttractorPt.ext ?_
      funext T₁ t a
      exact term_ext _ _)
  exact this

/-- **Corollary 11.10**, schemes only: if `X → S` is smooth, `F` a face of `N`, and `X^N`, `X^F` are
representable by schemes, then `X^N → X^F` is smooth. -/
theorem smooth_repFace {X Zx Zf : Over S} (aX : AAction (overO S) M (yoneda.obj X))
    {F : AddSubmonoid M} (hF : IsFace F N) [Smooth X.hom]
    (rx : RepresentsAttractor aX N (yoneda.obj Zx)) (rf : RepresentsAttractor aX F (yoneda.obj Zf))
    (z : Zx ⟶ Zf) (hz : ∀ (T : Over S) (w : T ⟶ Zx),
      rf.equiv T (w ≫ z) = AttractorPt.ofFace hF (rx.equiv T w)) : Smooth z.left := by
  have h₁ := locallyOfFinitePresentation_rep N aX rx
  have h₂ := locallyOfFinitePresentation_rep F aX rf
  have h₃ : LocallyOfFinitePresentation (z.left ≫ Zf.hom) := by
    rw [Over.w z]
    exact h₁
  have h₄ : LocallyOfFinitePresentation z.left :=
    locallyOfFinitePresentation_of_comp z.left Zf.hom
  exact (Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth z.left).2
    ⟨h₄, formallySmoothScheme_of_rep (faceMap aX hF) (isFormallySmooth_faceMap_scheme N hF aX)
      rx.equiv rf.equiv (fun s w => rx.naturality s w) (fun s w => rf.naturality s w) z hz⟩

end AlgMag.SmoothSchemes
