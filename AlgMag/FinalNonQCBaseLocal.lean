/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCBase

/-!
# A representable property of a morphism of spaces is local on the base

If the restriction of `f : F ⟶ G` to the site of an object `T₀` has a representable property, then every base change of `f` along
`V ⟶ G`, for `V` over `T₀`, has it on the site of `S` (`exists_rep_over`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- If `f : F → G` has property `P` after restriction to `T₀`, then every map from an object `V` over `T₀` to `G`
is representable by `f` with a pullback `W → V` having `P`. -/
theorem exists_rep_over (T₀ : BigFppfOver B S hS) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    {P : MorphismProperty Scheme.{u}}
    (h : (P.inverseImage (BigFppfOver.toScheme B T₀.left.1 T₀.left.2)).presheaf
      ((relocalizeRestrict T₀.hom).map f))
    {V : BigFppfOver B S hS} (l : V ⟶ T₀) (g : yoneda.obj V ⟶ G) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ V) (q : yoneda.obj W ⟶ F),
      IsPullback q (yoneda.map p) f g ∧ P ((SCH).map p) := by
  let a := T₀.hom
  have hψ : l.left ≫ a = V.hom := Over.w l
  let e := overMapMkIso a hψ
  let V' : BigFppfOver B T₀.left.1 T₀.left.2 := Over.mk l.left
  let g₀ : G.obj (op ((Over.map a).obj V')) := G.map e.inv.op (yonedaEquiv g)
  let g' : yoneda.obj V' ⟶ (relocalizeRestrict a).obj G := yonedaEquiv.symm g₀
  have hpb := h.rep.isPullback g'
  let W' := h.rep.pullback g'
  let p' : W' ⟶ V' := h.rep.snd g'
  let fst' := h.rep.fst g'
  let q₀ : F.obj (op ((Over.map a).obj W')) := fst'.app (op W') (𝟙 W')
  have hyg : ∀ {U : BigFppfOver B S hS} (c : U ⟶ V), g.app (op U) c = G.map c.op (yonedaEquiv g) := by
    intro U c
    have := congrArg (fun k => k (𝟙 V)) (g.naturality c.op)
    simpa [yonedaEquiv] using this
  have hfst : ∀ {U' : BigFppfOver B T₀.left.1 T₀.left.2} (c : U' ⟶ W'),
      fst'.app (op U') c = F.map ((Over.map a).map c).op q₀ := by
    intro U' c
    have := congrArg (fun k => k (𝟙 W')) (fst'.naturality c.op)
    have h2 := this
    simp at h2
    exact h2
  have hg' : ∀ {U' : BigFppfOver B T₀.left.1 T₀.left.2} (c : U' ⟶ V'),
      g'.app (op U') c = G.map ((Over.map a).map c).op g₀ := fun _ => rfl
  have hw : ∀ {U' : BigFppfOver B T₀.left.1 T₀.left.2} (c : U' ⟶ W'),
      f.app (op ((Over.map a).obj U')) (fst'.app (op U') c) = g'.app (op U') (c ≫ p') := fun {U'} c =>
    congrArg (fun k => k.app (op U') c) hpb.w
  let q : yoneda.obj ((Over.map a).obj W') ⟶ F := yonedaEquiv.symm q₀
  let p : (Over.map a).obj W' ⟶ V := (Over.map a).map p' ≫ e.inv
  have hP : P ((SCH).map p) := by
    have hp : (SCH).map p = (BigFppfOver.toScheme B T₀.left.1 T₀.left.2).map p' := by
      have : e.inv.left = 𝟙 _ := rfl
      simp only [p, Functor.map_comp]
      refine (congrArg _ ?_).trans (Category.comp_id _)
      exact rfl
    rw [hp]
    exact h.property_snd g'
  -- a map `U ⟶ (Over.map a).obj W'` over `t` is a map `upObj t ⟶ W'`
  have hmk : ∀ {U : BigFppfOver B S hS} (t : U ⟶ (Over.map a).obj V') (c : U ⟶ (Over.map a).obj W'),
      c ≫ (Over.map a).map p' = t → ∃ d : upObj (T₀ := T₀) t ⟶ W', d ≫ p' = upMap t ∧
        (upIso t).hom ≫ (Over.map a).map d = c := by
    intro U t c hc
    have hl : c.left ≫ p'.left = t.left := congrArg (fun k => k.left) hc
    have hd : c.left ≫ W'.hom = t.left ≫ V'.hom := by
      rw [← hl, Category.assoc]
      exact congrArg (c.left ≫ ·) (Over.w p').symm
    exact ⟨Over.homMk c.left hd, Over.OverMorphism.ext hl, Over.OverMorphism.ext (Category.id_comp _)⟩
  have hqc : ∀ {U : BigFppfOver B S hS} (t : U ⟶ (Over.map a).obj V') (d : upObj (T₀ := T₀) t ⟶ W'),
      F.map (upIso t).hom.op (fst'.app (op (upObj t)) d) =
        q.app (op U) ((upIso t).hom ≫ (Over.map a).map d) := by
    intro U t d
    rw [hfst, ← Functor.map_comp_apply, ← op_comp]
    rfl
  refine ⟨_, p, q, ?_, hP⟩
  refine IsPullback.of_forall_isPullback_app fun U => ?_
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext c
    change f.app U (F.map (Quiver.Hom.op c) q₀) = g.app U (c ≫ p)
    rw [NatTrans.naturality_apply f, hyg]
    have h0 := hw (𝟙 W')
    rw [hfst, Category.id_comp, hg'] at h0
    have h0' : f.app _ q₀ = G.map ((Over.map a).map p').op g₀ := by
      simpa using h0
    rw [h0']
    simp only [g₀, ← Functor.map_comp_apply, ← op_comp, p, Category.assoc]
  · rintro c c' ⟨h1, h2⟩
    have h2' : c ≫ p = c' ≫ p := h2
    let t : unop U ⟶ (Over.map a).obj V' := c ≫ (Over.map a).map p'
    have hc' : c' ≫ (Over.map a).map p' = t := by
      have := congrArg (· ≫ e.hom) h2'
      simpa [p, t] using this.symm
    obtain ⟨d, hd, hdc⟩ := hmk t c rfl
    obtain ⟨d', hd', hdc'⟩ := hmk t c' hc'
    have hq := (hqc t d).trans ((congrArg (q.app (op (unop U))) hdc).trans
      (h1.trans ((congrArg (q.app (op (unop U))) hdc').symm.trans (hqc t d').symm)))
    have hfeq : fst'.app (op (upObj t)) d = fst'.app (op (upObj t)) d' := by
      have hinv := congrArg (F.map (upIso t).inv.op) hq
      simpa [← Functor.map_comp_apply, ← op_comp] using hinv
    have hdd : d = d' := by
      have hU := (Types.isPullback_iff _ _ _ _).1 (hpb.map ((evaluation _ _).obj (op (upObj t))))
      exact hU.2.1 d d' ⟨hfeq, by
        change d ≫ p' = d' ≫ p'
        rw [hd, hd']⟩
    rw [← hdc, ← hdc', hdd]
  · intro x y hxy
    let hh : unop U ⟶ V := y
    let t : unop U ⟶ (Over.map a).obj V' := hh ≫ e.hom
    let x' : F.obj (op ((Over.map a).obj (upObj (T₀ := T₀) t))) := F.map (upIso t).inv.op x
    have hcomp : (upIso t).inv ≫ hh = (Over.map a).map (upMap t) ≫ e.inv := by
      refine Over.OverMorphism.ext ?_
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    have hcond : f.app _ x' = g'.app (op (upObj t)) (upMap t) := by
      rw [hg']
      change f.app _ (F.map _ x) = _
      rw [NatTrans.naturality_apply f, show f.app U x = g.app U y from hxy, hyg (c := hh)]
      simp only [g₀, ← Functor.map_comp_apply, ← op_comp, hcomp]
    have hU := (Types.isPullback_iff _ _ _ _).1 (hpb.map ((evaluation _ _).obj (op (upObj t))))
    obtain ⟨d, hd1, hd2⟩ := hU.2.2 x' (upMap t) hcond
    have hd2' : d ≫ p' = upMap t := hd2
    refine ⟨(upIso t).hom ≫ (Over.map a).map d, ?_, ?_⟩
    · rw [← hqc]
      have hd1' : fst'.app (op (upObj t)) d = x' := hd1
      rw [hd1']
      simp [x', ← Functor.map_comp_apply, ← op_comp]
    · change ((upIso t).hom ≫ (Over.map a).map d) ≫ p = hh
      simp only [p, Category.assoc]
      rw [← Functor.map_comp_assoc, hd2', ← hcomp, Iso.hom_inv_id_assoc]

end AlgMag.Final
