/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitFinal
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.FppfMayerVietoris

/-!
# Viewing an action over `Spec ℤ` and coming back

Mayeux, *Algebraic Magnetism*, proofs of Theorems A.1 and A.2: reduction of a general base `S` to
the site of `Spec ℤ`. A presheaf `X` on the site of `S` is viewed on the site of `Spec ℤ` along the
lower-shriek extension; a section over `T` is a pair `(ψ : T ⟶ S, s ∈ X(T, ψ))`. Sections of the
structure sheaf over `T` do not depend on `ψ`, so an action of `D(M)` on `X` is an action on the
view, `h • (ψ, s) = (ψ, h • s)`, which preserves `ψ`.

* `viewAct`, `viewMap_equivariant`: the action on the view.
* `chartObj`, `chartAct`, `chartMap`, `exists_chart_of_view`: an equivariant chart of the view is
  the extension of an equivariant chart of `X`, and étale, surjective, FPR come back.
* `isFinitePresentation_viewMap`, `view_isAlgebraicSpace`, `viewMap_invariant`.
* `closed_of_view`, `isFinitePresentation_of_view`: the fixed points come back.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimView

open Space

noncomputable section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The structure morphism of `S` over `Spec ℤ`. -/
abbrev toZ (hS : B.Contains S) : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩

/-- The site of `Spec ℤ`. -/
abbrev ZSite := BigFppfOver B (⊤_ Scheme.{u}) hZ

/-- The view of a presheaf. -/
abbrev view (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : (ZSite (B := B) hZ)ᵒᵖ ⥤ Type u :=
  viewOverIntegers B S hS hZ F

variable {hZ}

lemma comp_toZ {W : ZSite (B := B) hZ} (ψ : W.left ⟶ B.obj hS) : ψ ≫ toZ hZ hS = W.hom :=
  ObjectProperty.hom_ext _ (terminal.hom_ext _ _)

/-- A morphism of the site of `Spec ℤ` is its underlying morphism. -/
def zhom {W V : ZSite (B := B) hZ} (l : W.left ⟶ V.left) : W ⟶ V :=
  Over.homMk l (ObjectProperty.hom_ext _ (terminal.hom_ext _ _))

@[simp] lemma zhom_left {W V : ZSite (B := B) hZ} (l : W.left ⟶ V.left) :
    (zhom l : W ⟶ V).left = l := rfl

lemma zhom_of_left {W V : ZSite (B := B) hZ} (g : W ⟶ V) : zhom g.left = g :=
  Over.OverMorphism.ext rfl

variable {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {M : Type*} [AddCommMonoid M]

/-- A section of the view from `(ψ, s)`. -/
def sec (W : ZSite (B := B) hZ) (ψ : W.left ⟶ B.obj hS) (s : X.obj (op (Over.mk ψ))) :
    (view hZ X).obj (op W) :=
  ⟨⟨ψ, s⟩, comp_toZ ψ⟩

lemma sec_inj {W : ZSite (B := B) hZ} {ψ : W.left ⟶ B.obj hS} {s s' : X.obj (op (Over.mk ψ))}
    (h : sec W ψ s = sec W ψ s') : s = s' := by
  exact OverShriek.sigma_snd_inj (congrArg Subtype.val h)

/-- A point of `D(M)` over `W`, read over `(W, ψ)`. -/
abbrev ptS {W : ZSite (B := B) hZ} (ψ : W.left ⟶ B.obj hS)
    (a : APt (fppfO B (⊤_ Scheme.{u}) hZ) M (op W)) :
    APt (fppfO B S hS) M (op (Over.mk ψ)) := a

/-- **The action on the view**: `h • (ψ, s) = (ψ, h • s)`. -/
def viewAct (act : AAction (fppfO B S hS) M X) :
    AAction (fppfO B (⊤_ Scheme.{u}) hZ) M (view hZ X) where
  smul {U} a p := ⟨⟨p.1.1, act.smul (ptS (W := U.unop) p.1.1 a) p.1.2⟩, p.2⟩
  one_smul p := Subtype.ext (congrArg (Sigma.mk p.1.1) (act.one_smul p.1.2))
  mul_smul g h p := Subtype.ext (congrArg (Sigma.mk p.1.1) (act.mul_smul _ _ p.1.2))
  map_smul {U V} f a p := by
    let r : Over.mk (f.unop.left ≫ p.1.1) ⟶ Over.mk p.1.1 := Over.homMk f.unop.left rfl
    exact Subtype.ext (congrArg (Sigma.mk _) (act.map_smul r.op (ptS (W := U.unop) p.1.1 a) p.1.2))

@[simp] lemma viewAct_sec (act : AAction (fppfO B S hS) M X) {W : ZSite (B := B) hZ}
    (ψ : W.left ⟶ B.obj hS) (a : APt (fppfO B (⊤_ Scheme.{u}) hZ) M (op W))
    (s : X.obj (op (Over.mk ψ))) :
    (viewAct act).smul a (sec W ψ s) = sec W ψ (act.smul (ptS ψ a) s) := rfl

/-- The view of an equivariant morphism is equivariant. -/
theorem viewMap_equivariant {act : AAction (fppfO B S hS) M X}
    {act' : AAction (fppfO B S hS) M X'} {f : X ⟶ X'} (hf : IsEquivariant act act' f) :
    IsEquivariant (viewAct (hZ := hZ) act) (viewAct act')
      ((OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map f) := by
  intro U a p
  exact Subtype.ext (congrArg (Sigma.mk p.1.1) (hf (ptS (W := U.unop) p.1.1 a) p.1.2))

variable {act : AAction (fppfO B S hS) M X}

/-- Restriction of a section of the view along a morphism of the `S`-site. -/
lemma map_sec {W W' : ZSite (B := B) hZ} {ψ : W.left ⟶ B.obj hS} {ψ' : W'.left ⟶ B.obj hS}
    (b : (Over.mk ψ' : BigFppfOver B S hS) ⟶ Over.mk ψ) (s : X.obj (op (Over.mk ψ))) :
    (view hZ X).map (zhom (W := W') (V := W) b.left).op (sec W ψ s) =
      sec W' ψ' (X.map b.op s) :=
  Subtype.ext (OverShriek.presheaf_map_sigmaMk (G := X) b s)

/-- A section `(ψ, s)` of the view is fixed if `s` is. -/
theorem sec_mem_fixed {W : ZSite (B := B) hZ} {ψ : W.left ⟶ B.obj hS}
    {s : X.obj (op (Over.mk ψ))} (hs : s ∈ (fixedPoints act).obj (op (Over.mk ψ))) :
    sec W ψ s ∈ (fixedPoints (viewAct act)).obj (op W) := by
  intro W' f a
  let r : Over.mk (f.unop.left ≫ ψ) ⟶ Over.mk ψ := Over.homMk f.unop.left rfl
  exact Subtype.ext (congrArg (Sigma.mk _) (hs r.op (ptS (W := W'.unop) _ a)))

/-- The site object `T` of the `S`-site, viewed on the site of `Spec ℤ`. -/
abbrev jo (T : BigFppfOver B S hS) : ZSite (B := B) hZ := (Over.map (toZ hZ hS)).obj T

/-- A point of `D(M)` over `T`, read over the view of `T`. -/
abbrev ptZ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) M (op T)) :
    APt (fppfO B (⊤_ Scheme.{u}) hZ) M (op (jo (hZ := hZ) T)) := a

/-- A section `(ψ, s)` of the view is fixed only if `s` is. -/
theorem mem_fixed_of_sec {W : ZSite (B := B) hZ} {ψ : W.left ⟶ B.obj hS}
    {s : X.obj (op (Over.mk ψ))} (h : sec W ψ s ∈ (fixedPoints (viewAct act)).obj (op W)) :
    s ∈ (fixedPoints act).obj (op (Over.mk ψ)) := by
  rintro ⟨T⟩ r a
  have e := map_sec (W := W) (W' := jo (hZ := hZ) T) (ψ := ψ) (ψ' := T.hom) r.unop s
  have h1 := h (zhom (W := jo (hZ := hZ) T) (V := W) r.unop.left).op (ptZ a)
  rw [e] at h1
  exact sec_inj h1

section Chart

variable {V' : ZSite (B := B) hZ} (v' : yoneda.obj V' ⟶ view hZ X)

/-- The morphism to `S` carried by the chart of the view. -/
def chartψ : V'.left ⟶ B.obj hS := (v'.app (op V') (𝟙 V')).1.1

/-- The underlying object of the chart, with its morphism to `S`: the same scheme as `V'`. -/
def chartObj : BigFppfOver B S hS := Over.mk (chartψ v')

/-- The section of `X` carried by the chart of the view. -/
def chartSec : X.obj (op (chartObj v')) := (v'.app (op V') (𝟙 V')).1.2

/-- The morphism to `X` underlying the chart of the view. -/
def chartMap : yoneda.obj (chartObj v') ⟶ X := yonedaEquiv.symm (chartSec v')

/-- The schemes underlying the chart and its view are the same. -/
lemma chartObj_scheme :
    (BigFppfOver.toScheme B S hS).obj (chartObj v') =
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V' := rfl

lemma app_eq_map {W : ZSite (B := B) hZ} (g : W ⟶ V') :
    v'.app (op W) g = (view hZ X).map g.op (v'.app (op V') (𝟙 V')) := by
  rw [← NatTrans.naturality_apply]
  exact congrArg (v'.app (op W)) (Category.comp_id g).symm

lemma app_fst {W : ZSite (B := B) hZ} (g : W ⟶ V') :
    (v'.app (op W) g).1.1 = g.left ≫ chartψ v' := by
  rw [app_eq_map]; rfl

/-- The value of the chart of the view on a point from `(W, ψ')`. -/
lemma eval {W : ZSite (B := B) hZ} {ψ' : W.left ⟶ B.obj hS}
    (t : (Over.mk ψ' : BigFppfOver B S hS) ⟶ chartObj v') :
    v'.app (op W) (zhom (W := W) (V := V') t.left) =
      sec W ψ' ((chartMap v').app (op (Over.mk ψ')) t) := by
  rw [app_eq_map]
  exact map_sec (W := V') (ψ := chartψ v') t (chartSec v')

/-- `eval` at a point `t : T ⟶ V` of the `S`-site. -/
lemma eval' {T : BigFppfOver B S hS} (t : T ⟶ chartObj v') :
    v'.app (op (jo (hZ := hZ) T)) (zhom (W := jo (hZ := hZ) T) (V := V') t.left) =
      sec (jo (hZ := hZ) T) T.hom ((chartMap v').app (op T) t) :=
  eval (W := jo (hZ := hZ) T) (ψ' := T.hom) v' t

variable {v'} {actV' : AAction (fppfO B (⊤_ Scheme.{u}) hZ) M (yoneda.obj V')}

lemma chart_w (hv' : IsEquivariant actV' (viewAct act) v') {T : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) M (op T)) (t : T ⟶ chartObj v') :
    (actV'.smul (ptZ (hZ := hZ) a) (zhom (W := jo (hZ := hZ) T) (V := V') t.left) :
        jo (hZ := hZ) T ⟶ V').left ≫ chartψ v' = T.hom := by
  have h1 := app_fst v' (actV'.smul (ptZ (hZ := hZ) a)
    (zhom (W := jo (hZ := hZ) T) (V := V') t.left) : jo (hZ := hZ) T ⟶ V')
  rw [hv' (T := op (jo (hZ := hZ) T)) (ptZ (hZ := hZ) a) (zhom t.left)] at h1
  have h2 := app_fst v' (zhom (W := jo (hZ := hZ) T) (V := V') t.left)
  exact h1.symm.trans (h2.trans (Over.w t))

/-- The action on the chart: on underlying morphisms it is the action on `V'`. -/
def chartAct (actV' : AAction (fppfO B (⊤_ Scheme.{u}) hZ) M (yoneda.obj V'))
    (hv' : IsEquivariant actV' (viewAct act) v') :
    AAction (fppfO B S hS) M (yoneda.obj (chartObj v')) where
  smul {T} a t := Over.homMk (actV'.smul (ptZ (hZ := hZ) (T := T.unop) a)
    (zhom (W := jo (hZ := hZ) T.unop) (V := V') (show T.unop ⟶ chartObj v' from t).left) :
      jo (hZ := hZ) T.unop ⟶ V').left (chart_w hv' a t)
  one_smul {T} t := Over.OverMorphism.ext (by
    have := actV'.one_smul (U := op (jo (hZ := hZ) T.unop))
      (zhom (W := jo (hZ := hZ) T.unop) (V := V') (show T.unop ⟶ chartObj v' from t).left)
    exact congrArg (fun x : jo (hZ := hZ) T.unop ⟶ V' => x.left) this)
  mul_smul {T} g h t := Over.OverMorphism.ext (by
    have := actV'.mul_smul (U := op (jo (hZ := hZ) T.unop)) (ptZ (hZ := hZ) (T := T.unop) g)
      (ptZ (hZ := hZ) (T := T.unop) h)
      (zhom (W := jo (hZ := hZ) T.unop) (V := V') (show T.unop ⟶ chartObj v' from t).left)
    exact congrArg (fun x : jo (hZ := hZ) T.unop ⟶ V' => x.left)
      (this.trans (congrArg (actV'.smul _) (zhom_of_left _).symm)))
  map_smul {T T'} f a t := Over.OverMorphism.ext (by
    have := actV'.map_smul (zhom (W := jo (hZ := hZ) T'.unop) (V := jo (hZ := hZ) T.unop)
        f.unop.left).op (ptZ (hZ := hZ) (T := T.unop) a)
      (zhom (W := jo (hZ := hZ) T.unop) (V := V') (show T.unop ⟶ chartObj v' from t).left)
    exact congrArg (fun x : jo (hZ := hZ) T'.unop ⟶ V' => x.left) this)

lemma chartAct_left (hv' : IsEquivariant actV' (viewAct act) v') {T : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) M (op T)) (t : T ⟶ chartObj v') :
    ((chartAct actV' hv').smul a t : T ⟶ chartObj v').left =
      (actV'.smul (ptZ (hZ := hZ) a) (zhom (W := jo (hZ := hZ) T) (V := V') t.left) :
        jo (hZ := hZ) T ⟶ V').left := rfl

/-- The morphism underlying the chart is equivariant. -/
theorem chartMap_equivariant (hv' : IsEquivariant actV' (viewAct act) v') :
    IsEquivariant (chartAct actV' hv') act (chartMap v') := by
  rintro ⟨T⟩ a (t : T ⟶ chartObj v')
  refine sec_inj (W := jo (hZ := hZ) T) (ψ := T.hom) ?_
  have h1 := eval' (hZ := hZ) v' ((chartAct actV' hv').smul a t : T ⟶ chartObj v')
  have h2 := eval' (hZ := hZ) v' t
  refine h1.symm.trans ?_
  have h3 : zhom (W := jo (hZ := hZ) T) (V := V')
      ((chartAct actV' hv').smul a t : T ⟶ chartObj v').left =
      actV'.smul (ptZ (hZ := hZ) a) (zhom (W := jo (hZ := hZ) T) (V := V') t.left) :=
    zhom_of_left _
  rw [h3, hv' (T := op (jo (hZ := hZ) T)) (ptZ (hZ := hZ) a) (zhom t.left), h2]
  rfl

/-- **FPR comes back**, for any monoid acting: the actions are compared on underlying morphisms. -/
theorem isFPR_of_view {P : Type*} [AddCommMonoid P] {actP : AAction (fppfO B S hS) P X}
    {actV : AAction (fppfO B S hS) P (yoneda.obj (chartObj v'))}
    {actW : AAction (fppfO B (⊤_ Scheme.{u}) hZ) P (yoneda.obj V')}
    (hleft : ∀ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) P (op T)) (t : T ⟶ chartObj v'),
      (actV.smul a t : T ⟶ chartObj v').left =
        (actW.smul (ptZ (hZ := hZ) a) (zhom (W := jo (hZ := hZ) T) (V := V') t.left) :
          jo (hZ := hZ) T ⟶ V').left)
    {hv : IsEquivariant actV actP (chartMap v')} {hw : IsEquivariant actW (viewAct actP) v'}
    (H : IsFPR hw) : IsFPR hv := by
  refine (isFPR_iff hv).mpr ?_
  rintro ⟨T⟩ (t : T ⟶ chartObj v') hx
  have hz : zhom (W := jo (hZ := hZ) T) (V := V') t.left ∈
      (fixedPoints actW).obj (op (jo (hZ := hZ) T)) := by
    refine (isFPR_iff hw).mp H _ _ ?_
    rw [eval' (hZ := hZ) v' t]
    exact sec_mem_fixed hx
  rintro ⟨T'⟩ s a
  refine Over.OverMorphism.ext ?_
  have h1 := hz (zhom (W := jo (hZ := hZ) T') (V := jo (hZ := hZ) T) s.unop.left).op
    (ptZ (hZ := hZ) a)
  exact (hleft a (s.unop ≫ t)).trans
    (congrArg (fun x : jo (hZ := hZ) T' ⟶ V' => x.left) h1)

/-- The comparison between the view of the chart and `V'`. -/
def chartIso (v' : yoneda.obj V' ⟶ view hZ X) :
    (Over.map (toZ hZ hS)).obj (chartObj v') ≅ V' :=
  Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (terminal.hom_ext _ _))

/-- **The extension of the chart is `v'`**, through `Λ h_V ≅ h_{jV} ≅ h_{V'}`. -/
theorem map_chartMap (v' : yoneda.obj V' ⟶ view hZ X) :
    (OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map (chartMap v') =
      ((OverShriek.relocalizeYonedaIso (toZ hZ hS)).app (chartObj v')).hom ≫
        yoneda.map (chartIso v').hom ≫ v' := by
  ext ⟨W⟩ ⟨⟨ψ', t⟩, hp⟩
  have e := eval (W := W) (ψ' := ψ') v' t
  refine e.symm.trans (congrArg (v'.app (op W)) ?_)
  exact Over.OverMorphism.ext (by
    change t.left = t.left ≫ 𝟙 _
    rw [Category.comp_id])

variable {Q : MorphismProperty Scheme.{u}} [MorphismProperty.RespectsIso Q]

/-- Tested properties come back from the view of a chart: étale, surjective. -/
theorem chartMap_presheaf (v' : yoneda.obj V' ⟶ view hZ X)
    (h : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf v') :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf (chartMap v') := by
  refine presheaf_relocalizeMap_of B S _ hS hZ (toZ hZ hS) Q _ ?_
  rw [map_chartMap, ← Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ v').2 h

/-- Étale comes back from the view of a chart. -/
theorem chartMap_etale (v' : yoneda.obj V' ⟶ view hZ X)
    (h : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf v') :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (chartMap v') :=
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  chartMap_presheaf v' h

/-- Surjective comes back from the view of a chart. -/
theorem chartMap_surjective (v' : yoneda.obj V' ⟶ view hZ X)
    (h : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf v') :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (chartMap v') :=
  have _ : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  chartMap_presheaf v' h

/-- The chart is `S`-affine when `S` and `V'` are affine. -/
theorem chart_isAffineHom [IsAffine S] (v' : yoneda.obj V' ⟶ view hZ X)
    [hV : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V')] :
    IsAffineHom (structMap (chartObj v')) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartObj v')) := hV
  infer_instance

end Chart

section Group

variable {G : Type*} [AddCommGroup G] {act : AAction (fppfO B S hS) G X}
  {V' : ZSite (B := B) hZ} {v' : yoneda.obj V' ⟶ view hZ X}
  {actV' : AAction (fppfO B (⊤_ Scheme.{u}) hZ) G (yoneda.obj V')}

/-- A stable open of `V'` is a stable open of the chart. -/
theorem chart_isStableOpen (hv' : IsEquivariant actV' (viewAct act) v')
    {O : ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V').Opens}
    (hO : IsStableOpen actV' O) :
    IsStableOpen (chartAct actV' hv') (show ((BigFppfOver.toScheme B S hS).obj
      (chartObj v')).Opens from O) := by
  intro T t a ht
  exact hO (T := jo (hZ := hZ) T) (zhom (W := jo (hZ := hZ) T) (V := V') t.left)
    (ptZ (hZ := hZ) a) ht

/-- `Z`-FPR comes back from the view of a chart. -/
theorem chart_isZFPR (hv' : IsEquivariant actV' (viewAct act) v') (Z : AddSubgroup G)
    (H : IsZFPR hv' Z) : IsZFPR (chartMap_equivariant hv') Z :=
  isFPR_of_view (actP := act.comap (QuotientAddGroup.mk' Z))
    (actV := (chartAct actV' hv').comap (QuotientAddGroup.mk' Z))
    (actW := actV'.comap (QuotientAddGroup.mk' Z)) (fun _ _ => rfl)
    (hv := IsEquivariant.comap (chartMap_equivariant hv') _) (hw := IsEquivariant.comap hv' _) H

/-- Strongly-FPR comes back from the view of a chart. -/
theorem chart_isStronglyFPR (hv' : IsEquivariant actV' (viewAct act) v')
    (H : IsStronglyFPR hv') : IsStronglyFPR (chartMap_equivariant hv') :=
  fun Z => chart_isZFPR hv' Z (H Z)

/-- **An equivariant chart of the view is the extension of an equivariant chart of `X`**: same
scheme, and étale, surjective, `Z`-FPR, strongly-FPR, stable opens come back. -/
theorem exists_chart_of_view (hv' : IsEquivariant actV' (viewAct act) v') :
    ∃ (V : BigFppfOver B S hS) (actV : AAction (fppfO B S hS) G (yoneda.obj V))
      (v : yoneda.obj V ⟶ X) (hv : IsEquivariant actV act v)
      (e : (Over.map (toZ hZ hS)).obj V ≅ V'),
      (OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map v =
          ((OverShriek.relocalizeYonedaIso (toZ hZ hS)).app V).hom ≫ yoneda.map e.hom ≫ v' ∧
      (∀ (Q : MorphismProperty Scheme.{u}) [MorphismProperty.RespectsIso Q],
        (MorphismProperty.inverseImage Q
          (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf v' →
        (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf v) ∧
      (∀ Z : AddSubgroup G, IsZFPR hv' Z → IsZFPR hv Z) ∧
      (IsStronglyFPR hv' → IsStronglyFPR hv) :=
  ⟨chartObj v', chartAct actV' hv', chartMap v', chartMap_equivariant hv', chartIso v',
    map_chartMap v', fun _ _ h => chartMap_presheaf v' h, chart_isZFPR hv',
    chart_isStronglyFPR hv'⟩

end Group

section FP

variable {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Finite presentation does not depend on the base. -/
theorem isFinitePresentation_view_iff (k : Y ⟶ Y') :
    IsFinitePresentation B (⊤_ Scheme.{u}) hZ
        ((OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map k) ↔
      IsFinitePresentation B S hS k :=
  and_congr (holdsOnEveryEtaleChart_relocalizeMap_iff B S _ hS hZ (toZ hZ hS) _ k)
    (and_congr (isQuasiCompact_relocalize_iff B S hS _ hZ (toZ hZ hS) k)
      (isQuasiSeparated_relocalize_iff B S hS _ hZ (toZ hZ hS) k))

/-- The view of an algebraic space is an algebraic space. -/
theorem view_isAlgebraicSpace (hY : IsAlgebraicSpace B S hS Y) :
    IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (view hZ Y) :=
  isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) (toZ hZ hS) Y hY

/-- The morphism from the view of `Y` to the object `A` of the site of `S`, viewed over `ℤ`. -/
def viewMap {A : BigFppfOver B S hS} (p : Y ⟶ yoneda.obj A) :
    view hZ Y ⟶ yoneda.obj ((Over.map (toZ hZ hS)).obj A) :=
  (OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map p ≫
    ((OverShriek.relocalizeYonedaIso (toZ hZ hS)).app A).hom

/-- `viewMap` is of finite presentation. -/
theorem isFinitePresentation_viewMap {A : BigFppfOver B S hS} (p : Y ⟶ yoneda.obj A)
    (hp : IsFinitePresentation B S hS p) :
    IsFinitePresentation B (⊤_ Scheme.{u}) hZ (viewMap (hZ := hZ) p) :=
  isFinitePresentation_of_arrowIso B _ hZ _ _ (𝟙 _)
    ((OverShriek.relocalizeYonedaIso (toZ hZ hS)).app A).hom (by simp [viewMap])
    ((isFinitePresentation_view_iff (hZ := hZ) p).2 hp)

/-- `viewMap` of an invariant morphism is invariant. -/
theorem viewMap_invariant {actY : AAction (fppfO B S hS) M Y} {A : BigFppfOver B S hS}
    {p : Y ⟶ yoneda.obj A}
    (hp : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a : APt (fppfO B S hS) M T) (y : Y.obj T),
      p.app T (actY.smul a y) = p.app T y)
    {U : (ZSite (B := B) hZ)ᵒᵖ} (a : APt (fppfO B (⊤_ Scheme.{u}) hZ) M U)
    (q : (view hZ Y).obj U) :
    (viewMap (hZ := hZ) p).app U ((viewAct actY).smul a q) = (viewMap (hZ := hZ) p).app U q :=
  Over.OverMorphism.ext (congrArg (fun x : Over.mk q.1.1 ⟶ A => x.left)
    (hp (T := op (Over.mk q.1.1)) (ptS (W := U.unop) q.1.1 a) q.1.2))

end FP

section Fixed

variable (act)

/-- The comparison from the view of the fixed points of `act` to the fixed points of the view. -/
def viewFixedHom :
    view hZ (fixedPoints act).toFunctor ⟶ (fixedPoints (viewAct (hZ := hZ) act)).toFunctor where
  app U := ↾fun q => ⟨⟨⟨q.1.1, q.1.2.1⟩, q.2⟩,
    sec_mem_fixed (W := U.unop) (ψ := q.1.1) q.1.2.2⟩
  naturality U U' f := by
    ext q
    refine Subtype.ext ?_
    exact NatTrans.naturality_apply
      ((OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map (fixedPoints act).ι) f q

lemma viewFixedHom_bijective (U : (ZSite (B := B) hZ)ᵒᵖ) :
    Function.Bijective ((viewFixedHom (hZ := hZ) act).app U) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨ψ, s⟩, h⟩ ⟨⟨ψ', s'⟩, h'⟩ he
    have e : (⟨ψ, s.1⟩ : Σ ψ : U.unop.left ⟶ B.obj hS, X.obj (op (Over.mk ψ))) = ⟨ψ', s'.1⟩ :=
      congrArg (fun x => x.1.1) he
    obtain rfl : ψ = ψ' := congrArg Sigma.fst e
    have e2 : s.1 = s'.1 := OverShriek.sigma_snd_inj e
    exact Subtype.ext (congrArg (Sigma.mk ψ) (Subtype.ext e2))
  · rintro ⟨⟨⟨ψ, s⟩, h⟩, hx⟩
    exact ⟨⟨⟨ψ, ⟨s, mem_fixed_of_sec (W := U.unop) (ψ := ψ) hx⟩⟩, h⟩, rfl⟩

instance : IsIso (viewFixedHom (hZ := hZ) act) := by
  have : ∀ U, IsIso ((viewFixedHom (hZ := hZ) act).app U) := fun U =>
    (isIso_iff_bijective _).2 (viewFixedHom_bijective act U)
  exact NatIso.isIso_of_isIso_app _

/-- **The view of the fixed points is the fixed points of the view.** -/
def viewFixedIso : view hZ (fixedPoints act).toFunctor ≅
    (fixedPoints (viewAct (hZ := hZ) act)).toFunctor :=
  asIso (viewFixedHom (hZ := hZ) act)

lemma viewFixedHom_ι :
    (OverShriek.relocalizePresheafFunctor (toZ hZ hS)).map (fixedPoints act).ι =
      viewFixedHom (hZ := hZ) act ≫ (fixedPoints (viewAct (hZ := hZ) act)).ι := rfl

variable {act}

/-- If the fixed points of the view are closed, so are the fixed points of `act`. -/
theorem closed_of_view
    (h : (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf
        (fixedPoints (viewAct (hZ := hZ) act)).ι) :
    (MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (fixedPoints act).ι := by
  refine presheaf_relocalizeMap_of B S _ hS hZ (toZ hZ hS) _ _ ?_
  rw [viewFixedHom_ι]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h

/-- If the fixed points of the view are of finite presentation, so are those of `act`. -/
theorem isFinitePresentation_of_view
    (h : IsFinitePresentation B (⊤_ Scheme.{u}) hZ (fixedPoints (viewAct (hZ := hZ) act)).ι) :
    IsFinitePresentation B S hS (fixedPoints act).ι := by
  refine (isFinitePresentation_view_iff (hZ := hZ) _).1 ?_
  exact isFinitePresentation_of_arrowIso B _ hZ _ _ (inv (viewFixedHom (hZ := hZ) act)) (𝟙 _)
    (by rw [viewFixedHom_ι]; simp) h

end Fixed

end

end AlgMag.LimView

#print axioms AlgMag.LimView.viewAct
#print axioms AlgMag.LimView.viewMap_equivariant
#print axioms AlgMag.LimView.exists_chart_of_view
#print axioms AlgMag.LimView.chart_isAffineHom
#print axioms AlgMag.LimView.chart_isStableOpen
#print axioms AlgMag.LimView.isFinitePresentation_viewMap
#print axioms AlgMag.LimView.view_isAlgebraicSpace
#print axioms AlgMag.LimView.viewMap_invariant
#print axioms AlgMag.LimView.closed_of_view
#print axioms AlgMag.LimView.isFinitePresentation_of_view
