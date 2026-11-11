/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Functorial
import AlgMag.Representation
import AlgMag.AlgebraicSpace
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RingTheory.Etale.Basic

/-!
# Separated targets, infinitesimal lifting along étale morphisms, charts

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, material of §3 and §5.

* `AlgMag.etale_retraction`, `AlgMag.existsUnique_etale_lift`: infinitesimal lifting along an étale
  morphism `U → X`, `U` an `S`-affine scheme, `X` a separated algebraic space (the use of Tags 04XX,
  02H6 in the proof of Proposition 5.1).
* `AlgMag.exists_equalizer`, `AlgMag.eq_of_forall_restrict_eq`: closed equalizers in a separated `X`.
* `AlgMag.spObj`, `AlgMag.spMap`, `AlgMag.spLift`, `AlgMag.spPt`: `Spec R'` as an object of the site
  over an affine `T`.
* `AlgMag.chartObj`, `AlgMag.ptOf`: `U_T`, and points of `U` as algebra maps.
* `AlgMag.spUniversal`: `𝔸(N)_T` as a universal point.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


universe u

namespace AlgMag

/-! ### Infinitesimal lifting -/

section RingLift

/-- The infinitesimal lifting property of an étale ring map, in the form of a retraction: this is
the ring statement behind the use of Tags 04XX, 02H6 in the proof of **Proposition 5.1 (i)**. -/
theorem etale_retraction {R E R₀ : Type u} [CommRing R] [CommRing E] [CommRing R₀]
    (α : R →+* E) (hα : α.Etale) (π : R →+* R₀) (hπ : Function.Surjective π)
    (hnil : IsNilpotent (RingHom.ker π)) (g : E →+* R₀) (hg : g.comp α = π) :
    ∃! s : E →+* R, s.comp α = RingHom.id R ∧ π.comp s = g := by
  algebraize [α]
  letI : Algebra R R₀ := π.toAlgebra
  have hfs : Algebra.FormallySmooth R E := inferInstance
  have hfu : Algebra.FormallyUnramified R E := inferInstance
  let gA : E →ₐ[R] R₀ := { g with commutes' := fun r => congrArg (fun k : R →+* R₀ => k r) hg }
  let πA : R →ₐ[R] R₀ := { π with commutes' := fun _ => rfl }
  have hπA : Function.Surjective πA := hπ
  have hn : IsNilpotent (RingHom.ker πA) := hnil
  let s := Algebra.FormallySmooth.liftOfSurjective gA πA hπA hn
  have hs : πA.comp s = gA := Algebra.FormallySmooth.comp_liftOfSurjective gA πA hπA hn
  refine ⟨s.toRingHom, ⟨RingHom.ext fun r => s.commutes r, ?_⟩, ?_⟩
  · exact RingHom.ext fun e => AlgHom.congr_fun hs e
  · rintro s' ⟨h₁, h₂⟩
    let sA' : E →ₐ[R] R := { s' with commutes' := fun r => congrArg (fun k : R →+* R => k r) h₁ }
    have : sA' = s := Algebra.FormallyUnramified.ext' π hnil _ _ fun x => by
      have e₁ : π (s' x) = g x := congrArg (fun k : E →+* R₀ => k x) h₂
      have e₂ : π (s x) = g x := AlgHom.congr_fun hs x
      exact e₁.trans e₂.symm
    exact RingHom.ext fun x => AlgHom.congr_fun this x

end RingLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

/-- A morphism of schemes over `S` between objects of the site is a morphism of the site. -/
noncomputable def siteHom {V W : BigFppfOver B S hS} (g : (Sch).obj V ⟶ (Sch).obj W)
    (w : g ≫ W.hom.hom = V.hom.hom) : V ⟶ W :=
  Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ w)

@[simp] lemma siteHom_map {V W : BigFppfOver B S hS} (g : (Sch).obj V ⟶ (Sch).obj W)
    (w : g ≫ W.hom.hom = V.hom.hom) : (Sch).map (siteHom g w) = g := rfl

lemma site_hom_ext {V W : BigFppfOver B S hS} {g g' : V ⟶ W} (h : (Sch).map g = (Sch).map g') :
    g = g' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)

lemma site_w {V W : BigFppfOver B S hS} (g : V ⟶ W) : (Sch).map g ≫ W.hom.hom = V.hom.hom :=
  congrArg (fun k => k.hom) (Over.w g)

/-- The final object `S/S` of the site. -/
noncomputable abbrev siteTop : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The structure morphism of a presheaf on the site, to the final presheaf. -/
noncomputable def toBase (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    X ⟶ yoneda.obj (siteTop (B := B) (S := S) (hS := hS)) where
  app V := ↾ fun _ => Over.mkIdTerminal.from _
  naturality _ _ _ := by
    ext _
    exact Over.mkIdTerminal.hom_ext _ _

/-- The algebraic space `X` is separated over `S`: its diagonal is a closed immersion
(Tag 03HL). -/
abbrev IsSeparatedOver (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  Space.IsSeparated B S hS (toBase X)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

lemma yoneda_map_comp_symm {V W : BigFppfOver B S hS} (r : V ⟶ W) (a : X.obj (op W)) :
    yoneda.map r ≫ yonedaEquiv.symm a = yonedaEquiv.symm (X.map r.op a) := by
  ext V' s
  simp

/-- The equalizer of two points of a separated `X` is a closed subscheme. -/
theorem exists_equalizer (hX : IsSeparatedOver X) {W : BigFppfOver B S hS} (a b : X.obj (op W)) :
    ∃ (E : BigFppfOver B S hS) (e : E ⟶ W), AlgebraicGeometry.IsClosedImmersion ((Sch).map e) ∧
      X.map e.op a = X.map e.op b ∧
      ∀ {V : BigFppfOver B S hS} (r : V ⟶ W), X.map r.op a = X.map r.op b → ∃ l : V ⟶ E, l ≫ e = r := by
  let ya : yoneda.obj W ⟶ X := yonedaEquiv.symm a
  let yb : yoneda.obj W ⟶ X := yonedaEquiv.symm b
  have hab : ya ≫ toBase X = yb ≫ toBase X := by
    ext V r
    exact Over.mkIdTerminal.hom_ext _ _
  let g : yoneda.obj W ⟶ pullback (toBase X) (toBase X) := pullback.lift ya yb hab
  let E := hX.1.pullback g
  let e : E ⟶ W := hX.1.snd g
  have hpb : IsPullback (hX.1.fst g) (yoneda.map e) (pullback.diagonal (toBase X)) g :=
    hX.1.isPullback g
  have hcl : AlgebraicGeometry.IsClosedImmersion ((Sch).map e) := hX.property_snd g
  have hgf : g ≫ pullback.fst (toBase X) (toBase X) = ya := pullback.lift_fst _ _ _
  have hgs : g ≫ pullback.snd (toBase X) (toBase X) = yb := pullback.lift_snd _ _ _
  refine ⟨E, e, hcl, ?_, ?_⟩
  · have hw := hpb.w
    have h₁ : hX.1.fst g = yoneda.map e ≫ ya := by
      have := congrArg (fun k => k ≫ pullback.fst (toBase X) (toBase X)) hw
      simpa [hgf] using this
    have h₂ : hX.1.fst g = yoneda.map e ≫ yb := by
      have := congrArg (fun k => k ≫ pullback.snd (toBase X) (toBase X)) hw
      simpa [hgs] using this
    have h := h₁.symm.trans h₂
    rw [yoneda_map_comp_symm, yoneda_map_comp_symm] at h
    exact yonedaEquiv.symm.injective h
  · intro V r hr
    have hyr : yoneda.map r ≫ ya = yoneda.map r ≫ yb := by
      simp only [ya, yb, yoneda_map_comp_symm, hr]
    let t : yoneda.obj V ⟶ X := yoneda.map r ≫ ya
    have hsq : t ≫ pullback.diagonal (toBase X) = yoneda.map r ≫ g := by
      apply pullback.hom_ext
      · simp [t, hgf]
      · simp [t, hgs, hyr]
    let l' := hpb.lift t (yoneda.map r) hsq
    obtain ⟨l, hl⟩ := Functor.Full.map_surjective (F := yoneda) l'
    refine ⟨l, Functor.Faithful.map_injective (F := yoneda) ?_⟩
    rw [Functor.map_comp, hl]
    exact hpb.lift_snd _ _ _

variable {U : BigFppfOver B S hS}

/-- Morphisms to an affine scheme from their map on global sections. -/
noncomputable def homOfGlobal {Z E : Scheme.{u}} [IsAffine E] (s : Γ(E, ⊤) ⟶ Γ(Z, ⊤)) : Z ⟶ E :=
  Z.toSpecΓ ≫ Spec.map s ≫ E.isoSpec.inv

lemma homOfGlobal_appTop {Z E : Scheme.{u}} [IsAffine E] (s : Γ(E, ⊤) ⟶ Γ(Z, ⊤)) :
    (homOfGlobal s).appTop = s := by
  have h₁ : E.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(E, ⊤)).inv := by
    have e : E.isoSpec.hom.appTop ≫ E.isoSpec.inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
      simp
    have e₁ : E.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(E, ⊤)).hom := Scheme.toSpecΓ_appTop E
    rw [e₁] at e
    exact (Iso.hom_comp_eq_id _).mp e
  simp only [homOfGlobal, Scheme.Hom.comp_appTop, h₁, Category.assoc]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Scheme.toSpecΓ_appTop]
  simp

/-- The base change `E = Z ×_X U` of `U → X` along a point `τ` of a separated `X` on an affine `Z`:
it is an affine object of the site, étale over `Z`. -/
theorem exists_etale_chart (hX : IsSeparatedOver X) [IsAffineHom U.hom.hom]
    {f : yoneda.obj U ⟶ X}
    (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Sch)).presheaf f)
    {Z : BigFppfOver B S hS} [IsAffine ((Sch).obj Z)] (τ : X.obj (op Z)) :
    ∃ (E : BigFppfOver B S hS) (e₁ : E ⟶ Z) (e₂ : E ⟶ U), IsAffine ((Sch).obj E) ∧
      ((Sch).map e₁).appTop.hom.Etale ∧ f.app (op E) e₂ = X.map e₁.op τ ∧
      (∀ {V : BigFppfOver B S hS} (l l' : V ⟶ E), l ≫ e₁ = l' ≫ e₁ → l ≫ e₂ = l' ≫ e₂ → l = l') ∧
      (∀ {V : BigFppfOver B S hS} (z : V ⟶ Z) (v : V ⟶ U), f.app (op V) v = X.map z.op τ →
        ∃ l : V ⟶ E, l ≫ e₁ = z ∧ l ≫ e₂ = v) := by
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (Sch) := preservesPullbacks_bigFppfOverToScheme B S hS
  let tZ : Z ⟶ siteTop := Over.mkIdTerminal.from Z
  let tU : U ⟶ siteTop := Over.mkIdTerminal.from U
  let W := pullback tZ tU
  let p₁ : W ⟶ Z := pullback.fst tZ tU
  let p₂ : W ⟶ U := pullback.snd tZ tU
  have hW : IsPullback ((Sch).map p₁) ((Sch).map p₂) ((Sch).map tZ) ((Sch).map tU) :=
    (IsPullback.of_hasPullback tZ tU).map (Sch)
  have htU : IsAffineHom ((Sch).map tU) := by
    have : (Sch).map tU = U.hom.hom := by
      have := site_w tU
      simpa using this
    rw [this]; infer_instance
  have hp₁ : IsAffineHom ((Sch).map p₁) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hW.flip htU
  have hWa : IsAffine ((Sch).obj W) := isAffine_of_isAffineHom ((Sch).map p₁)
  obtain ⟨E, e, hcl, hab, heq⟩ := exists_equalizer hX (W := W) (X.map p₁.op τ) (f.app (op W) p₂)
  have hEa : IsAffine ((Sch).obj E) := isAffine_of_isAffineHom ((Sch).map e)
  let e₁ : E ⟶ Z := e ≫ p₁
  let e₂ : E ⟶ U := e ≫ p₂
  have hfnat : ∀ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ U),
      f.app (op V') (r ≫ v) = X.map r.op (f.app (op V) v) := fun r v =>
    hom_naturality_apply f r.op v
  have h₀ : f.app (op E) e₂ = X.map e₁.op τ := by
    change f.app (op E) (e ≫ p₂) = X.map (e ≫ p₁).op τ
    rw [hfnat, op_comp, Functor.map_comp_apply]
    exact hab.symm
  have hmono : Mono e := by
    refine ⟨fun {_} g₁ g₂ h => site_hom_ext ?_⟩
    have := congrArg (Sch).map h
    simp only [Functor.map_comp] at this
    exact (cancel_mono _).1 this
  have huniq : ∀ {V : BigFppfOver B S hS} (l l' : V ⟶ E), l ≫ e₁ = l' ≫ e₁ → l ≫ e₂ = l' ≫ e₂ →
      l = l' := by
    intro V l l' h₁ h₂
    refine (cancel_mono e).1 (pullback.hom_ext ?_ ?_)
    · simpa [e₁, p₁] using h₁
    · simpa [e₂, p₂] using h₂
  have hex : ∀ {V : BigFppfOver B S hS} (z : V ⟶ Z) (v : V ⟶ U), f.app (op V) v = X.map z.op τ →
      ∃ l : V ⟶ E, l ≫ e₁ = z ∧ l ≫ e₂ = v := by
    intro V z v hv
    let r : V ⟶ W := pullback.lift z v (Over.mkIdTerminal.hom_ext _ _)
    have hr₁ : r ≫ p₁ = z := pullback.lift_fst _ _ _
    have hr₂ : r ≫ p₂ = v := pullback.lift_snd _ _ _
    obtain ⟨l, hl⟩ := heq r (by
      rw [← Functor.map_comp_apply, ← op_comp, hr₁]
      change _ = X.map r.op (f.app (op W) p₂)
      rw [← hfnat, hr₂, hv])
    exact ⟨l, by simp [e₁, ← Category.assoc, hl, hr₁], by simp [e₂, ← Category.assoc, hl, hr₂]⟩
  -- `E → Z` is étale, being a base change of `U → X`
  have hsq : IsPullback (yoneda.map e₂) (yoneda.map e₁) f (yonedaEquiv.symm τ) := by
    refine IsPullback.of_forall_isPullback_app fun V => ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · ext (l : (unop V) ⟶ E)
      change f.app V (l ≫ e₂) = X.map (l ≫ e₁).op τ
      rw [show f.app V (l ≫ e₂) = X.map l.op (f.app (op E) e₂) from hfnat l e₂, h₀,
        show (l ≫ e₁).op = e₁.op ≫ l.op from rfl, Functor.map_comp_apply]
    · rintro (l : (unop V) ⟶ E) (l' : (unop V) ⟶ E) ⟨h₁, h₂⟩
      exact huniq l l' h₂ h₁
    · intro (v : (unop V) ⟶ U) (z : (unop V) ⟶ Z) hvz
      obtain ⟨l, hl₁, hl₂⟩ := hex z v (by simpa using hvz)
      exact ⟨l, hl₂, hl₁⟩
  have het : AlgebraicGeometry.Etale ((Sch).map e₁) := hf.2 _ _ e₁ hsq
  have hring : ((Sch).map e₁).appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).1 het
  exact ⟨E, e₁, e₂, hEa, hring, h₀, huniq, hex⟩

/-- **Infinitesimal lifting along `U → X`** (Tags 04XX, 02H6, as used in the proof of
**Proposition 5.1**): let `U → X` be étale from an `S`-affine scheme to a separated `X`, and `Z₀ → Z` a
thickening of affine objects of the site, with nilpotent kernel. A point `τ` of `X` on `Z` and a lift
`v₀` of it on `Z₀` extend to a unique lift on `Z`. -/
theorem existsUnique_etale_lift (hX : IsSeparatedOver X) [IsAffineHom U.hom.hom]
    {f : yoneda.obj U ⟶ X}
    (hf : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (Sch)).presheaf f)
    {Z₀ Z : BigFppfOver B S hS} (i : Z₀ ⟶ Z) [IsAffine ((Sch).obj Z₀)] [IsAffine ((Sch).obj Z)]
    (hsurj : Function.Surjective ((Sch).map i).appTop.hom)
    (hnil : IsNilpotent (RingHom.ker ((Sch).map i).appTop.hom))
    (τ : X.obj (op Z)) (v₀ : Z₀ ⟶ U) (hv₀ : f.app (op Z₀) v₀ = X.map i.op τ) :
    ∃! v : Z ⟶ U, i ≫ v = v₀ ∧ f.app (op Z) v = τ := by
  obtain ⟨E, e₁, e₂, hEa, hring, h₀, huniq, hex⟩ := exists_etale_chart hX hf τ
  have hfnat : ∀ {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ U),
      f.app (op V') (r ≫ v) = X.map r.op (f.app (op V) v) := fun r v =>
    hom_naturality_apply f r.op v
  obtain ⟨V₀, hV₁, hV₂⟩ := hex i v₀ hv₀
  have hgα : ((Sch).map V₀).appTop.hom.comp ((Sch).map e₁).appTop.hom =
      ((Sch).map i).appTop.hom := by
    rw [← hV₁, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨s, ⟨hs₁, hs₂⟩, hsu⟩ := etale_retraction _ hring _ hsurj hnil _ hgα
  let zS : (Sch).obj Z ⟶ (Sch).obj E := homOfGlobal (CommRingCat.ofHom s)
  have hzS : zS.appTop = CommRingCat.ofHom s := homOfGlobal_appTop _
  have hz₁ : zS ≫ (Sch).map e₁ = 𝟙 _ := by
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, hzS]
    ext x
    simpa using congrArg (fun k : _ →+* _ => k x) hs₁
  let z : Z ⟶ E := siteHom zS (by
    rw [← site_w e₁, ← Category.assoc, hz₁, Category.id_comp])
  have hz₁' : z ≫ e₁ = 𝟙 Z := site_hom_ext (by rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact hz₁)
  have hiz : i ≫ z = V₀ := by
    refine site_hom_ext (ext_of_isAffine ?_)
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, siteHom_map, hzS]
    ext x
    simpa using congrArg (fun k : _ →+* _ => k x) hs₂
  refine ⟨z ≫ e₂, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, hiz, hV₂]
  · rw [hfnat, h₀, ← Functor.map_comp_apply, ← op_comp, hz₁']
    simp
  · rintro v' ⟨hv'₁, hv'₂⟩
    obtain ⟨l, hl₁, hl₂⟩ := hex (𝟙 Z) v' (by simpa using hv'₂)
    have hil : i ≫ l = V₀ := huniq _ _ (by simp [hl₁, hV₁]) (by simp [hl₂, hV₂, hv'₁])
    have hsl : ((Sch).map l).appTop.hom = s := by
      refine hsu _ ⟨?_, ?_⟩
      · have h : ((Sch).map e₁).appTop ≫ ((Sch).map l).appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, ← Functor.map_comp, hl₁]; simp
        exact congrArg CommRingCat.Hom.hom h
      · have h : ((Sch).map l).appTop ≫ ((Sch).map i).appTop = ((Sch).map V₀).appTop := by
          rw [← Scheme.Hom.comp_appTop, ← Functor.map_comp, hil]
        exact congrArg CommRingCat.Hom.hom h
    have hlz : l = z := by
      refine site_hom_ext (ext_of_isAffine ?_)
      rw [siteHom_map, hzS]
      ext x
      exact congrArg (fun k : _ →+* _ => k x) hsl
    rw [← hlz, hl₂]

/-- A point of a separated `X` is determined by its restrictions to a family of closed subschemes
`Zₖ → Z` of an affine `Z` whose ideals have trivial intersection. This replaces, in the proof of
**Proposition 5.1 (i)**, the implicit claim that the filling `𝔸(N)_T → U_T` lies over `X`. -/
theorem eq_of_forall_restrict_eq (hX : IsSeparatedOver X) {Z : BigFppfOver B S hS}
    [IsAffine ((Sch).obj Z)] {ι : Type*} {Zk : ι → BigFppfOver B S hS} (ik : ∀ k, Zk k ⟶ Z)
    (hinj : ∀ x : Γ((Sch).obj Z, ⊤), (∀ k, ((Sch).map (ik k)).appTop.hom x = 0) → x = 0)
    {a b : X.obj (op Z)} (hab : ∀ k, X.map (ik k).op a = X.map (ik k).op b) : a = b := by
  obtain ⟨E, e, hcl, heq, hlift⟩ := exists_equalizer hX a b
  have hEa : IsAffine ((Sch).obj E) := isAffine_of_isAffineHom ((Sch).map e)
  have hker : Function.Injective ((Sch).map e).appTop.hom := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => hinj x fun k => ?_
    obtain ⟨l, hl⟩ := hlift (ik k) (hab k)
    rw [← hl, Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((Sch).map l).appTop.hom (((Sch).map e).appTop.hom x) = 0
    rw [hx, map_zero]
  have hisoE : IsIso ((Sch).map e) :=
    AlgebraicGeometry.IsClosedImmersion.isIso_of_injective_of_isAffine hker
  -- a section
  let zS := inv ((Sch).map e)
  let z : Z ⟶ E := siteHom zS (by
    rw [← site_w e, IsIso.inv_hom_id_assoc])
  have hz : z ≫ e = 𝟙 Z := site_hom_ext (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, siteHom_map, IsIso.inv_hom_id])
  have := congrArg (X.map z.op) heq
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hz] at this
  simpa using this

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

section Sp

/-- The ring of functions of an object of the site. -/
noncomputable abbrev RT (T : BigFppfOver B S hS) : CommRingCat.{u} := Γ((Sch).obj T, ⊤)

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]


/-- `Spec R'` as an object of the site over `T`, for a ring `R'` over `Γ(T)`. -/
noncomputable def spObj {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) : BigFppfOver B S hS :=
  siteObject B S hS hC (Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv ≫ T.hom.hom)

instance {R' : Type u} [CommRing R'] (ρ : RT T →+* R') (hC : B.Contains (Spec (.of R'))) :
    IsAffine ((Sch).obj (spObj T ρ hC)) := by
  change IsAffine (Spec _)
  infer_instance

/-- `Spec R' → T`. -/
noncomputable def spToT {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) : spObj T ρ hC ⟶ T :=
  siteHom (Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv) rfl

/-- `Spec R'' → Spec R'` over `T`, for a ring map over `Γ(T)`. -/
noncomputable def spMap {R' R'' : Type u} [CommRing R'] [CommRing R''] {ρ : RT T →+* R'}
    {ρ' : RT T →+* R''} {hC : B.Contains (Spec (.of R'))} {hC' : B.Contains (Spec (.of R''))}
    (π : R' →+* R'') (hπ : π.comp ρ = ρ') : spObj T ρ' hC' ⟶ spObj T ρ hC :=
  siteHom (Spec.map (CommRingCat.ofHom π)) (by
    subst hπ
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl)

@[simp] lemma spMap_toT {R' R'' : Type u} [CommRing R'] [CommRing R''] {ρ : RT T →+* R'}
    {ρ' : RT T →+* R''} {hC : B.Contains (Spec (.of R'))} {hC' : B.Contains (Spec (.of R''))}
    (π : R' →+* R'') (hπ : π.comp ρ = ρ') :
    spMap T (hC := hC) (hC' := hC') π hπ ≫ spToT T ρ hC = spToT T ρ' hC' := by
  subst hπ
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

lemma spMap_comp {R' R'' R''' : Type u} [CommRing R'] [CommRing R''] [CommRing R''']
    {ρ : RT T →+* R'} {ρ' : RT T →+* R''} {ρ'' : RT T →+* R'''}
    {hC : B.Contains (Spec (.of R'))} {hC' : B.Contains (Spec (.of R''))}
    {hC'' : B.Contains (Spec (.of R'''))} (π : R' →+* R'') (hπ : π.comp ρ = ρ')
    (π' : R'' →+* R''') (hπ' : π'.comp ρ' = ρ'') :
    spMap T (hC := hC') (hC' := hC'') π' hπ' ≫ spMap T (hC := hC) (hC' := hC') π hπ =
      spMap T (hC := hC) (hC' := hC'') (π'.comp π) (by rw [RingHom.comp_assoc, hπ, hπ']) := by
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Elements of `R'` as global functions on `Spec R'`. -/
noncomputable def spSec {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) : R' →+* Γ((Sch).obj (spObj T ρ hC), ⊤) :=
  (Scheme.ΓSpecIso (.of R')).inv.hom

lemma spSec_bijective {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) : Function.Bijective (spSec T ρ hC) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R')).inv

lemma spMap_appTop {R' R'' : Type u} [CommRing R'] [CommRing R''] {ρ : RT T →+* R'}
    {ρ' : RT T →+* R''} {hC : B.Contains (Spec (.of R'))} {hC' : B.Contains (Spec (.of R''))}
    (π : R' →+* R'') (hπ : π.comp ρ = ρ') (x : R') :
    ((Sch).map (spMap T (hC := hC) (hC' := hC') π hπ)).appTop.hom (spSec T ρ hC x) =
      spSec T ρ' hC' (π x) :=
  congrArg (fun k => k.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom π)).symm

lemma spToT_appTop {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) (x : RT T) :
    ((Sch).map (spToT T ρ hC)).appTop.hom x = spSec T ρ hC (ρ x) := by
  have h : ((Sch).obj T).isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ((Sch).obj T, ⊤)).inv := by
    have e : ((Sch).obj T).isoSpec.hom.appTop ≫ ((Sch).obj T).isoSpec.inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
      simp
    have e₁ : ((Sch).obj T).isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ((Sch).obj T, ⊤)).hom :=
      Scheme.toSpecΓ_appTop _
    rw [e₁] at e
    exact (Iso.hom_comp_eq_id _).mp e
  have h₂ : ((Sch).map (spToT T ρ hC)).appTop =
      (Scheme.ΓSpecIso Γ((Sch).obj T, ⊤)).inv ≫ (Spec.map (CommRingCat.ofHom ρ)).appTop := by
    change (Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop, h]
  rw [h₂]
  have h₃ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)
  exact congrArg (fun k => k.hom x) h₃.symm

/-- The morphism `T' → Spec R'` over `T` given by a ring map `R' → Γ(T')`. -/
noncomputable def spLift {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (ψ : R' →+* Γ((Sch).obj T', ⊤)) (hψ : ψ.comp ρ = ((Sch).map t).appTop.hom) :
    T' ⟶ spObj T ρ hC :=
  siteHom (((Sch).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)) (by
    have key : ((Sch).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv = (Sch).map t := by
      refine ext_of_isAffine ?_
      have hsub : homOfGlobal (Z := (Sch).obj T') (E := (Sch).obj T)
          (CommRingCat.ofHom (ψ.comp ρ)) = (Sch).map t := by
        refine ext_of_isAffine ?_
        rw [homOfGlobal_appTop, hψ]
        rfl
      rw [← hsub, homOfGlobal, ← Category.assoc (Spec.map _), ← Spec.map_comp]
      rfl
    change ((Sch).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom ρ) ≫ ((Sch).obj T).isoSpec.inv ≫ T.hom.hom = _
    rw [← site_w t, ← key]
    simp only [Category.assoc])

lemma spLift_appTop {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (ψ : R' →+* Γ((Sch).obj T', ⊤)) (hψ : ψ.comp ρ = ((Sch).map t).appTop.hom) (x : R') :
    ((Sch).map (spLift T ρ hC t ψ hψ)).appTop.hom (spSec T ρ hC x) = ψ x := by
  have h : (Scheme.ΓSpecIso (.of R')).inv ≫
      (((Sch).obj T').toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop = CommRingCat.ofHom ψ := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  exact congrArg (fun k => k.hom x) h

/-- Two morphisms to `Spec R'` are equal if they agree on functions. -/
lemma sp_hom_ext {R' : Type u} [CommRing R'] {ρ : RT T →+* R'}
    {hC : B.Contains (Spec (.of R'))} {T' : BigFppfOver B S hS} {l l' : T' ⟶ spObj T ρ hC}
    (h : ∀ x, ((Sch).map l).appTop.hom (spSec T ρ hC x) =
      ((Sch).map l').appTop.hom (spSec T ρ hC x)) : l = l' := by
  refine site_hom_ext (ext_of_isAffine ?_)
  ext y
  obtain ⟨x, rfl⟩ := (spSec_bijective T ρ hC).2 y
  exact h x

lemma spLift_toT {R' : Type u} [CommRing R'] (ρ : RT T →+* R')
    (hC : B.Contains (Spec (.of R'))) {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (ψ : R' →+* Γ((Sch).obj T', ⊤)) (hψ : ψ.comp ρ = ((Sch).map t).appTop.hom) :
    spLift T ρ hC t ψ hψ ≫ spToT T ρ hC = t := by
  refine site_hom_ext (ext_of_isAffine ?_)
  ext x
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  change ((Sch).map (spLift T ρ hC t ψ hψ)).appTop.hom (((Sch).map (spToT T ρ hC)).appTop.hom x) = _
  rw [spToT_appTop, spLift_appTop]
  exact congrArg (fun k : _ →+* _ => k x) hψ

end Sp

end AlgMag

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Chart

variable (T U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffineHom (U.hom.hom)]

/-- `U_T = U ×_S T`, as an object of the site. -/
noncomputable def chartObj : BigFppfOver B S hS :=
  pullback (Over.mkIdTerminal.from T : T ⟶ siteTop) (Over.mkIdTerminal.from U : U ⟶ siteTop)

/-- `U_T → T`. -/
noncomputable def chartFst : chartObj T U ⟶ T := pullback.fst _ _

/-- `U_T → U`. -/
noncomputable def chartSnd : chartObj T U ⟶ U := pullback.snd _ _

instance : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartObj T U)) := by
  have hW := (IsPullback.of_hasPullback (Over.mkIdTerminal.from T : T ⟶ siteTop)
    (Over.mkIdTerminal.from U : U ⟶ siteTop)).map (Sch)
  have htU : IsAffineHom ((Sch).map (Over.mkIdTerminal.from U : U ⟶ siteTop)) := by
    have : (Sch).map (Over.mkIdTerminal.from U : U ⟶ siteTop) = U.hom.hom := by
      have := site_w (Over.mkIdTerminal.from U : U ⟶ siteTop)
      simpa using this
    rw [this]; infer_instance
  have hp₁ : IsAffineHom ((Sch).map (chartFst T U)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hW.flip htU
  exact isAffine_of_isAffineHom ((Sch).map (chartFst T U))

/-- The algebra of `U_T`. -/
noncomputable abbrev chartA : CommRingCat.{u} := RT (chartObj T U)

/-- The structure map `Γ(T) → Γ(U_T)`. -/
noncomputable def chartα : RT T →+* chartA T U := ((Sch).map (chartFst T U)).appTop.hom

variable {T U}
variable {R' : Type u} [CommRing R'] {ρ : RT T →+* R'} {hC : B.Contains (Spec (.of R'))}

/-- The `Spec R' → U_T` of an algebra map `Γ(U_T) → R'`. -/
noncomputable def chartLift (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ) :
    spObj T ρ hC ⟶ chartObj T U :=
  siteHom (homOfGlobal (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of R')).inv)) (by
    have h : homOfGlobal (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of R')).inv) ≫ (Sch).map (chartFst T U) =
        (Sch).map (spToT T ρ hC) := by
      refine ext_of_isAffine ?_
      rw [Scheme.Hom.comp_appTop, homOfGlobal_appTop]
      ext x
      change spSec T ρ hC (ψ (chartα T U x)) = _
      refine Eq.trans ?_ (spToT_appTop T ρ hC x).symm
      exact congrArg (spSec T ρ hC) (congrArg (fun k : _ →+* _ => k x) hψ)
    rw [← site_w (chartFst T U), ← Category.assoc]
    exact (congrArg (· ≫ T.hom.hom) h).trans (site_w _))

lemma chartLift_appTop (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ) (y) :
    ((Sch).map (chartLift (hC := hC) ψ hψ)).appTop.hom y = spSec T ρ hC (ψ y) := by
  have := homOfGlobal_appTop (Z := (Sch).obj (spObj T ρ hC)) (E := (Sch).obj (chartObj T U))
    (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of R')).inv)
  exact congrArg (fun k => k.hom y) this

lemma chartLift_fst (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ) :
    chartLift (hC := hC) ψ hψ ≫ chartFst T U = spToT T ρ hC := by
  refine site_hom_ext (ext_of_isAffine ?_)
  ext x
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  change ((Sch).map (chartLift (hC := hC) ψ hψ)).appTop.hom (chartα T U x) = _
  rw [chartLift_appTop, spToT_appTop]
  exact congrArg (spSec T ρ hC) (congrArg (fun k : _ →+* _ => k x) hψ)

/-- The point of `U` on `Spec R'` given by an algebra map `Γ(U_T) → R'`. -/
noncomputable def ptOf (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ) :
    spObj T ρ hC ⟶ U :=
  chartLift ψ hψ ≫ chartSnd T U

lemma chart_hom_ext {V : BigFppfOver B S hS} {l l' : V ⟶ chartObj T U}
    (h₁ : l ≫ chartFst T U = l' ≫ chartFst T U) (h₂ : l ≫ chartSnd T U = l' ≫ chartSnd T U) :
    l = l' :=
  pullback.hom_ext h₁ h₂

theorem ptOf_injective {ψ ψ' : chartA T U →+* R'} (hψ : ψ.comp (chartα T U) = ρ)
    (hψ' : ψ'.comp (chartα T U) = ρ) (h : ptOf (hC := hC) ψ hψ = ptOf (hC := hC) ψ' hψ') :
    ψ = ψ' := by
  have e : chartLift (hC := hC) ψ hψ = chartLift (hC := hC) ψ' hψ' :=
    chart_hom_ext (by rw [chartLift_fst, chartLift_fst]) h
  ext y
  apply (spSec_bijective T ρ hC).1
  rw [← chartLift_appTop (hC := hC) ψ hψ, ← chartLift_appTop (hC := hC) ψ' hψ', e]

theorem exists_ptOf (v : spObj T ρ hC ⟶ U) :
    ∃ (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ), ptOf (hC := hC) ψ hψ = v := by
  let r : spObj T ρ hC ⟶ chartObj T U :=
    pullback.lift (spToT T ρ hC) v (Over.mkIdTerminal.hom_ext _ _)
  have hr₁ : r ≫ chartFst T U = spToT T ρ hC := pullback.lift_fst _ _ _
  have hr₂ : r ≫ chartSnd T U = v := pullback.lift_snd _ _ _
  let ψ : chartA T U →+* R' := (Scheme.ΓSpecIso (.of R')).hom.hom.comp ((Sch).map r).appTop.hom
  have hsec : ∀ y, spSec T ρ hC (ψ y) = ((Sch).map r).appTop.hom y := fun y => by
    change ((Scheme.ΓSpecIso (.of R')).hom ≫ (Scheme.ΓSpecIso (.of R')).inv).hom _ = _
    rw [Iso.hom_inv_id]
    rfl
  have hψ : ψ.comp (chartα T U) = ρ := by
    ext x
    apply (spSec_bijective T ρ hC).1
    change spSec T ρ hC (ψ (chartα T U x)) = _
    rw [hsec, ← spToT_appTop, ← hr₁, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  refine ⟨ψ, hψ, ?_⟩
  have : chartLift (hC := hC) ψ hψ = r := by
    refine site_hom_ext (ext_of_isAffine ?_)
    ext y
    rw [← hsec, ← chartLift_appTop (hC := hC) ψ hψ]
  rw [ptOf, this, hr₂]

lemma spMap_comp_ptOf {R'' : Type u} [CommRing R''] {ρ' : RT T →+* R''}
    {hC' : B.Contains (Spec (.of R''))} (π : R' →+* R'') (hπ : π.comp ρ = ρ')
    (ψ : chartA T U →+* R') (hψ : ψ.comp (chartα T U) = ρ) :
    spMap T (hC := hC) (hC' := hC') π hπ ≫ ptOf ψ hψ =
      ptOf (hC := hC') (π.comp ψ) (by rw [RingHom.comp_assoc, hψ, hπ]) := by
  have : spMap T (hC := hC) (hC' := hC') π hπ ≫ chartLift ψ hψ =
      chartLift (hC := hC') (π.comp ψ) (by rw [RingHom.comp_assoc, hψ, hπ]) := by
    refine site_hom_ext (ext_of_isAffine ?_)
    ext y
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((Sch).map (spMap T π hπ)).appTop.hom
      (((Sch).map (chartLift ψ hψ)).appTop.hom y) = _
    rw [chartLift_appTop, spMap_appTop, chartLift_appTop]
    rfl
  rw [ptOf, ← Category.assoc, this, ptOf]

end Chart

section Points

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
variable {R' : Type u} [CommRing R'] {ρ : RT T →+* R'} {hC : B.Contains (Spec (.of R'))}

/-- A monoid map to `R'` as a point of `𝔸(P)` on `Spec R'`. -/
noncomputable def spPt {P : Type*} [AddCommMonoid P] (a : Multiplicative P →* R') :
    APt (fppfO B S hS) P (op (spObj T ρ hC)) :=
  (spSec T ρ hC).toMonoidHom.comp a

@[simp] lemma spPt_apply {P : Type*} [AddCommMonoid P] (a : Multiplicative P →* R') (p) :
    spPt (T := T) (ρ := ρ) (hC := hC) a p = spSec T ρ hC (a p) := rfl

lemma spPt_res {P : Type*} [AddCommMonoid P] {R'' : Type u} [CommRing R''] {ρ' : RT T →+* R''}
    {hC' : B.Contains (Spec (.of R''))} (π : R' →+* R'') (hπ : π.comp ρ = ρ')
    (a : Multiplicative P →* R') :
    APt.res (spMap T (hC := hC) (hC' := hC') π hπ).op (spPt a) = spPt (π.toMonoidHom.comp a) := by
  refine MonoidHom.ext fun p => ?_
  exact spMap_appTop T (hC := hC) (hC' := hC') π hπ (a p)

lemma res_spPt_apply {P : Type*} [AddCommMonoid P] {T' : BigFppfOver B S hS}
    (s : T' ⟶ spObj T ρ hC) (b : Multiplicative P →* R') (p) :
    APt.res s.op (spPt (T := T) (ρ := ρ) (hC := hC) b) p =
      ((Sch).map s).appTop.hom (spSec T ρ hC (b p)) := rfl

variable {M : Type u} [AddCommMonoid M]

lemma lift_single' {A C P : Type*} [Semiring A] [CommSemiring C] [AddMonoid P] (f : A →+* C)
    (g : Multiplicative P →* C) (h) (r : A) (n : P) :
    AddMonoidAlgebra.liftNCRingHom f g h (AddMonoidAlgebra.single n r) =
      f r * g (Multiplicative.ofAdd n) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

/-- Ring maps, with the instances of the `CommRing` structures: this keeps the unifier from unfolding
schemes when it compares the instance paths on `AddMonoidAlgebra`. -/
abbrev RH (A C : Type*) [CommRing A] [CommRing C] := A →+* C

/-- The ring map `Γ(T)[N] → Γ(T')` of a point of `𝔸(N)` over `t : T' → T`. -/
noncomputable def pointRing {N : AddSubmonoid M} {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) : RH (AddMonoidAlgebra (RT T) N) Γ((Sch).obj T', ⊤) :=
  AddMonoidAlgebra.liftNCRingHom ((Sch).map t).appTop.hom
    (show Multiplicative N →* Γ((Sch).obj T', ⊤) from a) (fun _ _ => Commute.all _ _)

lemma pointRing_single {N : AddSubmonoid M} {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) (r : RT T) (n : N) :
    pointRing t a (AddMonoidAlgebra.single n r) =
      ((Sch).map t).appTop.hom r *
        (show Multiplicative N →* Γ((Sch).obj T', ⊤) from a) (Multiplicative.ofAdd n) :=
  lift_single' _ _ _ _ _

/-- The structure map `Γ(T) → Γ(T)[N]`. -/
noncomputable def ρN (T : BigFppfOver B S hS) (N : AddSubmonoid M) :
    RH (RT T) (AddMonoidAlgebra (RT T) N) :=
  AddMonoidAlgebra.singleZeroRingHom

lemma pointRing_comp {N : AddSubmonoid M} {T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) N (op T')) :
    (pointRing t a).comp (ρN T N) = ((Sch).map t).appTop.hom := by
  ext x
  change pointRing t a (AddMonoidAlgebra.single 0 x) = _
  rw [pointRing_single, ofAdd_zero, map_one, mul_one]

/-- The monoid map `N → R[N]`. -/
noncomputable def monN (R : Type*) [CommRing R] (N : AddSubmonoid M) :
    Multiplicative N →* AddMonoidAlgebra R N where
  toFun n := AddMonoidAlgebra.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' x y := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]; rfl

set_option maxHeartbeats 2000000 in
/-- The classifying map of a point of `𝔸(N)`. -/
noncomputable def spUniLift (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (N : AddSubmonoid M)
    (hC : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) N)))) {T' : BigFppfOver B S hS}
    (t : T' ⟶ T) (a : APt (fppfO B S hS) N (op T')) :
    T' ⟶ spObj T (ρN T N) hC :=
  spLift T (ρN T N) hC t (pointRing t a) (pointRing_comp t a)

/-- `𝔸(N)_T = Spec Γ(T)[N]`, as a universal point in the sense of `AlgMag.UniversalPoint`. -/
noncomputable def spUniversal (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (N : AddSubmonoid M)
    (hC : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) N)))) :
    UniversalPoint (fppfO B S hS) N T where
  P := spObj T (ρN T N) hC
  π := spToT T (ρN T N) hC
  u := spPt (monN _ N)
  lift {T'} t a := spUniLift T N hC t a
  lift_π t a := spLift_toT T (ρN T N) hC t (pointRing t a) (pointRing_comp t a)
  res_lift {T'} t a := by
    refine MonoidHom.ext (fun n => ?_)
    rw [res_spPt_apply, spUniLift, spLift_appTop, show monN (RT T) N n =
      AddMonoidAlgebra.single (Multiplicative.toAdd n) 1 from rfl, pointRing_single, map_one, one_mul]
    rfl
  uniq {T'} t a s h₁ h₂ := by
    refine sp_hom_ext T fun x => ?_
    rw [spUniLift, spLift_appTop]
    let g₁ : AddMonoidAlgebra (RT T) N →+* Γ((Sch).obj T', ⊤) :=
      ((Sch).map s).appTop.hom.comp (spSec T (ρN T N) hC)
    suffices g₁ = pointRing t a from congrArg (fun k : _ →+* _ => k x) this
    refine AddMonoidAlgebra.ringHom_ext (fun c => ?_) (fun n => ?_)
    · have e : g₁ (AddMonoidAlgebra.single 0 c) = ((Sch).map (s ≫ spToT T (ρN T N) hC)).appTop.hom c := by
        rw [Functor.map_comp, Scheme.Hom.comp_appTop]
        change _ = ((Sch).map s).appTop.hom (((Sch).map (spToT T (ρN T N) hC)).appTop.hom c)
        rw [spToT_appTop]
        rfl
      rw [e, h₁, pointRing_single, ofAdd_zero, map_one, mul_one]
    · have := congrArg (fun k : APt (fppfO B S hS) N (op T') => k (Multiplicative.ofAdd n)) h₂
      change ((Sch).map s).appTop.hom (spSec T (ρN T N) hC (AddMonoidAlgebra.single n 1)) = _
      rw [pointRing_single, map_one, one_mul]
      exact this

end Points

end AlgMag
