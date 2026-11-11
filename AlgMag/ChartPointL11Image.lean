/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointL11Ring
import AlgMag.ChartPointAssemble
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject

/-!
# The scheme-theoretic image of the orbit (Lemma 1.1 of the chart-lemma proof, step A)

* `exists_pull`: the fibre product of two points of a separated `X`, one of them affine.
* `kills_of_mem_image`, `exists_closed_image`: the scheme-theoretic image of a morphism of affine
  objects of the site is cut out by the kernel.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Pull

variable {O T W : BigFppfOver B S hS} {o : yoneda.obj O ⟶ X} {t : yoneda.obj T ⟶ X}
  {p : W ⟶ O} {w : W ⟶ T}

lemma pb_of_app_eq {V : BigFppfOver B S hS} {a : V ⟶ O} {b : V ⟶ T}
    (h : o.app (op V) a = t.app (op V) b) : yoneda.map a ≫ o = yoneda.map b ≫ t := by
  apply yonedaEquiv.injective
  simpa [yonedaEquiv] using h

lemma pb_comm (sq : IsPullback (yoneda.map p) (yoneda.map w) o t) :
    o.app (op W) p = t.app (op W) w := by
  have := congrArg (fun k => k.app (op W) (𝟙 W)) sq.w
  simpa using this

/-- Lifting in a pullback square of representables. -/
lemma pb_lift (sq : IsPullback (yoneda.map p) (yoneda.map w) o t) {V : BigFppfOver B S hS}
    (a : V ⟶ O) (b : V ⟶ T) (h : o.app (op V) a = t.app (op V) b) :
    ∃ l : V ⟶ W, l ≫ p = a ∧ l ≫ w = b := by
  obtain ⟨l, hl⟩ := Functor.Full.map_surjective (F := yoneda)
    (sq.lift (yoneda.map a) (yoneda.map b) (pb_of_app_eq h))
  refine ⟨l, Functor.Faithful.map_injective (F := yoneda) ?_,
    Functor.Faithful.map_injective (F := yoneda) ?_⟩
  · rw [Functor.map_comp, hl]; exact sq.lift_fst _ _ _
  · rw [Functor.map_comp, hl]; exact sq.lift_snd _ _ _

lemma pb_ext (sq : IsPullback (yoneda.map p) (yoneda.map w) o t) {V : BigFppfOver B S hS}
    {l l' : V ⟶ W} (h1 : l ≫ p = l' ≫ p) (h2 : l ≫ w = l' ≫ w) : l = l' := by
  apply Functor.Faithful.map_injective (F := yoneda)
  refine sq.hom_ext ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, h1]
  · rw [← Functor.map_comp, ← Functor.map_comp, h2]

/-- A pullback square of representables, from its elementary description. -/
lemma pb_mk (hc : o.app (op W) p = t.app (op W) w)
    (hl : ∀ {V : BigFppfOver B S hS} (a : V ⟶ O) (b : V ⟶ T), o.app (op V) a = t.app (op V) b →
      ∃ l : V ⟶ W, l ≫ p = a ∧ l ≫ w = b)
    (he : ∀ {V : BigFppfOver B S hS} {l l' : V ⟶ W}, l ≫ p = l' ≫ p → l ≫ w = l' ≫ w → l = l') :
    IsPullback (yoneda.map p) (yoneda.map w) o t := by
  have hcomm : yoneda.map p ≫ o = yoneda.map w ≫ t := pb_of_app_eq hc
  refine IsPullback.of_forall_isPullback_app fun V => ?_
  rw [Types.isPullback_iff]
  refine ⟨congr_app hcomm V, fun x y h => he h.1 h.2, fun a b hab => ?_⟩
  obtain ⟨l, h1, h2⟩ := hl a b hab
  exact ⟨l, h1, h2⟩

end Pull

section Exists

variable [IsAffine S]

instance instAffineTop' : IsAffine ((SCH).obj (siteTop (B := B) (S := S) (hS := hS))) :=
  inferInstanceAs (IsAffine S)

/-- The fibre product of a point `τ` of a separated `X` with a point `u` on an affine `U`: it is
affine over `Z`. -/
theorem exists_pull (hX : AlgMag.IsSeparatedOver X) {Z U : BigFppfOver B S hS}
    [IsAffine ((SCH).obj U)] (u : yoneda.obj U ⟶ X) (τ : yoneda.obj Z ⟶ X) :
    ∃ (E : BigFppfOver B S hS) (e₂ : E ⟶ U) (e₁ : E ⟶ Z), IsAffineHom ((SCH).map e₁) ∧
      IsPullback (yoneda.map e₂) (yoneda.map e₁) u τ := by
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  let tZ : Z ⟶ siteTop := Over.mkIdTerminal.from Z
  let tU : U ⟶ siteTop := Over.mkIdTerminal.from U
  let W := pullback tZ tU
  let p₁ : W ⟶ Z := pullback.fst tZ tU
  let p₂ : W ⟶ U := pullback.snd tZ tU
  have hW : IsPullback ((SCH).map p₁) ((SCH).map p₂) ((SCH).map tZ) ((SCH).map tU) :=
    (IsPullback.of_hasPullback tZ tU).map (SCH)
  have htU : IsAffineHom ((SCH).map tU) := isAffineHom_of_isAffine _
  have hp₁ : IsAffineHom ((SCH).map p₁) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hW.flip htU
  obtain ⟨E, e, hcl, hab, heq⟩ := exists_equalizer hX (W := W) (τ.app (op W) p₁) (u.app (op W) p₂)
  have hmono : Mono e := by
    refine ⟨fun {_} g₁ g₂ h => site_hom_ext ?_⟩
    have := congrArg (SCH).map h
    simp only [Functor.map_comp] at this
    exact (cancel_mono _).1 this
  have hnat : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A : BigFppfOver B S hS}
      (f : yoneda.obj A ⟶ F) {V V' : BigFppfOver B S hS} (r : V' ⟶ V) (v : V ⟶ A),
      f.app (op V') (r ≫ v) = F.map r.op (f.app (op V) v) := fun f _ _ r v =>
    hom_naturality_apply f r.op v
  refine ⟨E, e ≫ p₂, e ≫ p₁, ?_, pb_mk ?_ ?_ ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [hnat, hnat]; exact hab.symm
  · intro V a b hv
    let r : V ⟶ W := pullback.lift b a (Over.mkIdTerminal.hom_ext _ _)
    have hr₁ : r ≫ p₁ = b := pullback.lift_fst _ _ _
    have hr₂ : r ≫ p₂ = a := pullback.lift_snd _ _ _
    obtain ⟨l, hl⟩ := heq r (by
      rw [← hnat, ← hnat, hr₁, hr₂]; exact hv.symm)
    exact ⟨l, by rw [← Category.assoc, hl, hr₂], by rw [← Category.assoc, hl, hr₁]⟩
  · intro V l l' h₂ h₁
    refine (cancel_mono e).1 (pullback.hom_ext ?_ ?_)
    · simpa [p₁] using h₁
    · simpa [p₂] using h₂

end Exists

section Image

/-- The image, as a subfunctor. -/
noncomputable abbrev imS {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Subfunctor G :=
  Space.schemeTheoreticImageSubfunctor B S hS f

variable {T W : BigFppfOver B S hS}

/-- A function vanishing on `W` vanishes on the scheme-theoretic image of `W → T`. -/
lemma kills_of_mem_image [IsAffine ((SCH).obj T)] (w : W ⟶ T) (a : RT T) (ha : ((SCH).map w).appTop.hom a = 0)
    {V : BigFppfOver B S hS} (τ : V ⟶ T) (hτ : τ ∈ (imS (yoneda.map w)).obj (op V)) :
    ((SCH).map τ).appTop.hom a = 0 := by
  let I : Ideal (RT T) := Ideal.span {a}
  haveI : Algebra.FiniteType (RT T) (RT T ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ I) Ideal.Quotient.mk_surjective
  have hC : B.Contains (Spec (.of (RT T ⧸ I))) := contains_ft (RT T) _ (contains_RT T)
  let i : spObj T (Ideal.Quotient.mk I) hC ⟶ T := spToT T _ hC
  have hcl : IsClosedImmersion ((SCH).map i) := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      ((SCH).obj T).isoSpec.inv)
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hle : Subfunctor.range (yoneda.map w) ≤ Subfunctor.range (yoneda.map i) := by
    have hker : I ≤ RingHom.ker ((SCH).map w).appTop.hom := by
      rw [Ideal.span_le]
      rintro _ rfl
      exact ha
    let ψ := Ideal.Quotient.lift I ((SCH).map w).appTop.hom hker
    let l : W ⟶ spObj T (Ideal.Quotient.mk I) hC := spLift T (Ideal.Quotient.mk I) hC w ψ
      (RingHom.ext fun x => Ideal.Quotient.lift_mk I ((SCH).map w).appTop.hom hker)
    have hl : l ≫ i = w := spLift_toT T (Ideal.Quotient.mk I) hC w ψ _
    rintro V _ ⟨(x : V.unop ⟶ W), rfl⟩
    exact ⟨x ≫ l, by simp [hl]⟩
  obtain ⟨(x : V ⟶ _), hx⟩ := Space.schemeTheoreticImageSubfunctor_le B S hS (yoneda.map w)
    (Space.isClosedSubspace_range_yoneda_map B S hS i hcl) hle (op V) hτ
  have hx' : x ≫ i = τ := hx
  rw [← hx', Functor.map_comp, Scheme.Hom.comp_appTop]
  change ((SCH).map x).appTop.hom (((SCH).map i).appTop.hom a) = 0
  have h0 : ((SCH).map i).appTop.hom a = 0 := by
    rw [spToT_appTop]
    have : Ideal.Quotient.mk I a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)
    rw [this, map_zero]
  rw [h0, map_zero]

/-- The scheme-theoretic image of `W → T` is a closed subscheme `C → T`, with kernel that of
`Γ(T) → Γ(W)`. -/
theorem exists_closed_image [IsAffine ((SCH).obj T)] (w : W ⟶ T) :
    ∃ (C : BigFppfOver B S hS) (c : C ⟶ T), IsClosedImmersion ((SCH).map c) ∧
      Subfunctor.range (yoneda.map c) = imS (yoneda.map w) ∧
      RingHom.ker ((SCH).map c).appTop.hom = RingHom.ker ((SCH).map w).appTop.hom := by
  have hcl := Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (yoneda.map w)
    (isAlgebraicSpace_yoneda B S hS T)
  have hι := hcl.2
  let Y := imS (yoneda.map w)
  let g : yoneda.obj T ⟶ yoneda.obj T := 𝟙 _
  let C := hι.rep.pullback g
  let c : C ⟶ T := hι.rep.snd g
  have sq : IsPullback (hι.rep.fst g) (yoneda.map c) Y.ι g := hι.rep.isPullback g
  have hc : IsClosedImmersion ((SCH).map c) := hι.property_snd g
  have hrange : Subfunctor.range (yoneda.map c) = Y := by
    apply le_antisymm
    · rintro V _ ⟨(x : V.unop ⟶ C), rfl⟩
      have e : Y.ι.app V ((hι.rep.fst g).app V x) = (yoneda.map c).app V x :=
        congrArg (fun k => k.app V x) sq.w
      rw [← e]
      exact ((hι.rep.fst g).app V x).2
    · intro V y hy
      let a : yoneda.obj V.unop ⟶ Y.toFunctor := yonedaEquiv.symm ⟨y, hy⟩
      have hcomm : a ≫ Y.ι = yoneda.map y ≫ g := by
        apply yonedaEquiv.injective
        simp [a, g, yonedaEquiv]
        rfl
      obtain ⟨l, hl⟩ := Functor.Full.map_surjective (F := yoneda) (sq.lift a (yoneda.map y) hcomm)
      refine ⟨l, ?_⟩
      have : yoneda.map (l ≫ c) = yoneda.map y := by
        rw [Functor.map_comp, hl]; exact sq.lift_snd _ _ _
      exact Functor.Faithful.map_injective (F := yoneda) this
  have hcY : c ∈ Y.obj (op C) := by
    rw [← hrange]; exact ⟨𝟙 C, by simp⟩
  have hwY : w ∈ Y.obj (op W) :=
    Space.range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map w) (op W) ⟨𝟙 W, by simp⟩
  rw [← hrange] at hwY
  obtain ⟨(w' : W ⟶ C), hw'⟩ := hwY
  have hw'' : w' ≫ c = w := hw'
  refine ⟨C, c, hc, hrange, le_antisymm ?_ ?_⟩
  · intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [← hw'', Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map w').appTop.hom (((SCH).map c).appTop.hom a) = 0
    rw [ha, map_zero]
  · intro a ha
    exact kills_of_mem_image w a ha c hcY

end Image

section Orbit

variable [IsAffine S] {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] {N : AddSubgroup M} [AddMonoid.FG N]

/-- `O → X` is an affine morphism, hence quasi-compact. -/
lemma isQuasiCompact_orbit (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    (o : yoneda.obj (Ob P N) ⟶ X) : Space.IsQuasiCompact B S hS o := by
  refine Space.isQuasiCompact_of_isAffineHom' B S hS o (isAlgebraicSpace_yoneda B S hS _) hX ?_
  intro Z g
  haveI : IsAffine ((SCH).obj ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  obtain ⟨E, e₂, e₁, he, sq⟩ := exists_pull hsep o g
  have hE : IsAffine ((SCH).obj E) := isAffine_of_isAffineHom ((SCH).map e₁)
  exact ⟨⟨E, hE⟩, yoneda.map e₂, e₁, sq⟩

variable {o : yoneda.obj (Ob P N) ⟶ X}

/-- **Stacks 082Z(3)**, for an étale chart: the image pulls back to the image. -/
lemma preimage_image_chart (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    {T W : BigFppfOver B S hS} {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) :
    (imS o).preimage g = imS (yoneda.map w) := by
  have hbc := Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
    B S hS o g (isAlgebraicSpace_yoneda B S hS _) hX (isAlgebraicSpace_yoneda B S hS _)
    (isQuasiCompact_orbit hX hsep o) (Space.isEtale_of_presheafEtale B S hS g hg)
  rw [← hbc]
  refine Space.schemeTheoreticImageSubfunctor_congr_range B S hS _ _
    (isAlgebraicSpace_yoneda B S hS _) ?_
  have e : sq.isoPullback.hom ≫ pullback.snd o g = yoneda.map w := sq.isoPullback_hom_snd
  have e' : sq.isoPullback.inv ≫ yoneda.map w = pullback.snd o g := by
    rw [Iso.inv_comp_eq]; exact e.symm
  apply le_antisymm
  · rintro V _ ⟨x, rfl⟩
    exact ⟨sq.isoPullback.inv.app V x, congrArg (fun k => k.app V x) e'⟩
  · rintro V _ ⟨x, rfl⟩
    exact ⟨sq.isoPullback.hom.app V x, congrArg (fun k => k.app V x) e⟩

/-- A point of an étale chart lying in the image kills the kernel of `Γ(T) → Γ(O_T)`. -/
lemma chart_kills (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g)
    {V : BigFppfOver B S hS} (τ : V ⟶ T) (hτ : g.app (op V) τ ∈ (imS o).obj (op V)) (a : RT T)
    (ha : ((SCH).map w).appTop.hom a = 0) : ((SCH).map τ).appTop.hom a = 0 := by
  have : τ ∈ (imS (yoneda.map w)).obj (op V) := by
    rw [← preimage_image_chart hX hsep hg sq]
    exact hτ
  exact kills_of_mem_image w a ha τ this

/-- A point of an étale chart killing the kernel lies in the image. -/
lemma chart_mem (hX : IsAlgebraicSpace B S hS X) (hsep : AlgMag.IsSeparatedOver X)
    {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)] {g : yoneda.obj T ⟶ X}
    (hg : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) g)
    {p : W ⟶ Ob P N} {w : W ⟶ T} (sq : IsPullback (yoneda.map p) (yoneda.map w) o g)
    {V : BigFppfOver B S hS} (τ : V ⟶ T)
    (h : ∀ a : RT T, ((SCH).map w).appTop.hom a = 0 → ((SCH).map τ).appTop.hom a = 0) :
    g.app (op V) τ ∈ (imS o).obj (op V) := by
  obtain ⟨C, c, hc, hr, hk⟩ := exists_closed_image w
  have hCa : IsAffine ((SCH).obj C) := isAffine_of_isAffineHom ((SCH).map c)
  have hsurj : Function.Surjective ((SCH).map c).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map c)).2
  have hker : RingHom.ker ((SCH).map c).appTop.hom ≤ RingHom.ker ((SCH).map τ).appTop.hom := by
    rw [hk]; exact fun a ha => h a ha
  obtain ⟨φ, hφ⟩ := exists_ringHom_lift _ hsurj ((SCH).map τ).appTop.hom hker
  have hfacS : toAffine (T := (SCH).obj V) (U := (SCH).obj C) φ ≫ (SCH).map c = (SCH).map τ := by
    refine toAffine_ext ?_
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
    exact hφ
  let l : V ⟶ C := siteHom (toAffine (T := (SCH).obj V) (U := (SCH).obj C) φ) (by
    rw [← site_w c, ← Category.assoc, hfacS, site_w])
  have hl : l ≫ c = τ := site_hom_ext (by rw [Functor.map_comp]; exact hfacS)
  have : τ ∈ (imS (yoneda.map w)).obj (op V) := by
    rw [← hr]; exact ⟨l, hl⟩
  rw [← preimage_image_chart hX hsep hg sq] at this
  exact this

end Orbit

end AlgMag.ChartPoint
