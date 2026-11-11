/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartOrbit
import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid

/-!
# A thickening of an affine is affine (Stacks 05ZR, the case used in §2)

`SZ.*` is `StacksFrontier/RingTheory/Descent/SquareZeroGroupoid` and its closure (14 modules),
compiled under a prefix outside the Stacks build.

* `AlgMag.ChartMain.exists_affine_of_chart_pushout`: an algebraic space with an affine chart whose
  relation is the Čech groupoid of a faithfully flat ring map is affine, over an affine base.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma isPullback_of_appTop_pushout {P X Y T : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y]
    [IsAffine T] {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ T} {g : Y ⟶ T}
    (H : IsPushout f.appTop g.appTop p.appTop q.appTop) : IsPullback p q f g :=
  (H.op.flip.map Scheme.Spec).of_iso P.isoSpec.symm X.isoSpec.symm
    Y.isoSpec.symm T.isoSpec.symm (Scheme.isoSpec_inv_naturality p)
    (Scheme.isoSpec_inv_naturality q) (Scheme.isoSpec_inv_naturality f)
    (Scheme.isoSpec_inv_naturality g)

/-- A flat surjective morphism of affine schemes, as an fpqc family with one member. -/
lemma ofArrows_unit_mem_fpqc {Z T : Scheme.{u}} [IsAffine T] [IsAffine Z] (q : Z ⟶ T) [Flat q]
    [Surjective q] :
    Presieve.ofArrows (fun _ : Unit => Z) (fun _ => q) ∈ Scheme.fpqcPrecoverage T := by
  have hcov : ∀ x : T, ∃ i : Unit, x ∈ Set.range q := fun x => ⟨(), q.surjective x⟩
  let 𝒰 : T.Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers Unit (fun _ => Z) (fun _ => q) hcov (fun _ => inferInstance)
  have := Scheme.jointlySurjective_precoverage_flat
  have hfin : Finite 𝒰.I₀ := inferInstanceAs (Finite Unit)
  have hc : ∀ i, QuasiCompact (𝒰.f i) := fun _ => inferInstanceAs (QuasiCompact q)
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
    (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, fun _ => inferInstance⟩⟩

/-- Sheaf gluing along one fpqc morphism. -/
theorem exists_desc_fpqc (hX : IsAlgebraicSpace B S hS W)
    {V T : BigFppfOver B S hS} (q : V ⟶ T)
    (hcov : Presieve.ofArrows (fun _ : Unit => (SCH).obj V) (fun _ => (SCH).map q) ∈
      Scheme.fpqcPrecoverage ((SCH).obj T))
    (x : yoneda.obj V ⟶ W)
    (hx : ∀ ⦃Z : BigFppfOver B S hS⦄ (g₁ g₂ : Z ⟶ V), g₁ ≫ q = g₂ ≫ q →
      yoneda.map g₁ ≫ x = yoneda.map g₂ ≫ x) :
    ∃ φ : yoneda.obj T ⟶ W, yoneda.map q ≫ φ = x := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have hR : Presieve.ofArrows (fun _ : Unit => V) (fun _ => q) ∈
      Scheme.fpqcPrecoverage.comap (SCH) T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hcov
  have hF := (Presieve.isSheafFor_arrows_iff W (fun _ : Unit => q)).1 (hsh _ hR)
  obtain ⟨t, ht, -⟩ := hF (fun _ => yonedaEquiv x) (by
    intro i j Z g₁ g₂ h
    have e := congrArg yonedaEquiv (hx g₁ g₂ h)
    exact (yonedaEquiv_naturality x g₁).trans (e.trans (yonedaEquiv_naturality x g₂).symm))
  refine ⟨yonedaEquiv.symm t, ?_⟩
  apply yonedaEquiv.injective
  have e := yonedaEquiv_naturality (yonedaEquiv.symm t) q
  rw [Equiv.apply_symm_apply] at e
  exact e.symm.trans (ht ())

/-- **Stacks 05ZR, last step**: over an affine base, an algebraic space with an affine surjective
étale chart whose relation is the Čech groupoid of a faithfully flat ring map `α` is affine. -/
theorem exists_affine_of_chart_pushout [IsAffine S] (hW : IsAlgebraicSpace B S hS W)
    {V R : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ W) (t s : R ⟶ V)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) φ φ)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ)
    [IsAffine ((SCH).obj V)] [IsAffine ((SCH).obj R)]
    (A : CommRingCat.{u}) (α : A ⟶ Γ((SCH).obj V, ⊤)) (hff : α.hom.FaithfullyFlat)
    (hpush : IsPushout α α ((SCH).map t).appTop ((SCH).map s).appTop)
    (hrange : ∀ b : Γ((SCH).obj V, ⊤), ((SCH).map t).appTop.hom b = ((SCH).map s).appTop.hom b →
      b ∈ Set.range α.hom) :
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj T)), Nonempty (yoneda.obj T ≅ W) := by
  have hinj : Function.Injective α.hom := hff.injective
  have hA : B.Contains (Spec A) :=
    Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hinj V.left.2
  -- the structure map
  let ρ : Γ(S, ⊤) →+* Γ((SCH).obj V, ⊤) := (V.hom.hom).appTop.hom
  have hρ : ∀ r, ρ r ∈ α.hom.range := fun r => by
    have hts : ∀ f : R ⟶ V, ((SCH).map f).appTop.hom (ρ r) = (R.hom.hom).appTop.hom r := fun f => by
      have e : (SCH).map f ≫ V.hom.hom = R.hom.hom := congrArg (fun m => m.hom) (Over.w f)
      rw [← e, Scheme.Hom.comp_appTop]; rfl
    obtain ⟨a, ha⟩ := hrange (ρ r) ((hts t).trans (hts s).symm)
    exact ⟨a, ha⟩
  let eA : A ≃+* α.hom.range := RingEquiv.ofBijective α.hom.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), α.hom.rangeRestrict_surjective⟩
  let σ : Γ(S, ⊤) →+* A := eA.symm.toRingHom.comp (ρ.codRestrict α.hom.range hρ)
  have hσ : α.hom.comp σ = ρ := by
    ext r
    have := eA.apply_symm_apply (ρ.codRestrict α.hom.range hρ r)
    exact congrArg Subtype.val this
  let qA : Spec A ⟶ S := toAffine (T := Spec A) (U := S) ((Scheme.ΓSpecIso A).inv.hom.comp σ)
  let SA : BigFppfOver B S hS := Over.mk (⟨qA⟩ : B.obj hA ⟶ B.obj hS)
  have hSA : IsAffine ((SCH).obj SA) := inferInstanceAs (IsAffine (Spec A))
  let a0 : (SCH).obj V ⟶ Spec A := ((SCH).obj V).toSpecΓ ≫ Spec.map α
  have ha0 : a0.appTop = (Scheme.ΓSpecIso A).hom ≫ α := by
    show (((SCH).obj V).toSpecΓ ≫ Spec.map α).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have hq : a0 ≫ qA = V.hom.hom := by
    refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun r => ?_))
    have h1 : qA.appTop.hom r = (Scheme.ΓSpecIso A).inv.hom (σ r) := by
      simp only [qA, toAffine_appTop]; rfl
    rw [Scheme.Hom.comp_appTop]
    change a0.appTop.hom (qA.appTop.hom r) = ρ r
    rw [h1, ha0, ← hσ]
    change α.hom ((Scheme.ΓSpecIso A).hom.hom ((Scheme.ΓSpecIso A).inv.hom (σ r))) = α.hom (σ r)
    congr 1
    exact (Scheme.ΓSpecIso A).inv_hom_id_apply _
  let a : V ⟶ SA := Over.homMk ⟨a0⟩ (InducedCategory.hom_ext hq)
  have hGa : (SCH).map a = a0 := rfl
  have hpush' : IsPushout a0.appTop a0.appTop ((SCH).map t).appTop ((SCH).map s).appTop := by
    rw [ha0]
    exact hpush.of_iso (Scheme.ΓSpecIso A).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hpb : IsPullback ((SCH).map t) ((SCH).map s) a0 a0 := isPullback_of_appTop_pushout hpush'
  have hsa : s ≫ a = t ≫ a := siteExt (by
    rw [Functor.map_comp, Functor.map_comp, hGa]; exact hpb.w.symm)
  obtain ⟨hfl, hsu⟩ : Flat a0 ∧ Surjective a0 := by
    obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff α).2 hff
    exact ⟨inferInstanceAs (Flat (((SCH).obj V).toSpecΓ ≫ Spec.map α)),
      inferInstanceAs (Surjective (((SCH).obj V).toSpecΓ ≫ Spec.map α))⟩
  have hcov : Presieve.ofArrows (fun _ : Unit => (SCH).obj V) (fun _ => (SCH).map a) ∈
      Scheme.fpqcPrecoverage ((SCH).obj SA) := ofArrows_unit_mem_fpqc (T := Spec A) a0
  obtain ⟨h, hh⟩ := exists_desc_fpqc hW a hcov φ (by
    intro Z g₁ g₂ e
    have e' : (SCH).map g₁ ≫ a0 = (SCH).map g₂ ≫ a0 := by
      rw [← hGa, ← Functor.map_comp, ← Functor.map_comp, e]
    let l0 := hpb.lift _ _ e'
    have h1 : l0 ≫ (SCH).map t = (SCH).map g₁ := hpb.lift_fst _ _ _
    have h2 : l0 ≫ (SCH).map s = (SCH).map g₂ := hpb.lift_snd _ _ _
    let l : Z ⟶ R := Over.homMk ⟨l0⟩ (InducedCategory.hom_ext (by
      have e1 : (SCH).map t ≫ V.hom.hom = R.hom.hom := congrArg (fun m => m.hom) (Over.w t)
      have e2 : (SCH).map g₁ ≫ V.hom.hom = Z.hom.hom := congrArg (fun m => m.hom) (Over.w g₁)
      change l0 ≫ R.hom.hom = Z.hom.hom
      rw [← e1, ← Category.assoc, h1, e2]))
    have l1 : l ≫ t = g₁ := siteExt (by rw [Functor.map_comp]; exact h1)
    have l2 : l ≫ s = g₂ := siteExt (by rw [Functor.map_comp]; exact h2)
    rw [← l1, ← l2, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hR.w])
  obtain ⟨hRsh, hUsh, ⟨hc⟩⟩ := Space.isCoequalizer_of_surjectiveEtale B S hS φ t s hR hW hsurj het
  let J := BigFppfOver.topology B S hS
  have hSAsh : Presheaf.IsSheaf J (yoneda.obj SA) := BigFppfOver.isSheaf_yoneda_obj B S hS SA
  let GS : Sheaf J (Type u) := ⟨yoneda.obj SA, hSAsh⟩
  let k : (⟨yoneda.obj V, hUsh⟩ : Sheaf J (Type u)) ⟶ GS := ⟨yoneda.map a⟩
  have hk : (⟨yoneda.map t⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj V, hUsh⟩) ≫ k =
      (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj V, hUsh⟩) ≫ k := by
    apply Sheaf.hom_ext
    show yoneda.map t ≫ yoneda.map a = yoneda.map s ≫ yoneda.map a
    rw [← Functor.map_comp, ← Functor.map_comp, hsa]
  let g : W ⟶ yoneda.obj SA := (hc.desc (Cofork.ofπ k hk)).hom
  have hg : φ ≫ g = yoneda.map a :=
    congrArg (fun m => m.hom) (hc.fac (Cofork.ofπ k hk) WalkingParallelPair.one)
  have hgh : g ≫ h = 𝟙 W := by
    let WF : Sheaf J (Type u) := ⟨W, hW.isSheaf⟩
    have := Cofork.IsColimit.hom_ext hc (W := WF) (k := (⟨g ≫ h⟩ : WF ⟶ WF)) (l := (⟨𝟙 W⟩ : WF ⟶ WF))
      (Sheaf.hom_ext (by
        show φ ≫ g ≫ h = φ ≫ 𝟙 W
        rw [← Category.assoc, hg, hh, Category.comp_id]))
    exact congrArg (fun m => m.hom) this
  have hhg : h ≫ g = 𝟙 _ := by
    have e : yoneda.map a ≫ h ≫ g = yoneda.map a := by
      rw [← Category.assoc, hh, hg]
    obtain ⟨m, hm⟩ := yoneda.map_surjective (h ≫ g)
    rw [← hm, ← Functor.map_comp] at e
    have e2 : a ≫ m = a := yoneda.map_injective e
    have : m = 𝟙 _ := by
      apply siteExt
      refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      apply (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.injective
      apply hinj
      have e3 := congrArg (fun z => ((SCH).map z).appTop.hom x) e2
      simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at e3
      rw [hGa, ha0] at e3
      simp at e3 ⊢
      exact e3
    rw [← hm, this, yoneda.map_id]
  exact ⟨SA, hSA, ⟨⟨h, g, hhg, hgh⟩⟩⟩

lemma exists_ringEquiv_tensor {R C D T : Type u} [CommRing R] [CommRing C]
    [CommRing D] [CommRing T] [Algebra R C] [Algebra R D] (pC : C →+* T) (pD : D →+* T)
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R D))
      (CommRingCat.ofHom pC) (CommRingCat.ofHom pD)) :
    ∃ e : T ≃+* C ⊗[R] D, (∀ c, e (pC c) = c ⊗ₜ 1) ∧ (∀ d, e (pD d) = 1 ⊗ₜ d) := by
  have ht := CommRingCat.isPushout_tensorProduct R C D
  exact ⟨(hpush.isoIsPushout _ _ ht).commRingCatIsoToRingEquiv,
    fun c => congrArg (fun f => f.hom c) (hpush.inl_isoIsPushout_hom _ _ ht),
    fun d => congrArg (fun f => f.hom d) (hpush.inr_isoIsPushout_hom _ _ ht)⟩

/-- A type synonym carrying a second algebra structure. -/
def SecondRing (C : Type u) : Type u := C

instance (C : Type u) [CommRing C] : CommRing (SecondRing C) := ‹CommRing C›

section Groupoid

open Module.Descent.SquareZero

variable {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ W}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

local notation "Rel" => Space.atlasRelation B S hS hs
local notation "tgt" => Space.atlasRelationTarget B S hS hs
local notation "src" => Space.atlasRelationSource B S hS hs

lemma rel_w : yoneda.map (tgt) ≫ φ = yoneda.map (src) ≫ φ := by simpa using hs.rep.w φ

/-- The diagonal `V ⟶ V ×_W V`. -/
noncomputable def relDiag : V ⟶ Rel := hs.rep.lift' (𝟙 V) (𝟙 V) rfl

lemma relDiag_tgt : relDiag hs ≫ tgt = 𝟙 V := hs.rep.lift'_fst _ _ _
lemma relDiag_src : relDiag hs ≫ src = 𝟙 V := hs.rep.lift'_snd _ _ _

/-- Composition on the relation. -/
noncomputable def relComp : pullback (src) (tgt) ⟶ Rel :=
  hs.rep.lift' (pullback.fst _ _ ≫ tgt) (pullback.snd _ _ ≫ src) (by
    have hw := rel_w hs
    rw [Functor.map_comp, Category.assoc, hw, ← Category.assoc, ← Functor.map_comp,
      pullback.condition, Functor.map_comp, Category.assoc, hw, ← Category.assoc,
      ← Functor.map_comp, Functor.map_comp, Category.assoc])

lemma relComp_tgt : relComp hs ≫ tgt = pullback.fst _ _ ≫ tgt := hs.rep.lift'_fst _ _ _
lemma relComp_src : relComp hs ≫ src = pullback.snd _ _ ≫ src := hs.rep.lift'_snd _ _ _

/-- **Stacks 05ZR for finite-order thickenings, the ring step**: the chart groupoid of `W`
is effective when its reduction modulo a nilpotent invariant ideal is. -/
theorem isEffective_chart [IsAffine ((SCH).obj V)] [IsAffine ((SCH).obj Rel)]
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (K : Ideal Γ((SCH).obj V, ⊤)) {n : ℕ} (hn : K ^ n = ⊥) :
    letI := ((SCH).map (src)).appTop.hom.toAlgebra
    ∀ (hK : K.map ((SCH).map (tgt)).appTop.hom = extJ Γ((SCH).obj Rel, ⊤) K),
      IsEffective (s₀ ((SCH).map (tgt)).appTop.hom K hK) →
      IsEffective ((SCH).map (tgt)).appTop.hom := by
  let G := SCH
  let tg := (G.map (tgt)).appTop.hom
  let sc := (G.map (src)).appTop.hom
  let _ : Algebra Γ(G.obj V, ⊤) Γ(G.obj (Rel), ⊤) := sc.toAlgebra
  intro hK h₀
  have hetS : Etale (G.map (src)) := he.property φ (hs.rep.fst φ) (hs.rep.snd φ) (hs.rep.isPullback φ)
  have : Module.Flat Γ(G.obj V, ⊤) Γ(G.obj (Rel), ⊤) := (G.map (src)).flat_appTop
  let _ : Algebra Γ(G.obj V, ⊤) (SecondRing Γ(G.obj (Rel), ⊤)) := tg.toAlgebra
  let σ : Γ(G.obj (Rel), ⊤) ≃+* SecondRing Γ(G.obj (Rel), ⊤) := RingEquiv.refl _
  let e := (G.map (relDiag hs)).appTop.hom
  have hcomp : ∀ {X Y T : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ T) {c : X ⟶ T},
      a ≫ b = c → ∀ x, (G.map a).appTop.hom ((G.map b).appTop.hom x) = (G.map c).appTop.hom x := by
    rintro - - - a b - rfl x
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have hes : ∀ b, e (tg b) = b := fun b => (hcomp _ _ (relDiag_tgt hs) b).trans (by simp)
  have het : ∀ b, e (sc b) = b := fun b => (hcomp _ _ (relDiag_src hs) b).trans (by simp)
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hP : IsPullback (G.map (pullback.fst (src) (tgt))) (G.map (pullback.snd (src) (tgt)))
      (G.map (src)) (G.map (tgt)) := (IsPullback.of_hasPullback _ _).map _
  have : IsAffine (G.obj (pullback (src) (tgt))) := by
    have h1 : IsAffineHom (G.map (tgt)) := isAffineHom_of_isAffine _
    have h2 : IsAffineHom (G.map (pullback.fst (src) (tgt))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip h1
    exact isAffine_of_isAffineHom (G.map (pullback.fst (src) (tgt)))
  have hpush : IsPushout (G.map (src)).appTop (G.map (tgt)).appTop
      (G.map (pullback.fst (src) (tgt))).appTop (G.map (pullback.snd (src) (tgt))).appTop :=
    isPushout_appTop_of_isPullback hP
  obtain ⟨eQ, heQl, heQr⟩ := exists_ringEquiv_tensor (R := Γ(G.obj V, ⊤))
    (C := Γ(G.obj (Rel), ⊤)) (D := SecondRing Γ(G.obj (Rel), ⊤))
    (G.map (pullback.fst (src) (tgt))).appTop.hom (G.map (pullback.snd (src) (tgt))).appTop.hom hpush
  let m := eQ.toRingHom.comp (G.map (relComp hs)).appTop.hom
  have hms : ∀ b, m (tg b) = tg b ⊗ₜ 1 := fun b =>
    (congrArg eQ ((hcomp _ _ (relComp_tgt hs) b).trans
      (hcomp (pullback.fst _ _) _ rfl b).symm)).trans (heQl _)
  have hmt : ∀ b, m (sc b) = 1 ⊗ₜ σ (sc b) := fun b =>
    (congrArg eQ ((hcomp _ _ (relComp_src hs) b).trans
      (hcomp (pullback.snd _ _) _ rfl b).symm)).trans (heQr _)
  exact isEffective_of_pow_eq_bot tg σ (fun _ => rfl) e hes het m hms hmt K hK hn h₀

end Groupoid

section RingStep

open Module.Descent.SquareZero

/-- The reduced groupoid is effective when it is, up to isomorphism, the Čech groupoid of a
faithfully flat ring map (the case of an affine closed subspace in Stacks 05ZR). -/
theorem isEffective_s₀_of_model {B C B0 C0 A : Type u} [CommRing B] [CommRing C] [Algebra B C]
    [CommRing B0] [CommRing C0] [CommRing A] [Algebra A B0] [Module.FaithfullyFlat A B0]
    (tg : B →+* C) (K : Ideal B) (hK : K.map tg = extJ C K)
    (πB : B →+* B0) (hπB : Function.Surjective πB) (hkB : RingHom.ker πB = K)
    (πC : C →+* C0) (hπC : Function.Surjective πC) (hkC : RingHom.ker πC = extJ C K)
    (p q : B0 →+* C0) (hp : ∀ b, p (πB b) = πC (tg b)) (hq : ∀ b, q (πB b) = πC (algebraMap B C b))
    (hpush : IsPushout (CommRingCat.ofHom (algebraMap A B0)) (CommRingCat.ofHom (algebraMap A B0))
      (CommRingCat.ofHom q) (CommRingCat.ofHom p)) :
    IsEffective (s₀ tg K hK) := by
  let eB : (B ⧸ K) ≃+* B0 := (Ideal.quotEquivOfEq hkB.symm).trans
    (RingHom.quotientKerEquivOfSurjective hπB)
  let eC : (C ⧸ extJ C K) ≃+* C0 := (Ideal.quotEquivOfEq hkC.symm).trans
    (RingHom.quotientKerEquivOfSurjective hπC)
  have heB : ∀ b, eB (Ideal.Quotient.mk K b) = πB b := fun _ => rfl
  have heC : ∀ c, eC (Ideal.Quotient.mk _ c) = πC c := fun _ => rfl
  let _ : Algebra A (B ⧸ K) := (eB.symm.toRingHom.comp (algebraMap A B0)).toAlgebra
  let eBA : (B ⧸ K) ≃ₐ[A] B0 :=
    { eB with commutes' := fun a => eB.apply_symm_apply _ }
  have : Module.FaithfullyFlat A (B ⧸ K) := Module.FaithfullyFlat.of_linearEquiv A B0 eBA.toLinearEquiv
  have ht : ∀ x, eC (algebraMap (B ⧸ K) (C ⧸ extJ C K) x) = q (eB x) := fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [t₀_mk, heC, heB, hq]
  have hsb : ∀ x, eC (s₀ tg K hK x) = p (eB x) := fun x => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [s₀_mk, heC, heB, hp]
  have hpq : ∀ a, p (algebraMap A B0 a) = q (algebraMap A B0 a) := fun a =>
    (congrArg (fun f => f.hom a) hpush.w).symm
  have h : ∀ a : A, s₀ tg K hK (algebraMap A (B ⧸ K) a) =
      algebraMap (B ⧸ K) (C ⧸ extJ C K) (algebraMap A (B ⧸ K) a) := fun a => by
    apply eC.injective
    rw [hsb, ht]
    have e : eB (algebraMap A (B ⧸ K) a) = algebraMap A B0 a := eB.apply_symm_apply _
    rw [e, hpq]
  refine ⟨A, inferInstance, inferInstance, h, inferInstance, ?_⟩
  obtain ⟨e, he1, he2⟩ := exists_ringEquiv_tensor (R := A) (C := B0) (D := B0) q p hpush
  let cg := (Algebra.TensorProduct.congr eBA eBA)
  have key : ∀ z, e (eC (cmp (s₀ tg K hK) A h z)) = cg z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [cmp_tmul, map_mul, map_mul, ht, hsb, he1, he2]
      simp [cg, eBA]
  have hc : Function.Bijective (fun z => e (eC (cmp (s₀ tg K hK) A h z))) := by
    have : (fun z => e (eC (cmp (s₀ tg K hK) A h z))) = cg := funext key
    rw [this]; exact cg.bijective
  exact (Function.Bijective.of_comp_iff' (e.bijective.comp eC.bijective) _).1 hc

end RingStep

section Assemble

open Module.Descent.SquareZero

lemma faithfullyFlat_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) [Flat f]
    [Surjective f] : f.appTop.hom.FaithfullyFlat := by
  have e : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have h1 : Flat (Spec.map f.appTop) := by rw [e]; infer_instance
  have h2 : Surjective (Spec.map f.appTop) := by rw [e]; infer_instance
  exact (flat_and_surjective_SpecMap_iff f.appTop).1 ⟨h1, h2⟩

variable {V O : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ W} {j : yoneda.obj O ⟶ W}
  (ho : ClosedP j)

/-- The base change square of `ho` along a composite. -/
lemma isPullback_snd_comp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (t : yoneda.obj T ⟶ W)
    (t' : yoneda.obj T' ⟶ W) (ht : t' = yoneda.map g ≫ t) :
    ∃ m : ho.rep.pullback t' ⟶ ho.rep.pullback t,
      IsPullback m (ho.rep.snd t') (ho.rep.snd t) g ∧
      yoneda.map m ≫ ho.rep.fst t = ho.rep.fst t' := by
  subst ht
  have s1 := ho.rep.isPullback t
  have s2 := ho.rep.isPullback (yoneda.map g ≫ t)
  have hc : (ho.rep.fst (yoneda.map g ≫ t)) ≫ j =
      yoneda.map (ho.rep.snd (yoneda.map g ≫ t) ≫ g) ≫ t := by
    rw [s2.w, Functor.map_comp, Category.assoc]
  let m := ho.rep.lift (ho.rep.fst (yoneda.map g ≫ t)) (ho.rep.snd (yoneda.map g ≫ t) ≫ g) hc
  have hm : m ≫ ho.rep.snd t = ho.rep.snd (yoneda.map g ≫ t) ≫ g := ho.rep.lift_snd _ _ _
  have hm' : yoneda.map m ≫ ho.rep.fst t = ho.rep.fst (yoneda.map g ≫ t) := ho.rep.lift_fst _ _ _
  refine ⟨m, IsPullback.of_map yoneda (by rw [hm]) ?_, hm'⟩
  refine IsPullback.of_right (h₁₂ := ho.rep.fst t) (v₁₃ := j) (h₂₂ := t) ?_ ?_ s1
  · rw [hm']; exact s2
  · rw [← Functor.map_comp, ← Functor.map_comp, hm]

lemma ker_map_of_isPullback {Z' X Z Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {i' : Z' ⟶ X}
    {m : Z' ⟶ Z} {f : X ⟶ Y} {i : Z ⟶ Y} [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback i' m f i) :
    RingHom.ker i'.appTop.hom = (RingHom.ker i.appTop.hom).map f.appTop.hom := by
  have h := IdealPow.ideal_comap_top_of_isAffine i.ker f
  rw [← ker_eq_comap_of_isPullback sq] at h
  simp only [Scheme.Hom.ker_apply] at h
  exact h

lemma isPushout_of_bij {A D F : Type u} [CommRing A] [CommRing D] [CommRing F] [Algebra A D]
    (σ τ : D →+* F) (hστ : σ.comp (algebraMap A D) = τ.comp (algebraMap A D))
    (hbij : Function.Bijective (Stacks.AffineStageCore.tensorLift σ τ hστ)) :
    IsPushout (CommRingCat.ofHom (algebraMap A D)) (CommRingCat.ofHom (algebraMap A D))
      (CommRingCat.ofHom σ) (CommRingCat.ofHom τ) := by
  refine (CommRingCat.isPushout_tensorProduct A D D).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (RingEquiv.ofBijective _ hbij).toCommRingCatIso (by simp) (by simp) ?_ ?_ <;>
    ext d <;> simp [Stacks.AffineStageCore.tensorLift_tmul]

/-- **Stacks 05ZR, finite order, affine closed subspace**: if `j : O → W` is a closed immersion with
`O` affine and the ideal of `O` on an affine chart of `W` (with affine relation) is nilpotent, then
`W` is affine. Over an affine base. -/
theorem exists_affine_of_nilpotent_chart [IsAffine S] (hW : IsAlgebraicSpace B S hS W)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    [IsAffine ((SCH).obj V)] [IsAffine ((SCH).obj (Space.atlasRelation B S hS hs))]
    [IsAffine ((SCH).obj O)] {n : ℕ}
    (hn : RingHom.ker ((SCH).map (ho.rep.snd φ)).appTop.hom ^ n = ⊥) :
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj T)), Nonempty (yoneda.obj T ≅ W) := by
  let G := SCH
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let tgt := Space.atlasRelationTarget B S hS hs
  let src := Space.atlasRelationSource B S hS hs
  let i := ho.rep.snd φ
  have hi : IsClosedImmersion (G.map i) := ho.property_snd φ
  have : IsAffine (G.obj (ho.rep.pullback φ)) := isAffine_of_isAffineHom (G.map i)
  let tR := yoneda.map src ≫ φ
  let i' := ho.rep.snd tR
  have hi' : IsClosedImmersion (G.map i') := ho.property_snd tR
  have : IsAffine (G.obj (ho.rep.pullback tR)) := isAffine_of_isAffineHom (G.map i')
  obtain ⟨q, hq, hq'⟩ := isPullback_snd_comp ho src φ tR rfl
  obtain ⟨p, hp, hp'⟩ := isPullback_snd_comp ho tgt φ tR (rel_w hs).symm
  let K := RingHom.ker (G.map i).appTop.hom
  have kq : RingHom.ker (G.map i').appTop.hom = K.map (G.map src).appTop.hom :=
    ker_map_of_isPullback ((hq.map G).flip)
  have kp : RingHom.ker (G.map i').appTop.hom = K.map (G.map tgt).appTop.hom :=
    ker_map_of_isPullback ((hp.map G).flip)
  let _ : Algebra Γ(G.obj V, ⊤) Γ(G.obj (Space.atlasRelation B S hS hs), ⊤) :=
    (G.map src).appTop.hom.toAlgebra
  have hK : K.map (G.map tgt).appTop.hom = extJ Γ(G.obj (Space.atlasRelation B S hS hs), ⊤) K :=
    kp.symm.trans kq
  obtain ⟨f, hf⟩ := yoneda.map_surjective (ho.rep.fst φ)
  have sq0 : IsPullback (yoneda.map i) (yoneda.map f) φ j := by
    rw [hf]; exact (ho.rep.isPullback φ).flip
  have hfe : Etale (G.map f) := he.property j (yoneda.map i) f sq0
  have hfs : Surjective (G.map f) := hs.property j (yoneda.map i) f sq0
  have hR : IsPullback (yoneda.map tgt) (yoneda.map src) φ φ := by
    have := hs.rep.isPullback φ
    simpa [tgt, src] using this
  have big := ((hq.map yoneda).flip.paste_horiz hR)
  have hcomm : yoneda.map p ≫ yoneda.map i = yoneda.map i' ≫ yoneda.map tgt := by
    rw [← Functor.map_comp, ← Functor.map_comp, hp.w]
  have big' : IsPullback (yoneda.map p ≫ yoneda.map i) (yoneda.map q) φ (yoneda.map f ≫ j) := by
    rw [hcomm, ← sq0.w]; exact big
  have hpqf : yoneda.map p ≫ yoneda.map f = yoneda.map q ≫ yoneda.map f := by
    rw [hf, hp', hq']
  have sqY : IsPullback (yoneda.map p) (yoneda.map q) (yoneda.map f) (yoneda.map f) :=
    IsPullback.of_right big' hpqf sq0
  have sqS : IsPullback (G.map p) (G.map q) (G.map f) (G.map f) :=
    (IsPullback.of_map yoneda (yoneda.map_injective (by simpa [Functor.map_comp] using hpqf)) sqY).map G
  have hpush := isPushout_appTop_of_isPullback sqS
  let _ : Algebra Γ(G.obj O, ⊤) Γ(G.obj (ho.rep.pullback φ), ⊤) := (G.map f).appTop.hom.toAlgebra
  have hFF : Module.FaithfullyFlat Γ(G.obj O, ⊤) Γ(G.obj (ho.rep.pullback φ), ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 (faithfullyFlat_appTop (G.map f))
  have hcp : ∀ {X Y T : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ T) (x),
      (G.map (a ≫ b)).appTop.hom x = (G.map a).appTop.hom ((G.map b).appTop.hom x) := by
    intro X Y T a b x
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have h₀ := isEffective_s₀_of_model (A := Γ(G.obj O, ⊤)) (G.map tgt).appTop.hom K hK
    (G.map i).appTop.hom (IsClosedImmersion.isAffine_surjective_of_isAffine (G.map i)).2 rfl
    (G.map i').appTop.hom (IsClosedImmersion.isAffine_surjective_of_isAffine (G.map i')).2 kq
    (G.map p).appTop.hom (G.map q).appTop.hom
    (fun b => by rw [← hcp, hp.w, hcp])
    (fun b => by rw [← hcp, hq.w, hcp]; rfl)
    (by exact hpush.flip)
  have heff := isEffective_chart hs he K hn hK h₀
  obtain ⟨A, _, _, h, hff, hbij⟩ := heff
  have hst : (G.map src).appTop.hom.comp (algebraMap A Γ(G.obj V, ⊤)) =
      (G.map tgt).appTop.hom.comp (algebraMap A Γ(G.obj V, ⊤)) := RingHom.ext fun a => (h a).symm
  refine exists_affine_of_chart_pushout hW φ src tgt hR.flip hs he (CommRingCat.of A)
    (CommRingCat.ofHom (algebraMap A _)) (RingHom.faithfullyFlat_algebraMap_iff.2 hff)
    (isPushout_of_bij _ _ hst ?_)
    (fun b hb => Module.Descent.SquareZero.mem_range_of_eq _ h hbij hb.symm)
  have hfun : (fun x => Stacks.AffineStageCore.tensorLift (G.map src).appTop.hom
      (G.map tgt).appTop.hom hst x) = (cmp (G.map tgt).appTop.hom A h) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  change Function.Bijective (fun x => Stacks.AffineStageCore.tensorLift (G.map src).appTop.hom
      (G.map tgt).appTop.hom hst x)
  rw [hfun]
  exact hbij

end Assemble

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.isEffective_chart
#print axioms AlgMag.ChartMain.exists_affine_of_chart_pushout
#print axioms AlgMag.ChartMain.exists_affine_of_nilpotent_chart
