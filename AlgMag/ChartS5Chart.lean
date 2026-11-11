/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartConclude
import AlgMag.ChartEtaleFlat
import AlgMag.ChartOrbit

/-!
# Artin approximation and shrinking: the piece `Spec S` of `W ×_X V`

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


* `exists_chartPiece`, `ChartPiece`: an affine open of `W ×_X V` at the point `(u₀, v)`, with its rings.
* `exists_etaleOn_of_isEtaleAt`: shrinking step, étale at the point gives `D(g₀) → X` étale.
* `eq_of_agree_on_closedPoint`: two lifts to an étale `V → X` agreeing at the closed point are equal.
* `etale_base_change_ideal`: the base change `Z ×_X V` of a closed `Z ⊆ X`, in rings.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartS5

open ChartConclude ChartEtale

/-! ### Schemes -/

lemma etale_of_forall_open' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) : Etale f := by
  choose U hx hU using h
  have top : iSup U = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
  exact (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Etale) U top).2 hU

lemma etale_comp_of_range' {A X Z : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] (O : X.Opens)
    (b : X ⟶ Z) (hj : Set.range j ⊆ O) (hO : Etale (O.ι ≫ b)) : Etale (j ≫ b) := by
  have hr : Set.range j ⊆ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hj
  have ht : IsOpenImmersion.lift O.ι j hr ≫ O.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : Etale (IsOpenImmersion.lift O.ι j hr ≫ O.ι) := by rw [ht]; infer_instance
  have : Etale (IsOpenImmersion.lift O.ι j hr) := Etale.of_comp _ O.ι
  rw [← ht, Category.assoc]; infer_instance

/-- **Étale descent of étaleness at a point**, over any base: the form over affine bases
`ChartEtale.exists_open_etale_of_isPullback_Spec`, applied on affine opens of `T` and `T'`. -/
theorem exists_open_etale_of_isPullback {P Y T' T : Scheme.{u}} {a : P ⟶ Y} {b : P ⟶ T'} {f : Y ⟶ T}
    {g : T' ⟶ T} [LocallyOfFinitePresentation f] [Etale g] (sq : IsPullback a b f g) (z : P)
    (O : P.Opens) (hz : z ∈ O) (hO : Etale (O.ι ≫ b)) :
    ∃ U : Y.Opens, a z ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨T₀, hT₀, htz, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f (a z)))
  have hgb : b z ∈ g ⁻¹ᵁ T₀ := by
    change g (b z) ∈ T₀
    rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]
    exact htz
  obtain ⟨T'₀, hT'₀, hbz, hle⟩ := exists_isAffineOpen_mem_and_subset hgb
  let j := hT₀.fromSpec
  let j' := hT'₀.fromSpec
  have hr : Set.range (j' ≫ g) ⊆ Set.range j := by
    rw [hT₀.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have h1 : j' x ∈ T'₀ := by
      have : j' x ∈ Set.range j' := ⟨x, rfl⟩
      rwa [hT'₀.range_fromSpec] at this
    have h2 := hle h1
    rw [Scheme.Hom.comp_apply]
    exact h2
  let l := IsOpenImmersion.lift j (j' ≫ g) hr
  have hl : l ≫ j = j' ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hlet : Etale l := by
    have : Etale (l ≫ j) := by rw [hl]; infer_instance
    exact Etale.of_comp l j
  let σ := Spec.preimage l
  have hσ : Spec.map σ = l := Spec.map_preimage _
  have hfl : Flat (Spec.map σ) := by rw [hσ]; infer_instance
  have pY : IsPullback (pullback.fst f j) (pullback.snd f j) f j := IsPullback.of_hasPullback _ _
  have pP : IsPullback (pullback.fst b j') (pullback.snd b j') b j' := IsPullback.of_hasPullback _ _
  let a₁ : pullback b j' ⟶ pullback f j := pullback.lift (pullback.fst b j' ≫ a)
    (pullback.snd b j' ≫ Spec.map σ) (by
      rw [Category.assoc, Category.assoc, sq.w, hσ, hl, ← Category.assoc, pP.w, Category.assoc])
  have outer := pP.paste_horiz sq
  have sq₁ : IsPullback a₁ (pullback.snd b j') (pullback.snd f j) (Spec.map σ) := by
    refine IsPullback.of_right ?_ ?_ pY
    · have e1 : a₁ ≫ pullback.fst f j = pullback.fst b j' ≫ a := pullback.lift_fst _ _ _
      have e2 : Spec.map σ ≫ j = j' ≫ g := by rw [hσ, hl]
      rw [e1, e2]; exact outer
    · exact pullback.lift_snd _ _ _
  obtain ⟨s, hs⟩ : ∃ s, j' s = b z := by
    have : b z ∈ Set.range j' := by rw [hT'₀.range_fromSpec]; exact hbz
    exact this
  obtain ⟨z₁, hz₁, -⟩ := exists_pt_of_isPullback pP z s hs.symm
  let O₁ := (pullback.fst b j') ⁻¹ᵁ O
  have hO₁ : Etale (O₁.ι ≫ pullback.snd b j') := by
    have h1 : Etale ((O₁.ι ≫ pullback.fst b j') ≫ b) := by
      refine etale_comp_of_range' _ O b ?_ hO
      rintro _ ⟨x, rfl⟩
      exact x.2
    have h2 : Etale ((O₁.ι ≫ pullback.snd b j') ≫ j') := by
      rw [Category.assoc, ← pP.w, ← Category.assoc]; exact h1
    exact Etale.of_comp _ j'
  have hz₁O : z₁ ∈ O₁ := by
    change pullback.fst b j' z₁ ∈ O
    rw [hz₁]; exact hz
  obtain ⟨U₁, hU₁, hE₁⟩ := exists_open_etale_of_isPullback_Spec σ sq₁ z₁ O₁ hz₁O hO₁
  let j₂ := U₁.ι ≫ pullback.fst f j
  have hE₂ : Etale (j₂ ≫ f) := by
    have e : j₂ ≫ f = (U₁.ι ≫ pullback.snd f j) ≫ j := by
      simp only [j₂, Category.assoc, pY.w]
    rw [e]; infer_instance
  refine ⟨j₂.opensRange, ⟨⟨a₁ z₁, hU₁⟩, ?_⟩, ?_⟩
  · change pullback.fst f j (a₁ z₁) = a z
    rw [← Scheme.Hom.comp_apply, show a₁ ≫ pullback.fst f j = pullback.fst b j' ≫ a from
      pullback.lift_fst _ _ _, Scheme.Hom.comp_apply, hz₁]
  · have e : j₂.opensRange.ι ≫ f = j₂.isoOpensRange.inv ≫ j₂ ≫ f := by
      rw [← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e]; infer_instance

/-- `R → S_s` étale gives étaleness of an open containing `D(s)`. -/
lemma exists_open_of_etale_away {Q Vs : Scheme.{u}} [IsAffine Q] [IsAffine Vs] (φ : Q ⟶ Vs)
    (s : Γ(Q, ⊤)) (hE : letI := φ.appTop.hom.toAlgebra; Algebra.Etale Γ(Vs, ⊤) (Localization.Away s)) :
    ∃ U : Q.Opens, Q.basicOpen s ≤ U ∧ Etale (U.ι ≫ φ) := by
  letI := φ.appTop.hom.toAlgebra
  let T := Localization.Away s
  let toT : Γ(Q, ⊤) ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap Γ(Q, ⊤) T)
  have hrangeT : Set.range (Spec.map toT) = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum Γ(Q, ⊤))) :=
    PrimeSpectrum.localization_away_comap_range T s
  have : IsOpenImmersion (Spec.map toT) := IsOpenImmersion.of_isLocalization (S := T) s
  let J : Spec (CommRingCat.of T) ⟶ Q := Spec.map toT ≫ Q.isoSpec.inv
  have e2 : Q.isoSpec.inv ≫ φ = Spec.map φ.appTop ≫ Vs.isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hEt : Etale (J ≫ φ) := by
    have hJ : J ≫ φ = Spec.map (φ.appTop ≫ toT) ≫ Vs.isoSpec.inv := by
      simp only [J, Category.assoc, e2, Spec.map_comp]
    rw [hJ]
    have : Etale (Spec.map (φ.appTop ≫ toT)) := by
      refine (HasRingHomProperty.Spec_iff (P := @Etale)).2 ?_
      have e3 : (φ.appTop ≫ toT).hom = algebraMap Γ(Vs, ⊤) T := by
        rw [IsScalarTower.algebraMap_eq Γ(Vs, ⊤) Γ(Q, ⊤) T]; rfl
      rw [e3]
      exact (RingHom.etale_algebraMap (R := Γ(Vs, ⊤)) (S := T)).2 hE
    infer_instance
  refine ⟨J.opensRange, fun x hx => ?_, ?_⟩
  · have hx2 : s ∉ (Q.toSpecΓ x).asIdeal := by
      have hx' : x ∈ Q.basicOpen s := hx
      rw [← Scheme.toSpecΓ_preimage_basicOpen] at hx'
      exact hx'
    have hx3 : Q.isoSpec.hom x ∈ Set.range (Spec.map toT) := by
      rw [hrangeT, Scheme.isoSpec_hom]
      exact hx2
    obtain ⟨y, hy⟩ := hx3
    refine ⟨y, ?_⟩
    change Q.isoSpec.inv (Spec.map toT y) = _
    rw [hy, ← Scheme.Hom.comp_apply]; simp
  · have e5 : J.opensRange.ι ≫ φ = J.isoOpensRange.inv ≫ J ≫ φ := by
      rw [← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e5]; infer_instance

/-! ### The site -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `e` is étale, in presheaf form. -/
abbrev EtP {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (e : yoneda.obj V ⟶ X) : Prop :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) e

/-- `f` is locally of finite presentation, in presheaf form. -/
abbrev LFPP {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    (f : yoneda.obj W ⟶ X) : Prop :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)) f

instance oιOpen (V : BigFppfOver B S hS) (O : ((SCH).obj V).Opens) : IsOpenImmersion O.ι :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

lemma range_sub_oι {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : Set.range ((SCH).map τ) ⊆ Set.range O.ι := by
  rw [Scheme.Opens.range_ι]; exact h

/-- The scheme map underlying `oLift`. -/
noncomputable def oLiftS {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : (SCH).obj T ⟶ O.toScheme :=
  @IsOpenImmersion.lift _ _ _ O.ι ((SCH).map τ) (oιOpen V O) (range_sub_oι O τ h)

lemma oLiftS_fac {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : oLiftS O τ h ≫ O.ι = (SCH).map τ :=
  @IsOpenImmersion.lift_fac _ _ _ O.ι ((SCH).map τ) (oιOpen V O) _

/-- A map landing in an open factors through it. -/
noncomputable def oLift {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : T ⟶ Chart.immObj V O.ι :=
  Over.homMk ⟨oLiftS O τ h⟩ (by
    apply InducedCategory.hom_ext
    change oLiftS O τ h ≫ O.ι ≫ V.hom.hom = T.hom.hom
    rw [← Category.assoc, oLiftS_fac]
    exact congrArg (fun z => z.hom) (Over.w τ))

lemma oLift_ι {V T : BigFppfOver B S hS} (O : ((SCH).obj V).Opens) (τ : T ⟶ V)
    (h : Set.range ((SCH).map τ) ⊆ O) : oLift O τ h ≫ Chart.immι V O.ι = τ :=
  ChartMain.siteExt (by
    rw [Functor.map_comp]; exact oLiftS_fac O τ h)

/-- A scheme isomorphic to `Spec k` has at most one point. -/
lemma subsingleton_of_iso {Q : Scheme.{u}} {k : Type u} [Field k] (iso : Q ≅ Spec (.of k)) :
    Subsingleton Q := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : Q, iso.inv (iso.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply]; simp
  have : (iso.hom x : PrimeSpectrum k) = (iso.hom y : PrimeSpectrum k) := Subsingleton.elim _ _
  rw [← h x, ← h y]
  exact congrArg iso.inv this

/-- `Γ(Spec k)` is a field. -/
lemma isField_of_iso {Q : Scheme.{u}} {k : Type u} [Field k] (iso : Q ≅ Spec (.of k)) :
    IsField Γ(Q, ⊤) := by
  let e1 : Γ(Q, ⊤) ≃+* Γ(Spec (.of k), ⊤) := (Scheme.Γ.mapIso iso.symm.op).commRingCatIsoToRingEquiv
  let e2 : Γ(Spec (.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  exact MulEquiv.isField (Field.toIsField k) (e1.trans e2).toMulEquiv

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W P : BigFppfOver B S hS}
  {e : yoneda.obj V ⟶ X} {f : yoneda.obj W ⟶ X}

/-- Shrinking step: the output of `exists_chartPiece`: an affine open `O` of `W ×_X V` containing the image
of the point. Its rings are `ChartPiece.ringV`, `ringW`, `ringP` below. -/
structure ChartPiece (he : EtP e) (f : yoneda.obj W ⟶ X) (u₀ : P ⟶ W) (v : P ⟶ V)
    (hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e) where
  /-- the open -/
  O : ((SCH).obj (he.rep.pullback f)).Opens
  /-- it is affine -/
  affine : IsAffineOpen O
  /-- it contains the image of `P` -/
  mem : ∀ x : (SCH).obj P, (SCH).map (he.rep.lift' v u₀ hw.symm) x ∈ O

namespace ChartPiece

variable {he : EtP e} {u₀ : P ⟶ W} {v : P ⟶ V} {hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e}
  (c : ChartPiece he f u₀ v hw)

/-- `Sobj := Spec S`, the open of `W ×_X V` as an object. -/
noncomputable abbrev Sobj : BigFppfOver B S hS := Chart.immObj (he.rep.pullback f) c.O.ι

instance : IsAffine ((SCH).obj c.Sobj) := c.affine

/-- `Spec S → W`. -/
noncomputable def toW : c.Sobj ⟶ W := Chart.immι _ c.O.ι ≫ he.rep.snd f

/-- `Spec S → V`. -/
noncomputable def toV : c.Sobj ⟶ V := Chart.immι _ c.O.ι ≫ he.rep.fst' f

/-- `P → Spec S`. -/
noncomputable def pt : P ⟶ c.Sobj := oLift c.O (he.rep.lift' v u₀ hw.symm) (by
  rintro _ ⟨x, rfl⟩; exact c.mem x)

lemma pt_ι : c.pt ≫ Chart.immι _ c.O.ι = he.rep.lift' v u₀ hw.symm := oLift_ι _ _ _

lemma pt_toW : c.pt ≫ c.toW = u₀ := by
  rw [toW, ← Category.assoc, pt_ι]; exact he.rep.lift'_snd _ _ _

lemma pt_toV : c.pt ≫ c.toV = v := by
  rw [toV, ← Category.assoc, pt_ι]; exact he.rep.lift'_fst _ _ _

/-- `Spec S → W ×_X V → V` commutes over `X` with `Spec S → W`. -/
lemma toW_comm : yoneda.map c.toW ≫ f = yoneda.map c.toV ≫ e := by
  have := (he.rep.isPullback' f).w
  simp only [toW, toV, Functor.map_comp, Category.assoc, this]

/-- `R → S`, with `R = Γ(V)`. -/
noncomputable def ringV : Γ((SCH).obj V, ⊤) →+* Γ((SCH).obj c.Sobj, ⊤) :=
  ((SCH).map c.toV).appTop.hom

/-- `G → S`, with `G = Γ(W)`. -/
noncomputable def ringW : Γ((SCH).obj W, ⊤) →+* Γ((SCH).obj c.Sobj, ⊤) :=
  ((SCH).map c.toW).appTop.hom

/-- `S → Γ(P)`. -/
noncomputable def ringP : Γ((SCH).obj c.Sobj, ⊤) →+* Γ((SCH).obj P, ⊤) :=
  ((SCH).map c.pt).appTop.hom

lemma ringP_ringW (y : Γ((SCH).obj W, ⊤)) : c.ringP (c.ringW y) = ((SCH).map u₀).appTop.hom y := by
  conv_rhs => rw [← c.pt_toW, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

lemma ringP_ringV (y : Γ((SCH).obj V, ⊤)) : c.ringP (c.ringV y) = ((SCH).map v).appTop.hom y := by
  conv_rhs => rw [← c.pt_toV, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

lemma etale_toW : Etale ((SCH).map c.toW) := by
  have h : Etale ((SCH).map (he.rep.snd f)) := he.property_snd f
  rw [toW, Functor.map_comp]
  change Etale (c.O.ι ≫ _)
  infer_instance

/-- **D1**: `G → S` is étale. -/
theorem ringW_etale [IsAffine ((SCH).obj W)] : c.ringW.Etale :=
  (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 c.etale_toW

lemma lfp_fst (hfp : LFPP f) :
    LocallyOfFinitePresentation ((SCH).map (he.rep.fst' f)) :=
  hfp.property e _ _ (he.rep.isPullback' f).flip

/-- **D1**: `R → S` is of finite presentation. -/
theorem ringV_finitePresentation [IsAffine ((SCH).obj V)] (hfp : LFPP f) :
    c.ringV.FinitePresentation := by
  have h := lfp_fst (he := he) hfp
  have h2 : LocallyOfFinitePresentation ((SCH).map c.toV) := by
    rw [toV, Functor.map_comp]
    change LocallyOfFinitePresentation (c.O.ι ≫ _)
    infer_instance
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).1 h2

/-- **D1**: if `G → Γ(P)` is onto, so is `S → Γ(P)`. -/
theorem ringP_surjective (hs : Function.Surjective ((SCH).map u₀).appTop.hom) :
    Function.Surjective c.ringP := fun y => by
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨c.ringW x, c.ringP_ringW x⟩

/-- **D1**: `q = ker (S → Γ(P))` is maximal. -/
theorem ker_isMaximal {k : Type u} [Field k] (iso : (SCH).obj P ≅ Spec (.of k))
    (hs : Function.Surjective ((SCH).map u₀).appTop.hom) : (RingHom.ker c.ringP).IsMaximal := by
  letI := (isField_of_iso iso).toField
  exact RingHom.ker_isMaximal_of_surjective _ (c.ringP_surjective hs)

/-- **D1**: `q` contracts to the kernel of `u₀`. -/
theorem comap_ringW : (RingHom.ker c.ringP).comap c.ringW = RingHom.ker ((SCH).map u₀).appTop.hom := by
  ext y
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ringP_ringW]

/-- **D1**: `q` contracts to the kernel of `v`. -/
theorem comap_ringV : (RingHom.ker c.ringP).comap c.ringV = RingHom.ker ((SCH).map v).appTop.hom := by
  ext y
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ringP_ringV]

end ChartPiece

/-- **D1**: `W ×_X V` has an affine open at the point `(u₀, v)`. -/
theorem exists_chartPiece (he : EtP e) (f : yoneda.obj W ⟶ X) {k : Type u} [Field k]
    (iso : (SCH).obj P ≅ Spec (.of k)) (u₀ : P ⟶ W) (v : P ⟶ V)
    (hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e) : Nonempty (ChartPiece he f u₀ v hw) := by
  have hsub := subsingleton_of_iso iso
  let x₀ : (SCH).obj P := iso.inv (default : PrimeSpectrum k)
  obtain ⟨O, hO, hz, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top ((SCH).map (he.rep.lift' v u₀ hw.symm) x₀))
  exact ⟨⟨O, hO, fun x => by rw [Subsingleton.elim x x₀]; exact hz⟩⟩

/-! ### D2 -/

/-- The criterion for `IsEtaleOn`, on the represented pullbacks of `f`. -/
lemma isEtaleOn_of_points [IsAffine ((SCH).obj W)] (hfp : LFPP f) (g : Γ((SCH).obj W, ⊤))
    (H : ∀ {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X) (y : (SCH).obj (hfp.rep.pullback x)),
      (SCH).map (hfp.rep.fst' x) y ∈ ((SCH).obj W).basicOpen g →
      ∃ U : ((SCH).obj (hfp.rep.pullback x)).Opens, y ∈ U ∧ Etale (U.ι ≫ (SCH).map (hfp.rep.snd x))) :
    IsEtaleOn f g := by
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hO := dιOpen W g
  refine MorphismProperty.relative.of_exists fun T x => ?_
  let hrep := hfp.rep
  let a := hrep.fst' x
  let D := ((SCH).obj W).basicOpen g
  let Oy : ((SCH).obj (hrep.pullback x)).Opens := (SCH).map a ⁻¹ᵁ D
  let top : Chart.immObj (hrep.pullback x) Oy.ι ⟶ dObj W g :=
    oLift D (Chart.immι _ Oy.ι ≫ a) (by
      rintro _ ⟨z, rfl⟩
      rw [Functor.map_comp]
      exact z.2)
  have htop : top ≫ dι W g = Chart.immι _ Oy.ι ≫ a := oLift_ι _ _ _
  have hPB : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hsR : ∀ s : PullbackCone (dι W g) a, Set.range ((SCH).map s.snd) ⊆ Oy := by
    rintro s _ ⟨z, rfl⟩
    have e0 : (SCH).map s.snd ≫ (SCH).map a = (SCH).map s.fst ≫ (SCH).map (dι W g) := by
      rw [← Functor.map_comp, ← Functor.map_comp, s.condition]
    change (SCH).map a ((SCH).map s.snd z) ∈ D
    rw [← Scheme.Hom.comp_apply, e0, Scheme.Hom.comp_apply]
    exact ((SCH).map s.fst z).2
  have sq0 : IsPullback top (Chart.immι _ Oy.ι) (dι W g) a := by
    refine ⟨⟨htop⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => oLift Oy s.snd (hsR s)) ?_ ?_ ?_⟩⟩
    · intro s
      have : Mono (dι W g) := inferInstance
      refine (cancel_mono (dι W g)).1 ?_
      rw [Category.assoc, htop, ← Category.assoc]
      exact (congrArg (· ≫ a) (oLift_ι _ _ _)).trans s.condition.symm
    · intro s; exact oLift_ι _ _ _
    · intro s m _ h2
      refine ChartMain.siteExt ?_
      have h3 : m ≫ Chart.immι _ Oy.ι = oLift Oy s.snd (hsR s) ≫ Chart.immι _ Oy.ι := by
        rw [h2]; exact (oLift_ι _ _ _).symm
      have h4 := congrArg (fun z => (SCH).map z) h3
      simp only [Functor.map_comp] at h4
      exact (cancel_mono (Oy.ι)).1 h4
  have sq := (sq0.map yoneda).paste_vert (hrep.isPullback' x)
  rw [← yoneda.map_comp] at sq
  refine ⟨_, _, _, sq, ?_⟩
  change Etale ((SCH).map (_ ≫ hrep.snd x))
  rw [Functor.map_comp]
  change Etale (Oy.ι ≫ (SCH).map (hrep.snd x))
  refine etale_of_forall_open' _ fun y => ?_
  obtain ⟨U, hU, hE⟩ := H x y.1 y.2
  refine ⟨Oy.ι ⁻¹ᵁ U, hU, ?_⟩
  rw [← Category.assoc]
  refine etale_comp_of_range' _ U _ ?_ hE
  rintro _ ⟨z, rfl⟩
  exact z.2

/-- The cube of the shrinking step: étaleness of `Wv → V` on `Ω'`, at `z₀`, gives étaleness of `W ×_X T → T` at any
point over the image of `z₀`. -/
lemma exists_open_of_mem (he : EtP e) (hfp : LFPP f)
    (Ω' : ((SCH).obj (he.rep.pullback f)).Opens)
    (hΩ : Etale (Ω'.ι ≫ (SCH).map (he.rep.fst' f)))
    {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X) (y : (SCH).obj (hfp.rep.pullback x))
    (z₀ : (SCH).obj (he.rep.pullback f)) (hz₀ : z₀ ∈ Ω')
    (hzy : (SCH).map (he.rep.snd f) z₀ = (SCH).map (hfp.rep.fst' x) y) :
    ∃ U : ((SCH).obj (hfp.rep.pullback x)).Opens, y ∈ U ∧
      Etale (U.ι ≫ (SCH).map (hfp.rep.snd x)) := by
  have hPB : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let a := hfp.rep.fst' x
  let b := hfp.rep.snd x
  have sqY : IsPullback (yoneda.map a) (yoneda.map b) f x := hfp.rep.isPullback' x
  have sqW := he.rep.isPullback' f
  have sqT := he.rep.isPullback' x
  have sqH := he.rep.isPullback' (yoneda.map a ≫ f)
  let fH := he.rep.fst' (yoneda.map a ≫ f)
  let pY := he.rep.snd (yoneda.map a ≫ f)
  have hH : yoneda.map fH ≫ e = yoneda.map pY ≫ yoneda.map a ≫ f := sqH.w
  have sqH' : IsPullback (yoneda.map fH) (yoneda.map pY) e (yoneda.map b ≫ x) := by
    have : ∀ {g' : yoneda.obj _ ⟶ X} (_ : yoneda.map a ≫ f = g'),
        IsPullback (yoneda.map fH) (yoneda.map pY) e g' := by
      rintro _ rfl; exact sqH
    exact this sqY.w
  let pW : he.rep.pullback (yoneda.map a ≫ f) ⟶ he.rep.pullback f :=
    he.rep.lift' fH (pY ≫ a) (by rw [hH, Functor.map_comp, Category.assoc])
  let h : he.rep.pullback (yoneda.map a ≫ f) ⟶ he.rep.pullback x :=
    he.rep.lift' fH (pY ≫ b) (by
      rw [hH, Functor.map_comp, Category.assoc]; exact congrArg (yoneda.map pY ≫ ·) sqY.w)
  have hpW1 : pW ≫ he.rep.fst' f = fH := he.rep.lift'_fst _ _ _
  have hpW2 : pW ≫ he.rep.snd f = pY ≫ a := he.rep.lift'_snd _ _ _
  have hh1 : h ≫ he.rep.fst' x = fH := he.rep.lift'_fst _ _ _
  have hh2 : h ≫ he.rep.snd x = pY ≫ b := he.rep.lift'_snd _ _ _
  have A : IsPullback (yoneda.map pW) (yoneda.map pY) (yoneda.map (he.rep.snd f)) (yoneda.map a) := by
    refine IsPullback.of_right (h₁₂ := yoneda.map (he.rep.fst' f)) (v₁₃ := e) (h₂₂ := f) ?_ ?_ sqW
    · rw [← yoneda.map_comp, hpW1]; exact sqH
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hpW2]
  have C : IsPullback (yoneda.map h) (yoneda.map pY) (yoneda.map (he.rep.snd x)) (yoneda.map b) := by
    refine IsPullback.of_right (h₁₂ := yoneda.map (he.rep.fst' x)) (v₁₃ := e) (h₂₂ := x) ?_ ?_ sqT
    · rw [← yoneda.map_comp, hh1]; exact sqH'
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hh2]
  have B : IsPullback (yoneda.map pW) (yoneda.map h) (yoneda.map (he.rep.fst' f))
      (yoneda.map (he.rep.fst' x)) := by
    refine IsPullback.of_right (h₁₂ := yoneda.map (he.rep.snd f)) (v₁₃ := f) (h₂₂ := e) ?_ ?_ sqW.flip
    · have o := C.flip.paste_horiz sqY
      rw [← yoneda.map_comp pW, hpW2, yoneda.map_comp pY, sqT.w]
      exact o
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hpW1, hh1]
  have As : IsPullback ((SCH).map pW) ((SCH).map pY) ((SCH).map (he.rep.snd f)) ((SCH).map a) :=
    (IsPullback.of_map yoneda (by rw [hpW2]) A).map (SCH)
  have Bs : IsPullback ((SCH).map pW) ((SCH).map h) ((SCH).map (he.rep.fst' f))
      ((SCH).map (he.rep.fst' x)) :=
    (IsPullback.of_map yoneda (by rw [hpW1, hh1]) B).map (SCH)
  have Cs : IsPullback ((SCH).map h) ((SCH).map pY) ((SCH).map (he.rep.snd x)) ((SCH).map b) :=
    (IsPullback.of_map yoneda (by rw [hh2]) C).map (SCH)
  obtain ⟨ŷ, hŷ1, hŷ2⟩ := exists_pt_of_isPullback As z₀ y hzy
  let O' := (SCH).map pW ⁻¹ᵁ Ω'
  have hO' : Etale (O'.ι ≫ (SCH).map h) :=
    MorphismProperty.of_isPullback (P := @Etale)
      ((isPullback_morphismRestrict ((SCH).map pW) Ω').paste_vert Bs) hΩ
  have hŷO : ŷ ∈ O' := by
    change (SCH).map pW ŷ ∈ Ω'
    rw [hŷ1]; exact hz₀
  have l1 : LocallyOfFinitePresentation ((SCH).map b) := hfp.property_snd x
  have l2 : Etale ((SCH).map (he.rep.snd x)) := he.property_snd x
  obtain ⟨U, hU, hE⟩ := exists_open_etale_of_isPullback Cs.flip ŷ O' hŷO hO'
  exact ⟨U, by rwa [hŷ2] at hU, hE⟩

namespace ChartPiece

variable {he : EtP e} {u₀ : P ⟶ W} {v : P ⟶ V} {hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e}
  (c : ChartPiece he f u₀ v hw)

/-- The étale locus of `Wv → V` at the point. -/
lemma exists_locus [IsAffine ((SCH).obj V)] {k : Type u} [Field k]
    (iso : (SCH).obj P ≅ Spec (.of k)) (hfp : LFPP f) [hq : (RingHom.ker c.ringP).IsPrime]
    (h : letI := c.ringV.toAlgebra; Algebra.IsEtaleAt Γ((SCH).obj V, ⊤) (RingHom.ker c.ringP)) :
    ∃ Ω' : ((SCH).obj (he.rep.pullback f)).Opens,
      (∀ x : (SCH).obj P, (SCH).map (he.rep.lift' v u₀ hw.symm) x ∈ Ω') ∧
      Etale (Ω'.ι ≫ (SCH).map (he.rep.fst' f)) := by
  letI := c.ringV.toAlgebra
  have hfpa : Algebra.FinitePresentation Γ((SCH).obj V, ⊤) Γ((SCH).obj c.Sobj, ⊤) :=
    c.ringV_finitePresentation hfp
  obtain ⟨s, hs, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ((SCH).obj V, ⊤))
    (RingHom.ker c.ringP)
  have hE' : letI := ((SCH).map c.toV).appTop.hom.toAlgebra
      Algebra.Etale Γ((SCH).obj V, ⊤) (Localization.Away s) := hE
  obtain ⟨U, hU, hUE⟩ := exists_open_of_etale_away ((SCH).map c.toV) s hE'
  let J : U.toScheme ⟶ (SCH).obj (he.rep.pullback f) := U.ι ≫ c.O.ι
  have e1 : c.O.ι ≫ (SCH).map (he.rep.fst' f) = (SCH).map c.toV := by
    rw [toV, Functor.map_comp]; rfl
  have hEt : Etale (J ≫ (SCH).map (he.rep.fst' f)) := by
    have : J ≫ (SCH).map (he.rep.fst' f) = U.ι ≫ (SCH).map c.toV := by
      rw [← e1]; exact Category.assoc _ _ _
    rw [this]; exact hUE
  have hJo : IsOpenImmersion J := by
    have i1 : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))
    have i2 : IsOpenImmersion c.O.ι := oιOpen _ _
    exact @IsOpenImmersion.comp _ _ _ U.ι c.O.ι i1 i2
  refine ⟨J.opensRange, fun x => ?_, ?_⟩
  · have hne : c.ringP s ≠ 0 := fun h0 => hs h0
    have hunit : IsUnit (c.ringP s) := by
      letI := (isField_of_iso iso).toField
      exact isUnit_iff_ne_zero.2 hne
    have hb : ((SCH).obj P).basicOpen (c.ringP s) = ⊤ := Scheme.basicOpen_of_isUnit _ hunit
    have hx : (SCH).map c.pt x ∈ ((SCH).obj c.Sobj).basicOpen s := by
      change x ∈ (SCH).map c.pt ⁻¹ᵁ ((SCH).obj c.Sobj).basicOpen s
      rw [Scheme.preimage_basicOpen]
      change x ∈ ((SCH).obj P).basicOpen (c.ringP s)
      rw [hb]; trivial
    refine ⟨⟨_, hU hx⟩, ?_⟩
    change c.O.ι ((SCH).map c.pt x) = _
    rw [← c.pt_ι, Functor.map_comp, Scheme.Hom.comp_apply]
    rfl
  · have e5 : J.opensRange.ι ≫ (SCH).map (he.rep.fst' f) =
        J.isoOpensRange.inv ≫ J ≫ (SCH).map (he.rep.fst' f) := by
      rw [← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    rw [e5]; infer_instance

end ChartPiece

/-- **D2**: "the étale locus is open and contains `w`". If `Wv → V` is étale at `z`, then
`D(g₀) → X` is étale for some `g₀` not vanishing at `u₀`. -/
theorem exists_etaleOn_of_isEtaleAt [IsAffine ((SCH).obj W)] [IsAffine ((SCH).obj V)]
    {he : EtP e} {u₀ : P ⟶ W} {v : P ⟶ V} {hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e}
    (c : ChartPiece he f u₀ v hw) {k : Type u} [Field k] (iso : (SCH).obj P ≅ Spec (.of k))
    (hfp : LFPP f) [hq : (RingHom.ker c.ringP).IsPrime]
    (h : letI := c.ringV.toAlgebra; Algebra.IsEtaleAt Γ((SCH).obj V, ⊤) (RingHom.ker c.ringP)) :
    ∃ g₀ : Γ((SCH).obj W, ⊤), IsEtaleOn f g₀ ∧ ((SCH).map u₀).appTop.hom g₀ ≠ 0 := by
  obtain ⟨Ω', hmem, hΩ⟩ := c.exists_locus iso hfp h
  have hEs : Etale ((SCH).map (he.rep.snd f)) := he.property_snd f
  have hopen : IsOpenMap ((SCH).map (he.rep.snd f)) := ((SCH).map (he.rep.snd f)).isOpenMap
  let Ω : ((SCH).obj W).Opens := ⟨(SCH).map (he.rep.snd f) '' Ω', hopen _ Ω'.2⟩
  let x₀ : (SCH).obj P := iso.inv (default : PrimeSpectrum k)
  have hl : (SCH).map (he.rep.lift' v u₀ hw.symm) ≫ (SCH).map (he.rep.snd f) = (SCH).map u₀ := by
    rw [← Functor.map_comp, he.rep.lift'_snd]
  have hx₀ : (SCH).map u₀ x₀ ∈ Ω :=
    ⟨_, hmem x₀, by rw [← Scheme.Hom.comp_apply, hl]⟩
  obtain ⟨g₀, hle, hg₀⟩ := (isAffineOpen_top ((SCH).obj W)).exists_basicOpen_le ⟨_, hx₀⟩ trivial
  refine ⟨g₀, isEtaleOn_of_points hfp g₀ fun {T} x y hy => ?_, fun h0 => ?_⟩
  · obtain ⟨z₀, hz₀, hzy⟩ := hle hy
    exact exists_open_of_mem he hfp Ω' hΩ x y z₀ hz₀ hzy
  · have hmem' : x₀ ∈ (SCH).map u₀ ⁻¹ᵁ ((SCH).obj W).basicOpen g₀ := hg₀
    rw [Scheme.preimage_basicOpen] at hmem'
    have h1 : ((SCH).obj P).basicOpen (((SCH).map u₀).appTop.hom g₀) = ⊥ := by
      rw [h0]; exact Scheme.basicOpen_zero _ _
    have h2 : x₀ ∈ ((SCH).obj P).basicOpen (((SCH).map u₀).appTop.hom g₀) := hmem'
    rw [h1] at h2
    exact h2

/-! ### D3 -/

lemma closedι_appTop_of_mem {Y : Scheme.{u}} [IsAffine Y] (I : Ideal Γ(Y, ⊤)) (r : Γ(Y, ⊤))
    (h : r ∈ I) : (Chart.closedι Y I).appTop r = 0 := by
  have e : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ Y.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    simp
  have hinv : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := (Iso.hom_comp_eq_id _).mp e
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have this : (Chart.closedι Y I).appTop r =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
        ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    rw [Chart.closedι, Scheme.Hom.comp_appTop, hinv]; rfl
  have h1 := ConcreteCategory.congr_hom hnat ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← this] at h1
  have h3 : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) = r := by simp
  erw [h3] at h1
  have h2 : (Ideal.Quotient.mk I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
  erw [h2] at h1
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, ⊤) ⧸ I))).hom ((Chart.closedι Y I).appTop r) = 0 := h1
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, ⊤) ⧸ I))).inv h4
  simpa using this

/-- An affine scheme whose local ring has nilpotent maximal ideal has at most one point. -/
lemma subsingleton_of_nil {Y : Scheme.{u}} [IsAffine Y] [IsLocalRing Γ(Y, ⊤)]
    (hnil : ∀ x ∈ IsLocalRing.maximalIdeal Γ(Y, ⊤), IsNilpotent x) : Subsingleton Y := by
  have hp : ∀ p : PrimeSpectrum Γ(Y, ⊤), p.asIdeal = IsLocalRing.maximalIdeal Γ(Y, ⊤) := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) fun x hx => by
      obtain ⟨n, hn⟩ := hnil x hx
      exact p.2.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : Y, Y.isoSpec.inv (Y.isoSpec.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply]; simp
  have : (Y.isoSpec.hom x : PrimeSpectrum Γ(Y, ⊤)) = Y.isoSpec.hom y :=
    PrimeSpectrum.ext ((hp _).trans (hp _).symm)
  rw [← h x, ← h y]
  exact congrArg Y.isoSpec.inv this

/-- **D3**: two maps to `V`, equal after the étale `e`, agreeing at the closed point of an
infinitesimal `Z`, are equal. -/
theorem eq_of_agree_on_closedPoint (he : EtP e) [IsAffine ((SCH).obj V)] {Z : BigFppfOver B S hS}
    [IsAffine ((SCH).obj Z)] [IsLocalRing Γ((SCH).obj Z, ⊤)]
    (hnil : ∀ x ∈ IsLocalRing.maximalIdeal Γ((SCH).obj Z, ⊤), IsNilpotent x) (a b : Z ⟶ V)
    (hab : yoneda.map a ≫ e = yoneda.map b ≫ e)
    (hc : ∀ y : Γ((SCH).obj V, ⊤), ((SCH).map a).appTop.hom y - ((SCH).map b).appTop.hom y ∈
      IsLocalRing.maximalIdeal Γ((SCH).obj Z, ⊤)) : a = b := by
  let t : yoneda.obj Z ⟶ X := yoneda.map a ≫ e
  have sq := he.rep.isPullback' t
  let sa : Z ⟶ he.rep.pullback t := he.rep.lift' a (𝟙 Z) (by simp [t])
  let sb : Z ⟶ he.rep.pullback t := he.rep.lift' b (𝟙 Z) (by simp [t, hab])
  have sa1 : sa ≫ he.rep.fst' t = a := he.rep.lift'_fst _ _ _
  have sa2 : sa ≫ he.rep.snd t = 𝟙 Z := he.rep.lift'_snd _ _ _
  have sb1 : sb ≫ he.rep.fst' t = b := he.rep.lift'_fst _ _ _
  have sb2 : sb ≫ he.rep.snd t = 𝟙 Z := he.rep.lift'_snd _ _ _
  let m := IsLocalRing.maximalIdeal Γ((SCH).obj Z, ⊤)
  let ci := Chart.closedι ((SCH).obj Z) m
  let Zc := Chart.immObj Z ci
  let cl : Zc ⟶ Z := Chart.immι Z ci
  have hcS : (SCH).map cl = ci := rfl
  have hcab : cl ≫ a = cl ≫ b := by
    refine ChartMain.siteExt ?_
    rw [Functor.map_comp, Functor.map_comp]
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    ext y
    have h0 := closedι_appTop_of_mem m _ (hc y)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hcs : cl ≫ sa = cl ≫ sb := yoneda.map_injective (sq.hom_ext
    (by simp only [← yoneda.map_comp, Category.assoc, sa1, sb1, hcab])
    (by simp only [← yoneda.map_comp, Category.assoc, sa2, sb2]))
  let π := (SCH).map (he.rep.snd t)
  have hπ : Etale π := he.property_snd t
  have hsa : (SCH).map sa ≫ π = 𝟙 _ := by
    rw [← Functor.map_comp, sa2, (SCH).map_id]
  have hsb : (SCH).map sb ≫ π = 𝟙 _ := by
    rw [← Functor.map_comp, sb2, (SCH).map_id]
  let φ : (SCH).obj Z ⟶ pullback π π := pullback.lift ((SCH).map sa) ((SCH).map sb) (hsa.trans hsb.symm)
  let D := pullback.diagonal π
  have hD : IsOpenImmersion D := inferInstance
  have hφ1 : φ ≫ pullback.fst π π = (SCH).map sa := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π π = (SCH).map sb := pullback.lift_snd _ _ _
  have hD1 : D ≫ pullback.fst π π = 𝟙 _ := pullback.diagonal_fst _
  have hD2 : D ≫ pullback.snd π π = 𝟙 _ := pullback.diagonal_snd _
  have hcφ : ci ≫ φ = (ci ≫ (SCH).map sa) ≫ D := by
    have e1 : ci ≫ (SCH).map sa = ci ≫ (SCH).map sb := by
      have e := congrArg (fun z => (SCH).map z) hcs
      simp only [Functor.map_comp] at e
      exact e
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ1, hD1, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hφ2, hD2, Category.comp_id]
      exact e1.symm
  have hsub := subsingleton_of_nil hnil
  have hne : Nontrivial (Γ((SCH).obj Z, ⊤) ⧸ m) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have hr : Set.range φ ⊆ Set.range D := by
    rintro _ ⟨x, rfl⟩
    let x₁ : PrimeSpectrum (Γ((SCH).obj Z, ⊤) ⧸ m) := Classical.arbitrary _
    let x₂ : Spec (.of (Γ((SCH).obj Z, ⊤) ⧸ m)) := x₁
    rw [Subsingleton.elim x (ci x₂), ← Scheme.Hom.comp_apply, hcφ, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let l := IsOpenImmersion.lift D φ hr
  have hl : l ≫ D = φ := IsOpenImmersion.lift_fac _ _ _
  have e1 : (SCH).map sa = l := by
    rw [← hφ1, ← hl, Category.assoc, hD1, Category.comp_id]
  have e2 : (SCH).map sb = l := by
    rw [← hφ2, ← hl, Category.assoc, hD2, Category.comp_id]
  have hs : sa = sb := ChartMain.siteExt (e1.trans e2.symm)
  rw [← sa1, ← sb1, hs]

/-! ### D4 -/

/-- **D4**: for `o : Z → X` closed, `Z` affine, the base change `Zv = Z ×_X V` along the étale
`e : V → X` is affine, `Γ(Z) → Γ(Zv)` is étale, `Γ(V) → Γ(Zv)` is onto with kernel the global sections
of `idealOf ho e`. The maps are `appTop` of `fst'` and `snd`, and the square commutes over `X`. -/
theorem etale_base_change_ideal {Z : BigFppfOver B S hS} {o : yoneda.obj Z ⟶ X}
    (ho : ChartMain.ClosedP o) (he : EtP e) [IsAffine ((SCH).obj Z)] [IsAffine ((SCH).obj V)] :
    ∃ _ : IsAffine ((SCH).obj (ho.rep.pullback e)),
      ((SCH).map (ho.rep.fst' e)).appTop.hom.Etale ∧
      Function.Surjective ((SCH).map (ho.rep.snd e)).appTop.hom ∧
      RingHom.ker ((SCH).map (ho.rep.snd e)).appTop.hom =
        (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ∧
      yoneda.map (ho.rep.fst' e) ≫ o = yoneda.map (ho.rep.snd e) ≫ e := by
  have hcl : IsClosedImmersion ((SCH).map (ho.rep.snd e)) := ho.property_snd e
  obtain ⟨h1, h2⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map (ho.rep.snd e))
  have hE : Etale ((SCH).map (ho.rep.fst' e)) := he.property o _ _ (ho.rep.isPullback' e).flip
  refine ⟨h1, (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hE, h2, ?_,
    (ho.rep.isPullback' e).w⟩
  exact (Scheme.Hom.ker_apply ((SCH).map (ho.rep.snd e)) ⟨⊤, isAffineOpen_top _⟩).symm

end Site

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_chartPiece
#print axioms AlgMag.ChartS5.ChartPiece.ringW_etale
#print axioms AlgMag.ChartS5.ChartPiece.ringV_finitePresentation
#print axioms AlgMag.ChartS5.ChartPiece.ker_isMaximal
#print axioms AlgMag.ChartS5.exists_etaleOn_of_isEtaleAt
#print axioms AlgMag.ChartS5.eq_of_agree_on_closedPoint
#print axioms AlgMag.ChartS5.etale_base_change_ideal
