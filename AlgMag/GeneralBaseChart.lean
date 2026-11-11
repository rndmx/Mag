/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseCore

/-!
# Affine charts of an action over a general base

Let `X → S` be an affine morphism and `U ⊆ S` an affine open, with `R = Γ(S, U)` and
`A = Γ(X, p⁻¹ U)`. For every scheme `T` over `U`, affine or not, morphisms `T → X` over `S` are
`R`-algebra maps `A → Γ(T, ⊤)` (`AlgMag.GB.ptX`).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.GB

variable {S : Scheme.{u}}

/-- `T` lies over the open `U` of `S`. -/
def LiesOver (T : Over S) (U : S.Opens) : Prop := T.hom ⁻¹ᵁ U = ⊤

lemma LiesOver.mem {T : Over S} {U : S.Opens} (h : LiesOver T U) (x : T.left) : T.hom x ∈ U := by
  have : x ∈ T.hom ⁻¹ᵁ U := by rw [h]; trivial
  exact this

lemma liesOver_of_forall {T : Over S} {U : S.Opens} (h : ∀ x : T.left, T.hom x ∈ U) :
    LiesOver T U := by
  refine top_le_iff.mp fun x _ => h x

lemma LiesOver.of_hom {T T' : Over S} {U : S.Opens} (s : T' ⟶ T) (h : LiesOver T U) :
    LiesOver T' U := by
  refine liesOver_of_forall fun x => ?_
  have : T'.hom = s.left ≫ T.hom := (Over.w s).symm
  rw [this, Scheme.Hom.comp_apply]
  exact h.mem _

lemma LiesOver.mono {T : Over S} {U U' : S.Opens} (h : LiesOver T U) (hU : U ≤ U') :
    LiesOver T U' :=
  liesOver_of_forall fun x => hU (h.mem x)

section Chart

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The morphism `T → Spec Γ(S, U)` of a scheme over `U`. -/
def tau (T : Over S) (hT : LiesOver T U) : T.left ⟶ Spec Γ(S, U) :=
  IsOpenImmersion.lift hU.fromSpec T.hom (by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact hT.mem x)

@[reassoc (attr := simp)]
lemma tau_fromSpec (T : Over S) (hT : LiesOver T U) : tau hU T hT ≫ hU.fromSpec = T.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The structure ring map `Γ(S, U) → Γ(T, ⊤)`. -/
def rT (T : Over S) (hT : LiesOver T U) : Γ(S, U) ⟶ Γ(T.left, ⊤) :=
  homSpecEquiv _ _ (tau hU T hT)

/-- `Γ(T, ⊤)` as an algebra over `Γ(S, U)`. -/
def Ga (T : Over S) (hT : LiesOver T U) : CommAlgCat.{u} Γ(S, U) :=
  letI := (rT hU T hT).hom.toAlgebra
  CommAlgCat.of Γ(S, U) Γ(T.left, ⊤)

lemma Ga_algebraMap (T : Over S) (hT : LiesOver T U) (r : Γ(S, U)) :
    algebraMap Γ(S, U) (Ga hU T hT) r = (rT hU T hT).hom r := rfl

/-- `Spec D` as a scheme over `S`, for an algebra `D` over `Γ(S, U)`. -/
def Phi (D : CommAlgCat.{u} Γ(S, U)) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec)

lemma liesOver_Phi (D : CommAlgCat.{u} Γ(S, U)) : LiesOver (Phi hU D) U := by
  refine liesOver_of_forall fun x => ?_
  let x' : Spec (CommRingCat.of D) := x
  have : hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) x') ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  have e : (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec) x' =
    hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) x') := Scheme.Hom.comp_apply _ _ _
  rw [← e] at this
  exact this

/-- **Functor of points of `Spec D` over `U`**: `Hom_S(T, Spec D) = Hom_R(D, Γ(T, ⊤))`. -/
def homPhi (T : Over S) (hT : LiesOver T U) (D : CommAlgCat.{u} Γ(S, U)) :
    (T ⟶ Phi hU D) ≃ (D →ₐ[Γ(S, U)] Ga hU T hT) where
  toFun f :=
    let f' : T.left ⟶ Spec (CommRingCat.of D) := f.left
    { (homSpecEquiv T.left _ f').hom with
      commutes' := fun r => by
        have h : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) = tau hU T hT := by
          rw [← cancel_mono hU.fromSpec, tau_fromSpec, Category.assoc]
          exact Over.w f
        have h2 := congrArg (homSpecEquiv T.left _) h
        rw [homSpecEquiv_map] at h2
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) r }
  invFun g :=
    let g' : D →+* Γ(T.left, ⊤) := g.toRingHom
    Over.homMk (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g')) (by
      have h : CommRingCat.ofHom (algebraMap Γ(S, U) D) ≫ CommRingCat.ofHom g' =
          rT hU T hT := by
        refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
        exact g.commutes r
      have h3 : T.left.toSpecΓ ≫ Spec.map (rT hU T hT) = tau hU T hT :=
        (homSpecEquiv T.left _).left_inv _
      change (T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec = T.hom
      rw [Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, h,
        ← Category.assoc, h3, tau_fromSpec])
  left_inv f := by
    refine Over.OverMorphism.ext ?_
    exact (homSpecEquiv T.left _).left_inv f.left
  right_inv g := by
    refine AlgHom.ext fun a => ?_
    let g' : D →+* Γ(T.left, ⊤) := g.toRingHom
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      ((homSpecEquiv T.left _).right_inv (CommRingCat.ofHom g'))) a

/-- The pull-back `Γ(T, ⊤) → Γ(T', ⊤)` along a morphism over `S`. -/
def gpull {T T' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U) (s : T' ⟶ T) :
    Ga hU T hT →ₐ[Γ(S, U)] Ga hU T' hT' :=
  { (s.left.appTop).hom with
    commutes' := fun r => by
      have h : s.left ≫ tau hU T hT = tau hU T' hT' := by
        rw [← cancel_mono hU.fromSpec, Category.assoc, tau_fromSpec, tau_fromSpec]
        exact Over.w s
      have h2 := homSpecEquiv_comp s.left (tau hU T hT)
      rw [h] at h2
      exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) r).symm }

@[simp] lemma gpull_apply {T T' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U) (s : T' ⟶ T)
    (x : Ga hU T hT) : gpull hU hT hT' s x = (s.left.appTop).hom x := rfl

lemma gpull_id {T : Over S} (hT : LiesOver T U) : gpull hU hT hT (𝟙 T) = AlgHom.id _ _ := by
  refine AlgHom.ext fun x => ?_
  simp
  rfl

lemma gpull_comp {T T' T'' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U)
    (hT'' : LiesOver T'' U) (s : T' ⟶ T) (s' : T'' ⟶ T') :
    gpull hU hT hT'' (s' ≫ s) = (gpull hU hT' hT'' s').comp (gpull hU hT hT' s) := by
  refine AlgHom.ext fun x => ?_
  simp
  rfl

lemma homPhi_comp {T T' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U) (s : T' ⟶ T)
    {D : CommAlgCat.{u} Γ(S, U)} (f : T ⟶ Phi hU D) :
    homPhi hU T' hT' D (s ≫ f) = (gpull hU hT hT' s).comp (homPhi hU T hT D f) := by
  refine AlgHom.ext fun a => ?_
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (homSpecEquiv_comp s.left f.left)) a

/-- The morphism `Spec D' → Spec D` over `S` of an algebra map `D → D'`. -/
def PhiMap {D D' : CommAlgCat.{u} Γ(S, U)} (t : D →ₐ[Γ(S, U)] D') : Phi hU D' ⟶ Phi hU D :=
  Over.homMk (Spec.map (CommRingCat.ofHom t.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom t.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D')) ≫ hU.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun r => t.commutes r))

/-- The canonical `D → Γ(Spec D, ⊤)`. -/
def eta (D : CommAlgCat.{u} Γ(S, U)) : D →ₐ[Γ(S, U)] Ga hU (Phi hU D) (liesOver_Phi hU D) :=
  homPhi hU _ _ D (𝟙 _)

lemma eta_apply (D : CommAlgCat.{u} Γ(S, U)) (x : D) :
    eta hU D x = (Scheme.ΓSpecIso (CommRingCat.of D)).inv x := by
  change ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of D)))).hom x = _
  simp

lemma eta_bijective (D : CommAlgCat.{u} Γ(S, U)) : Function.Bijective (eta hU D) := by
  have : IsIso (Scheme.ΓSpecIso (CommRingCat.of D)).inv := inferInstance
  have h := (ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of D)).inv).mp this
  have e : ⇑(eta hU D) = ⇑(Scheme.ΓSpecIso (CommRingCat.of D)).inv :=
    funext (eta_apply hU D)
  rw [e]
  exact h

/-- `D ≃ Γ(Spec D, ⊤)` as algebras. -/
def etaEquiv (D : CommAlgCat.{u} Γ(S, U)) : D ≃ₐ[Γ(S, U)] Ga hU (Phi hU D) (liesOver_Phi hU D) :=
  AlgEquiv.ofBijective (eta hU D) (eta_bijective hU D)

@[simp] lemma etaEquiv_apply (D : CommAlgCat.{u} Γ(S, U)) (x : D) :
    etaEquiv hU D x = eta hU D x := rfl

lemma homPhi_PhiMap {D D' : CommAlgCat.{u} Γ(S, U)} (t : D →ₐ[Γ(S, U)] D') :
    homPhi hU _ (liesOver_Phi hU D') D (PhiMap hU t) = (eta hU D').comp t := by
  refine AlgHom.ext fun a => ?_
  have := homSpecEquiv_map (T := Spec (CommRingCat.of D')) (CommRingCat.ofHom t.toRingHom) (𝟙 _)
  rw [Category.id_comp] at this
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) a

lemma gpull_PhiMap_eta {D D' : CommAlgCat.{u} Γ(S, U)} (t : D →ₐ[Γ(S, U)] D') :
    (gpull hU (liesOver_Phi hU D) (liesOver_Phi hU D') (PhiMap hU t)).comp (eta hU D) =
      (eta hU D').comp t := by
  rw [eta, ← homPhi_comp, Category.comp_id, homPhi_PhiMap]

end Chart

section X

variable (X : Over S) {U : S.Opens} (hU : IsAffineOpen U) [IsAffineHom X.hom]

/-- The affine open `p⁻¹ U` of `X`. -/
lemma isAffineOpen_preimage (hU : IsAffineOpen U) : IsAffineOpen (X.hom ⁻¹ᵁ U) :=
  IsAffineOpen.preimage hU X.hom

/-- `A = Γ(X, p⁻¹ U)`, as an algebra over `R = Γ(S, U)`. -/
def Aalg (U : S.Opens) : CommAlgCat.{u} Γ(S, U) :=
  letI := (X.hom.appLE U (X.hom ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  CommAlgCat.of Γ(S, U) Γ(X.left, X.hom ⁻¹ᵁ U)

/-- The open immersion `Spec A → X` over `S`. -/
def iotaX : Phi hU (Aalg X U) ⟶ X :=
  Over.homMk (isAffineOpen_preimage X hU).fromSpec
    (IsAffineOpen.SpecMap_appLE_fromSpec X.hom hU (isAffineOpen_preimage X hU) le_rfl).symm

instance : IsOpenImmersion (iotaX X hU).left :=
  inferInstanceAs (IsOpenImmersion (isAffineOpen_preimage X hU).fromSpec)

lemma range_iotaX : Set.range (iotaX X hU).left = X.hom ⁻¹ᵁ U :=
  (isAffineOpen_preimage X hU).range_fromSpec

/-- For `T` over `U`, morphisms to `X` are morphisms to the chart. -/
def toChart (T : Over S) (hT : LiesOver T U) : (T ⟶ X) ≃ (T ⟶ Phi hU (Aalg X U)) where
  toFun f := Over.homMk (IsOpenImmersion.lift (iotaX X hU).left f.left (by
      rw [range_iotaX]
      rintro _ ⟨x, rfl⟩
      change X.hom (f.left x) ∈ U
      rw [← Scheme.Hom.comp_apply, Over.w f]
      exact hT.mem x)) (by
    rw [← cancel_epi (𝟙 _)]
    have := Over.w (iotaX X hU)
    rw [Category.id_comp, ← this]
    rw [IsOpenImmersion.lift_fac_assoc]
    exact Over.w f)
  invFun g := g ≫ iotaX X hU
  left_inv f := by
    refine Over.OverMorphism.ext ?_
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv g := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (iotaX X hU).left]
    exact IsOpenImmersion.lift_fac _ _ _

/-- **`Hom_S(T, X) = Hom_R(A, Γ(T, ⊤))`** for `T` over `U`, `U` affine, `X → S` affine. -/
def ptX (T : Over S) (hT : LiesOver T U) : (T ⟶ X) ≃ (Aalg X U →ₐ[Γ(S, U)] Ga hU T hT) :=
  (toChart X hU T hT).trans (homPhi hU T hT _)

lemma ptX_comp {T T' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U) (s : T' ⟶ T) (f : T ⟶ X) :
    ptX X hU T' hT' (s ≫ f) = (gpull hU hT hT' s).comp (ptX X hU T hT f) := by
  have h : toChart X hU T' hT' (s ≫ f) = s ≫ toChart X hU T hT f := by
    apply (toChart X hU T' hT').symm.injective
    rw [Equiv.symm_apply_apply]
    change _ = (s ≫ _) ≫ iotaX X hU
    rw [Category.assoc]
    congr 1
    exact ((toChart X hU T hT).symm_apply_apply f).symm
  change homPhi hU T' hT' _ (toChart X hU T' hT' (s ≫ f)) = _
  rw [h, homPhi_comp hU hT hT']
  rfl

lemma ptX_symm_comp {T T' : Over S} (hT : LiesOver T U) (hT' : LiesOver T' U) (s : T' ⟶ T)
    (g : Aalg X U →ₐ[Γ(S, U)] Ga hU T hT) :
    (ptX X hU T' hT').symm ((gpull hU hT hT' s).comp g) = s ≫ (ptX X hU T hT).symm g := by
  apply (ptX X hU T' hT').injective
  rw [Equiv.apply_symm_apply, ptX_comp X hU hT hT', Equiv.apply_symm_apply]

lemma ptX_PhiMap_comp {D D' : CommAlgCat.{u} Γ(S, U)} (t : D →ₐ[Γ(S, U)] D') (f : Phi hU D ⟶ X) :
    ptX X hU _ (liesOver_Phi hU D') (PhiMap hU t ≫ f) =
      (gpull hU (liesOver_Phi hU D) (liesOver_Phi hU D') (PhiMap hU t)).comp
        (ptX X hU _ (liesOver_Phi hU D) f) :=
  ptX_comp X hU _ _ _ _

end X

end AlgMag.GB
