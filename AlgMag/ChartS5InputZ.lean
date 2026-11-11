/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5EA
import AlgMag.ChartSection5

/-!
# Chart lemma, Artin approximation step: closed subschemes of an affine `T`, on the site

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

`Zc I = V(I) ⊂ T`, `Γ(Zc I) = Γ(T)/I`, maps into it; site maps to an affine object from ring maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `Γ(S) → Γ(T')` is compatible with `T' → T`. -/
lemma top_comp {T' T : BigFppfOver B S hS} (a : T' ⟶ T) (s : RT (siteTop (B := B) (S := S) (hS := hS))) :
    ((BigFppfOver.toScheme B S hS).map a).appTop.hom
      (((BigFppfOver.toScheme B S hS).map (toTop' T)).appTop.hom s) =
    ((BigFppfOver.toScheme B S hS).map (toTop' T')).appTop.hom s := by
  have e3 : a ≫ toTop' T = toTop' T' := Over.mkIdTerminal.hom_ext _ _
  have e4 := congrArg (fun z : T' ⟶ siteTop (B := B) (S := S) (hS := hS) =>
    ((BigFppfOver.toScheme B S hS).map z).appTop.hom s) e3
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at e4
  exact e4

/-- A ring map over `Γ(S)` to an affine object is a map of the site. -/
noncomputable def siteOfRing [hSa : IsAffine S] {T' V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj T', ⊤))
    (hg : ∀ s, g (((BigFppfOver.toScheme B S hS).map (toTop' V)).appTop.hom s) =
      ((BigFppfOver.toScheme B S hS).map (toTop' T')).appTop.hom s) : T' ⟶ V :=
  haveI : IsAffine (B.obj hS).obj := hSa
  haveI : IsAffine (Over.left V).obj := ‹IsAffine ((BigFppfOver.toScheme B S hS).obj V)›
  Over.homMk ⟨ChartMain.toAffine (T := (BigFppfOver.toScheme B S hS).obj T')
      (U := (BigFppfOver.toScheme B S hS).obj V) g⟩ (by
    apply InducedCategory.hom_ext
    have hT : ∀ Y : BigFppfOver B S hS, Y.hom.hom = (BigFppfOver.toScheme B S hS).map (toTop' Y) :=
      fun Y => (congrArg (fun z => z.hom) (Over.w (toTop' Y))).symm.trans (Category.comp_id _)
    refine ChartMain.toAffine_comp V.hom.hom _ _ (RingHom.ext fun s => ?_)
    rw [RingHom.comp_apply, hT V, hT T']
    exact hg s)

lemma siteOfRing_appTop [hSa : IsAffine S] {T' V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (g : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj T', ⊤))
    (hg : ∀ s, g (((BigFppfOver.toScheme B S hS).map (toTop' V)).appTop.hom s) =
      ((BigFppfOver.toScheme B S hS).map (toTop' T')).appTop.hom s) :
    ((BigFppfOver.toScheme B S hS).map (siteOfRing g hg)).appTop.hom = g :=
  ChartMain.toAffine_appTop (T := (BigFppfOver.toScheme B S hS).obj T')
      (U := (BigFppfOver.toScheme B S hS).obj V) g

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- `V(I) ⊂ T`. -/
noncomputable abbrev Zc (I : Ideal (RT T)) : BigFppfOver B S hS :=
  Chart.immObj T (Chart.closedι ((BigFppfOver.toScheme B S hS).obj T) I)

/-- `V(I) → T`. -/
noncomputable abbrev Zi (I : Ideal (RT T)) : Zc T I ⟶ T :=
  Chart.immι T (Chart.closedι ((BigFppfOver.toScheme B S hS).obj T) I)

instance Zc_affine (I : Ideal (RT T)) : IsAffine ((BigFppfOver.toScheme B S hS).obj (Zc T I)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- `Γ(T) → Γ(V(I))`. -/
noncomputable abbrev rZ (I : Ideal (RT T)) :
    RT T →+* Γ((BigFppfOver.toScheme B S hS).obj (Zc T I), ⊤) :=
  ((BigFppfOver.toScheme B S hS).map (Zi T I)).appTop.hom

lemma rZ_surjective (I : Ideal (RT T)) : Function.Surjective (rZ T I) := by
  have h : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (Zi T I)) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι _ I))
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map (Zi T I))).2

lemma rZ_eq_zero_iff (I : Ideal (RT T)) (c : RT T) : rZ T I c = 0 ↔ c ∈ I :=
  ⟨fun h => Chart.closedι_appTop_eq_zero I c h, fun h => closedι_appTop_of_mem I c h⟩

/-- `Γ(T)/I ≃ Γ(V(I))`. -/
noncomputable def zE (I : Ideal (RT T)) :
    (RT T ⧸ I) ≃+* Γ((BigFppfOver.toScheme B S hS).obj (Zc T I), ⊤) :=
  RingEquiv.ofBijective (Ideal.Quotient.lift I (rZ T I) fun c hc => (rZ_eq_zero_iff T I c).2 hc) (by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((rZ_eq_zero_iff T I c).1 hy)
    · intro y
      obtain ⟨c, rfl⟩ := rZ_surjective T I y
      exact ⟨Ideal.Quotient.mk _ c, rfl⟩)

@[simp] lemma zE_mk (I : Ideal (RT T)) (c : RT T) : zE T I (Ideal.Quotient.mk I c) = rZ T I c := rfl

variable {T} [hSa : IsAffine S]

/-- The ring map underlying `zLift`. -/
noncomputable def zRing (I : Ideal (RT T)) {T' : BigFppfOver B S hS} (a : T' ⟶ T)
    (ha : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) :
    Γ((BigFppfOver.toScheme B S hS).obj (Zc T I), ⊤) →+* Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) :=
  (Ideal.Quotient.lift I ((BigFppfOver.toScheme B S hS).map a).appTop.hom ha).comp
    ((zE T I).symm : _ →+* _)

lemma zRing_rZ (I : Ideal (RT T)) {T' : BigFppfOver B S hS} (a : T' ⟶ T)
    (ha : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) (c : RT T) :
    zRing I a ha (rZ T I c) = ((BigFppfOver.toScheme B S hS).map a).appTop.hom c := by
  have e : (zE T I).symm (rZ T I c) = Ideal.Quotient.mk I c := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change Ideal.Quotient.lift I _ ha ((zE T I).symm (rZ T I c)) = _
  rw [e]; rfl

/-- A map to `T` killing `I` factors through `V(I)`. -/
noncomputable def zLift (I : Ideal (RT T)) {T' : BigFppfOver B S hS} (a : T' ⟶ T)
    (ha : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) : T' ⟶ Zc T I :=
  siteOfRing (zRing I a ha) (fun s => by
    rw [← top_comp (Zi T I) s, zRing_rZ, top_comp])

lemma zLift_appTop (I : Ideal (RT T)) {T' : BigFppfOver B S hS} (a : T' ⟶ T)
    (ha : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) (c : RT T) :
    ((BigFppfOver.toScheme B S hS).map (zLift I a ha)).appTop.hom (rZ T I c) =
      ((BigFppfOver.toScheme B S hS).map a).appTop.hom c := by
  rw [zLift, siteOfRing_appTop, zRing_rZ]

lemma zLift_ι (I : Ideal (RT T)) {T' : BigFppfOver B S hS} (a : T' ⟶ T)
    (ha : ∀ c ∈ I, ((BigFppfOver.toScheme B S hS).map a).appTop.hom c = 0) :
    zLift I a ha ≫ Zi T I = a := by
  refine ChartMain.siteExt (ChartMain.toAffine_ext (RingHom.ext fun c => ?_))
  rw [Functor.map_comp, Scheme.Hom.comp_appTop]
  exact zLift_appTop I a ha c

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.zLift_ι
