/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumIntegral
import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace

/-!
# From the reduction back to the space (affine stratum lemma, step 1)

A stable affine open of `X_red` for `D(M/K)` gives an open of `X` with the same points. It is affine by
Stacks 07VT, and stable under `D(M)` when `K` is killed at field points.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] Space.pointTopology

/-- A point `y` over a field whose class lies in the image of an open immersion factors through it. -/
theorem exists_lift_of_field {Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hY : IsAlgebraicSpace B S hS Y) (f : U ⟶ Y)
    (hf : Space.IsOpenImmersion B S hS f) {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (y : Y.obj (op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))))
    (hc : (Space.FieldValuedPoint.class B S hS Y ⟨k, hk, b, y⟩) ∈
      Set.range (Space.pointsMap B S hS U f)) :
    ∃ t, f.app _ t = y := by
  let T : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
  have hop := Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS f hf
  have hH := Space.isOpenSubspace_openSubspaceOfPoints B S hS hY _ hop
  have hR := Space.isOpenSubspace_subfunctorRange B S hS hU hf
  have hle : Space.openSubspaceOfPoints B S hS Y (Set.range (Space.pointsMap B S hS U f)) ≤
      Subfunctor.range f := by
    refine Space.le_of_range_pointsMap_ι_subset B S hS hR ?_
    rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
    rintro _ ⟨a, rfl⟩
    refine ⟨Space.pointsMap B S hS U (Subfunctor.toRange f) a, ?_⟩
    rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
  have hsub : Subsingleton (Space.points B S hS (yoneda.obj T)) := by
    have : Subsingleton ((SCH).obj T) := inferInstanceAs (Subsingleton (Spec (.of k)))
    exact (Space.pointsEquivScheme B S hS T).subsingleton
  have hmem : y ∈ (Space.openSubspaceOfPoints B S hS Y
      (Set.range (Space.pointsMap B S hS U f))).obj (op T) := by
    rw [Space.mem_openSubspaceOfPoints_iff]
    rintro _ ⟨z, rfl⟩
    have hz : z = Space.FieldValuedPoint.class B S hS (yoneda.obj T) ⟨k, hk, b, 𝟙 T⟩ :=
      Subsingleton.elim _ _
    subst hz
    have e : (yonedaEquiv.symm y).app (op T) (𝟙 T) = y := by
      change Y.map (𝟙 T).op y = y
      rw [op_id, CategoryTheory.Functor.map_id]; rfl
    change Space.FieldValuedPoint.class B S hS Y ⟨k, hk, b, (yonedaEquiv.symm y).app (op T) (𝟙 T)⟩ ∈ _
    rw [e]
    exact hc
  obtain ⟨t, ht⟩ := hle _ hmem
  exact ⟨t, ht⟩

/-- **Affine stratum lemma, step 1**: from `X_red` back to `X`. -/
theorem exists_stable_open_of_reduction (actZ : AAction (fppfO B S hS) M Z)
    (hZ : IsAlgebraicSpace B S hS Z) (K : AddSubgroup M)
    (act2 : AAction (fppfO B S hS) (M ⧸ K) (Space.reduction B S hS Z hZ).toFunctor)
    (hact2 : IsEquivariant act2 (actZ.comap (QuotientAddGroup.mk' K)) (Space.reduction B S hS Z hZ).ι)
    (hK : ∀ {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
      (_ : Z.obj (op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))))
      (h : APt (fppfO B S hS) M (op (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))), TrivialOn K h)
    {U' : BigFppfOver B S hS} (actU' : AAction (fppfO B S hS) (M ⧸ K) (yoneda.obj U'))
    (f' : yoneda.obj U' ⟶ (Space.reduction B S hS Z hZ).toFunctor)
    (hU'a : IsAffine ((SCH).obj U')) (hU'n : Nonempty ((SCH).obj U'))
    (hf'e : IsEquivariant actU' act2 f') (hf'o : Space.IsOpenImmersion B S hS f') :
    ∃ G : Subfunctor Z, Space.IsOpenSubspace B S hS G ∧ Space.IsAffineSpace B S hS G.toFunctor ∧
      (∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (G.obj (op W))) ∧
      ∀ {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) {x : Z.obj (op T)},
        x ∈ G.obj (op T) → actZ.smul h x ∈ G.obj (op T) := by
  classical
  let Rd := Space.reduction B S hS Z hZ
  have hcl : Space.IsClosedSubspace B S hS Rd :=
    (Space.isAlgebraicSpaceStructure_reduction B S hS Z hZ).isClosedSubspace
  have hRsurj := Space.surjective_pointsMap_ι_reduction B S hS Z hZ
  have hRinj := Space.pointsMap_injective_of_mono B S hS Rd.ι
  have hRclosed : IsClosedMap (Space.pointsMap B S hS _ Rd.ι) :=
    Space.isClosed_of_universallyClosed B S hS hZ Rd.ι
      (Space.universallyClosed_of_isClosedImmersion B S hS hcl.1 hZ Rd.ι hcl.2)
  have hU'a' := isAlgebraicSpace_yoneda B S hS U'
  let W₀ := Set.range (Space.pointsMap B S hS _ f')
  let Gset := Space.pointsMap B S hS _ Rd.ι '' W₀
  have hW₀o : IsOpen W₀ := Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS f' hf'o
  have hGopen : IsOpen Gset := by
    have : Gset = (Space.pointsMap B S hS _ Rd.ι '' W₀ᶜ)ᶜ := by
      rw [Set.image_compl_eq ⟨hRinj, hRsurj⟩, compl_compl]
    rw [this]
    exact (hRclosed _ hW₀o.isClosed_compl).isOpen_compl
  let G := Space.openSubspaceOfPoints B S hS Z Gset
  have hG : Space.IsOpenSubspace B S hS G :=
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hZ _ hGopen
  have hGr : Set.range (Space.pointsMap B S hS G.toFunctor G.ι) = Gset :=
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _
  -- the preimage of `G` in `X_red` is `U'`
  have hPre : Space.IsOpenSubspace B S hS (G.preimage Rd.ι) :=
    Space.isOpenSubspace_preimage B S hS Rd.ι G hZ hcl.1 hG
  have hR := Space.isOpenSubspace_subfunctorRange B S hS hU'a' hf'o
  have hrr : Set.range (Space.pointsMap B S hS _ (Subfunctor.range f').ι) = W₀ := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a, rfl⟩
      have hmf : Mono f' := Space.mono_of_isOpenImmersion B S hS f' hf'o
      have hι : inv (Subfunctor.toRange f') ≫ f' = (Subfunctor.range f').ι :=
        (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι f').symm
      refine ⟨Space.pointsMap B S hS _ (inv (Subfunctor.toRange f')) a, ?_⟩
      rw [← Space.pointsMap_comp_apply, hι]
    · rintro _ ⟨a, rfl⟩
      refine ⟨Space.pointsMap B S hS _ (Subfunctor.toRange f') a, ?_⟩
      rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]
  have hpreq : G.preimage Rd.ι = Subfunctor.range f' := by
    apply le_antisymm
    · refine Space.le_of_range_pointsMap_ι_subset B S hS hR ?_
      rw [Space.pointsRange_preimage, hGr, hRinj.preimage_image, hrr]
    · refine Space.le_of_range_pointsMap_ι_subset B S hS hPre ?_
      rw [Space.pointsRange_preimage, hGr, hRinj.preimage_image, hrr]
  have hmf : Mono f' := Space.mono_of_isOpenImmersion B S hS f' hf'o
  have sq : IsPullback (G.fromPreimage Rd.ι) (G.preimage Rd.ι).ι G.ι Rd.ι :=
    Subfunctor.isPullback_preimage Rd.ι G
  have hci : Space.IsClosedImmersion B S hS (G.fromPreimage Rd.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq.flip hcl.2
  have hsrc : Space.IsAffineSpace B S hS (G.preimage Rd.ι).toFunctor := by
    rw [hpreq]
    exact ⟨U', hU'a, ⟨(asIso (Subfunctor.toRange f')).symm⟩⟩
  have hsurj : Space.IsSurjective B S hS (G.fromPreimage Rd.ι) := by
    let c1 : AlgebraicSpaces B S hS := ⟨_, hPre.1⟩
    let c2 : AlgebraicSpaces B S hS := ⟨_, hcl.1⟩
    let c3 : AlgebraicSpaces B S hS := ⟨_, hG.1⟩
    let c4 : AlgebraicSpaces B S hS := ⟨_, hZ⟩
    let s1 : c1 ⟶ c2 := ObjectProperty.homMk (G.preimage Rd.ι).ι
    let s2 : c1 ⟶ c3 := ObjectProperty.homMk (G.fromPreimage Rd.ι)
    let s3 : c2 ⟶ c4 := ObjectProperty.homMk Rd.ι
    let s4 : c3 ⟶ c4 := ObjectProperty.homMk G.ι
    have sq' : IsPullback s1 s2 s3 s4 :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.flip.w) sq.flip
    exact Space.isSurjective_of_isPullback B S hS sq' hRsurj
  refine ⟨G, hG, Space.isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS _ hPre.1 hG.1 hci
    hsurj hsrc, ?_, ?_⟩
  · refine ⟨U', hU'n, ?_⟩
    have hm : f'.app (op U') (𝟙 U') ∈ (G.preimage Rd.ι).obj (op U') := by
      rw [hpreq]; exact ⟨𝟙 U', rfl⟩
    exact ⟨⟨_, hm⟩⟩
  · intro T h x hx
    rw [Space.mem_openSubspaceOfPoints_iff]
    rintro _ ⟨z, rfl⟩
    induction z using Quot.ind with
    | mk p =>
    rcases p with ⟨k, hk, b, τ⟩
    let T₀ : BigFppfOver B S hS := Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)
    let τ' : T₀ ⟶ T := τ
    let y : Z.obj (op T₀) := Z.map τ'.op x
    have hyG : y ∈ G.obj (op T₀) := G.map τ'.op hx
    have hcG : Space.FieldValuedPoint.class B S hS Z ⟨k, hk, b, y⟩ ∈ Gset := by
      have h1 := (Space.mem_openSubspaceOfPoints_iff B S hS _ y).1 hyG
      have e : (yonedaEquiv.symm y).app (op T₀) (𝟙 T₀) = y := by
        change Z.map (𝟙 T₀).op y = y
        rw [op_id, CategoryTheory.Functor.map_id]; rfl
      have h2 := h1 ⟨Space.FieldValuedPoint.class B S hS (yoneda.obj T₀) ⟨k, hk, b, 𝟙 T₀⟩, rfl⟩
      change Space.FieldValuedPoint.class B S hS Z ⟨k, hk, b, (yonedaEquiv.symm y).app (op T₀) (𝟙 T₀)⟩ ∈ _ at h2
      rwa [e] at h2
    have hredT : IsReduced ((SCH).obj T₀) := inferInstanceAs (IsReduced (Spec (.of k)))
    have hyR : y ∈ Rd.obj (op T₀) := mem_of_isReduced hZ hcl hRsurj hredT y
    obtain ⟨w, hw, hwe⟩ := hcG
    have hcR : Space.FieldValuedPoint.class B S hS Rd.toFunctor ⟨k, hk, b, ⟨y, hyR⟩⟩ ∈ W₀ := by
      have : w = Space.FieldValuedPoint.class B S hS Rd.toFunctor ⟨k, hk, b, ⟨y, hyR⟩⟩ :=
        hRinj hwe
      exact this ▸ hw
    obtain ⟨t, ht⟩ := exists_lift_of_field hU'a' hcl.1 f' hf'o hk b ⟨y, hyR⟩ hcR
    let h₀ : APt (fppfO B S hS) M (op T₀) := APt.res τ'.op h
    obtain ⟨k₀, hk₀⟩ := exists_quotient_of_trivialOn (hK hk b y h₀)
    let t' := actU'.smul k₀ t
    have ey : Rd.ι.app (op T₀) (f'.app (op T₀) t') = Z.map τ'.op (actZ.smul h x) := by
      rw [actZ.map_smul]
      change Rd.ι.app (op T₀) (f'.app (op T₀) (actU'.smul k₀ t)) = _
      rw [hf'e, hact2, ht]
      change actZ.smul (k₀.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' K))) y = _
      rw [hk₀]
    refine ⟨Space.pointsMap B S hS _ f' (Space.FieldValuedPoint.class B S hS (yoneda.obj U') ⟨k, hk, b, t'⟩),
      ⟨_, rfl⟩, ?_⟩
    change Space.FieldValuedPoint.class B S hS Z ⟨k, hk, b, Rd.ι.app (op T₀) (f'.app (op T₀) t')⟩ =
      Space.FieldValuedPoint.class B S hS Z ⟨k, hk, b, Z.map τ'.op (actZ.smul h x)⟩
    rw [ey]

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_stable_open_of_reduction
