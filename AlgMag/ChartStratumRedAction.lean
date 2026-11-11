/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumChart
import AlgMag.ChartStratumReduced
import StacksFrontier.AlgebraicGeometry.Spaces.Reduction

/-!
# The action on the reduction (affine stratum lemma, step 1)

If the torsion of `M` is killed by an integer invertible on `X`, then `D(M)` preserves `X_red`: the map
`D(M) × V → X` has reduced source for every reduced chart `V`, and a map from a reduced scheme lands
in `X_red`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `𝔸(P)_T` is reduced if `Γ(T')[P]` is for the affine opens `T'` of `T`. -/
theorem isReduced_monAff {P : Type u} [AddCommMonoid P] (T : Scheme.{u})
    (h : ∀ (T' : Scheme.{u}) (j : T' ⟶ T) [IsAffine T'] [IsReduced T'] [IsOpenImmersion j],
      IsReduced (AddMonoidAlgebra Γ(T', ⊤) P))
    [IsReduced T] : IsReduced (MonAff P T) := by
  let 𝒰 : T.OpenCover := T.affineOpenCover.openCover
  have hopen : ∀ a, IsOpenImmersion (MonAff.map (P := P) (𝒰.f a)) := fun a =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (MonAff.isPullback_map (𝒰.f a)).flip
      inferInstance
  have hred : ∀ a, IsReduced (MonAff P (𝒰.X a)) := fun a => by
    have : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
    have : IsReduced (𝒰.X a) := isReduced_of_isOpenImmersion (𝒰.f a)
    have := h (𝒰.X a) (𝒰.f a)
    have hS : IsReduced (Spec (.of (AddMonoidAlgebra Γ(𝒰.X a, ⊤) P))) := inferInstance
    exact isReduced_of_isOpenImmersion (MonAff.isoOfIsAffine P (𝒰.X a)).hom
  have hst : ∀ x : MonAff P T, _root_.IsReduced ((MonAff P T).presheaf.stalk x) := by
    intro x
    obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (MonAff.π P T x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    have hp := MonAff.isPullback_map (P := P) (𝒰.f a)
    let w := hp.isoPullback.inv z
    have hw : MonAff.map (P := P) (𝒰.f a) w = x := by
      rw [← hz, ← Scheme.Hom.comp_apply, hp.isoPullback_inv_fst]
    subst hw
    have := hred a
    have := hopen a
    exact isReduced_of_injective ((MonAff.map (P := P) (𝒰.f a)).stalkMap w).hom
      (ConcreteCategory.bijective_of_isIso ((MonAff.map (P := P) (𝒰.f a)).stalkMap w)).1
  exact isReduced_of_isReduced_stalk _

/-- A map from a reduced scheme lands in any closed subspace with all the points. -/
theorem mem_of_isReduced {G : Subfunctor X} (hX : IsAlgebraicSpace B S hS X)
    (hcl : Space.IsClosedSubspace B S hS G)
    (hsurj : Function.Surjective (Space.pointsMap B S hS G.toFunctor G.ι))
    {T : BigFppfOver B S hS} (hT : IsReduced ((SCH).obj T)) (x : X.obj (op T)) :
    x ∈ G.obj (op T) := by
  let a : yoneda.obj T ⟶ X := yonedaEquiv.symm x
  have hrep := hcl.2.rep
  let s := hrep.snd a
  have sq := hrep.isPullback a
  have hs : AlgebraicGeometry.IsClosedImmersion ((SCH).map s) := hcl.2.property_snd a
  have hWa := isAlgebraicSpace_yoneda B S hS (hrep.pullback a)
  let cG : AlgebraicSpaces B S hS := ⟨_, hcl.1⟩
  let cX : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let cT : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let cW : AlgebraicSpaces B S hS := ⟨_, hWa⟩
  let f1 : cW ⟶ cG := ObjectProperty.homMk (hrep.fst a)
  let f2 : cW ⟶ cT := ObjectProperty.homMk (yoneda.map s)
  let f3 : cG ⟶ cX := ObjectProperty.homMk G.ι
  let f4 : cT ⟶ cX := ObjectProperty.homMk a
  have sq' : IsPullback f1 f2 f3 f4 :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hps : Space.IsSurjective B S hS (yoneda.map s) :=
    Space.isSurjective_of_isPullback B S hS sq' hsurj
  have hsS : Surjective ((SCH).map s) := (MorphismProperty.relative_map_iff (F := yoneda)
    (P := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))).mp
      ((Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS s).mpr hps)
  have hiso : IsIso ((SCH).map s) := isIso_of_isClosedImmersion_of_surjective _
  have hiso' : IsIso s := isIso_of_reflects_iso s (SCH)
  let y : G.toFunctor.obj (op T) := yonedaEquiv (yoneda.map (inv s) ≫ hrep.fst a)
  have hy : (y : X.obj (op T)) = x := by
    have e : (yoneda.map (inv s) ≫ hrep.fst a) ≫ G.ι = a := by
      rw [Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
      simp
    have e2 : ((y : X.obj (op T))) = yonedaEquiv ((yoneda.map (inv s) ≫ hrep.fst a) ≫ G.ι) := by
      rw [yonedaEquiv_comp]; rfl
    rw [e2, e]
    exact yonedaEquiv.apply_symm_apply x
  rw [← hy]
  exact y.2

section Act

variable {M : Type u} [AddCommGroup M] [Countable M] [AddGroup.FG M]

/-- `𝔸(⊤)_V` is reduced for `V` reduced with torsion of `M` killed by a unit. -/
theorem isReduced_top {V : Scheme.{u}} [IsReduced V] (N : ℕ) (hN : IsUnit (N : Γ(V, ⊤)))
    (ht : ∀ x : M, IsOfFinAddOrder x → N • x = 0) :
    IsReduced (MonAff (⊤ : AddSubgroup M).toAddSubmonoid V) := by
  refine isReduced_monAff V fun T' j _ _ _ => ?_
  have hN' : IsUnit (N : Γ(T', ⊤)) := by
    have := hN.map j.appTop.hom
    rwa [map_natCast] at this
  have h1 := isReduced_addMonoidAlgebra (R := Γ(T', ⊤)) (G := M) N hN' ht
  let e : (⊤ : AddSubgroup M).toAddSubmonoid ≃+ M :=
    { toFun := fun x => x.1
      invFun := fun y => ⟨y, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact isReduced_of_injective
    (AddMonoidAlgebra.domCongr Γ(T', ⊤) Γ(T', ⊤) e).toRingEquiv.toRingHom
    (AddMonoidAlgebra.domCongr Γ(T', ⊤) Γ(T', ⊤) e).toRingEquiv.injective

/-- **Affine stratum lemma, step 1**: `D(M)` preserves the reduction when the torsion of `M` is killed by an
integer invertible on `X`. -/
theorem smul_mem_reduction (act : AAction (fppfO B S hS) M X) (hX : IsAlgebraicSpace B S hS X)
    (N : ℕ) (hN : ∀ (T : BigFppfOver B S hS) (_ : X.obj (op T)), IsUnit (N : Γ((SCH).obj T, ⊤)))
    (ht : ∀ x : M, IsOfFinAddOrder x → N • x = 0)
    {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) {x : X.obj (op T)}
    (hx : x ∈ (Space.reduction B S hS X hX).obj (op T)) :
    act.smul h x ∈ (Space.reduction B S hS X hX).obj (op T) := by
  let Rd := Space.reduction B S hS X hX
  have hcl : Space.IsClosedSubspace B S hS Rd :=
    (Space.isAlgebraicSpaceStructure_reduction B S hS X hX).isClosedSubspace
  have hsurj := Space.surjective_pointsMap_ι_reduction B S hS X hX
  obtain ⟨U₀, φ, hφs, hφe, hU₀⟩ := Space.hasEtaleLocalProperty_isReduced_reduction B S hS X hX
  have hRa : IsAlgebraicSpace B S hS Rd.toFunctor := hcl.1
  have hPB : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance
  let a : yoneda.obj T ⟶ Rd.toFunctor := yonedaEquiv.symm ⟨x, hx⟩
  have hU₀a := isAlgebraicSpace_yoneda B S hS U₀
  have hTa := isAlgebraicSpace_yoneda B S hS T
  have hP : IsAlgebraicSpace B S hS (pullback a φ) := isAlgebraicSpace_pullback B S hS _ _ hTa hU₀a hRa
  have hφE : Space.IsEtale B S hS φ := (Space.isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφe
  have hsq := IsPullback.of_hasPullback a φ
  obtain ⟨f1, l1⟩ := flat_lfp_bc hP hU₀a hTa hRa hsq.flip.flip.flip
    (Space.isFlat_of_isEtale B S hS hφE) (Space.isLocallyOfFinitePresentation_of_isEtale B S hS hφE)
  have hφS : Space.IsSurjective B S hS φ :=
    (Space.surjective_iff_surjective_pointsMap B S hS _ hRa U₀ φ).1 hφs
  have hSu : Space.IsSurjective B S hS (pullback.fst a φ) := by
    let cP : AlgebraicSpaces B S hS := ⟨_, hP⟩
    let cU : AlgebraicSpaces B S hS := ⟨_, hU₀a⟩
    let cT : AlgebraicSpaces B S hS := ⟨_, hTa⟩
    let cR : AlgebraicSpaces B S hS := ⟨_, hRa⟩
    let s1 : cP ⟶ cU := ObjectProperty.homMk (pullback.snd a φ)
    let s2 : cP ⟶ cT := ObjectProperty.homMk (pullback.fst a φ)
    let s3 : cU ⟶ cR := ObjectProperty.homMk φ
    let s4 : cT ⟶ cR := ObjectProperty.homMk a
    have sq' : IsPullback s1 s2 s3 s4 :=
      IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.flip.w) hsq.flip
    exact Space.isSurjective_of_isPullback B S hS sq' hφS
  obtain ⟨U, q, u, hu, hqF, hqL, hqS⟩ := exists_fppf_lift hP _ hSu f1 l1
  let t : U ⟶ U₀ := yoneda.preimage (u ≫ pullback.snd a φ)
  have htm : yoneda.map t = u ≫ pullback.snd a φ := yoneda.map_preimage _
  have hcomm : yoneda.map q ≫ a = yoneda.map t ≫ φ := by
    rw [← hu, htm, Category.assoc, Category.assoc, pullback.condition]
  let c₀ : X.obj (op U₀) := (φ.app (op U₀) (𝟙 U₀)).1
  have hxq : X.map q.op x = X.map t.op c₀ := by
    have e1 := congrArg (fun k : yoneda.obj U ⟶ Rd.toFunctor => (yonedaEquiv k).1) hcomm
    have l1 : (yonedaEquiv (yoneda.map q ≫ a)).1 = X.map q.op x := by
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      change (a.app (op U) q).1 = _
      rfl
    have l2 : (yonedaEquiv (yoneda.map t ≫ φ)).1 = X.map t.op c₀ := by
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      have := ConcreteCategory.congr_hom (φ.naturality t.op) (𝟙 U₀)
      have e3 : t = (yoneda.obj U₀).map t.op (𝟙 U₀) := by simp
      have e4 : φ.app (op U) t = Rd.toFunctor.map t.op (φ.app (op U₀) (𝟙 U₀)) := by
        exact (congrArg (φ.app (op U)) e3).trans this
      rw [e4]
      rfl
    exact l1.symm.trans (e1.trans l2)
  have hN' : B.Contains (Spec (ZMon (⊤ : AddSubgroup M).toAddSubmonoid)) :=
    contains_zmon_of_countable hS _
  let Un := monAffUniversal (⊤ : AddSubgroup M).toAddSubmonoid hN' U₀
  have hU₀r : IsReduced ((SCH).obj U₀) := hU₀
  have hred : IsReduced ((SCH).obj Un.P) :=
    isReduced_top (V := (SCH).obj U₀) N (hN U₀ c₀) ht
  let y₀ : X.obj (op Un.P) := act.smul (topPt Un.u) (X.map Un.π.op c₀)
  have hy₀ : y₀ ∈ Rd.obj (op Un.P) := mem_of_isReduced hX hcl hsurj hred y₀
  let l : U ⟶ Un.P := Un.lift t (ptTop (APt.res q.op h))
  have hl : l ≫ Un.π = t := Un.lift_π _ _
  have hl2 : APt.res l.op Un.u = ptTop (APt.res q.op h) := Un.res_lift _ _
  have hmap : X.map l.op y₀ = X.map q.op (act.smul h x) := by
    change X.map l.op (act.smul (topPt Un.u) (X.map Un.π.op c₀)) = _
    rw [act.map_smul, act.map_smul, ← topPt_res, hl2, topPt_ptTop, hxq, ← Functor.map_comp_apply,
      ← op_comp, hl]
  have hmU : X.map q.op (act.smul h x) ∈ Rd.obj (op U) := by
    rw [← hmap]; exact Rd.map l.op hy₀
  have hXsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf
  have hRsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) Rd.toFunctor :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hRa.isSheaf
  refine (Subfunctor.isSheaf_iff _ hXsh).1 hRsh (op T) _ ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqS hqF hqL)
  rintro T' f ⟨U', z, q', hq', rfl⟩
  cases hq'
  change X.map (z ≫ q).op _ ∈ Rd.obj (op T')
  rw [op_comp, Functor.map_comp_apply]
  exact Rd.map z.op hmU

end Act

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.smul_mem_reduction
