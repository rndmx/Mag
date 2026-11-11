/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAtlas
import AlgMag.FinalFact334
import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# Fact 3.34 (ii), Theorem 15.3 for `X` not quasi-compact

Fix an affine `T` and `t ∈ X^N(T)`, all `N` in the family. The finite-degree step of `fact334_strong` needs finitely many charts,
chosen before the finite subfamily `J` is. They are the charts over the vertex point `v` of `X^{N^×}`, and `v` does not depend on
`J`: among the finite intersections, take `K` with `rank K^×` minimal. For `L ≤ K` in the family, `K^×/L^×` is torsion, so
`L ∩ K^× = L^×` (`neg_mem_of_nsmul`), so the vertex of `𝔸(L)` is the image of the vertex of `𝔸(K)`. `M` is a finitely generated
abelian group.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- Submodules of a finitely generated abelian group with `B ≤ A` of the same rank: `A / B` is torsion. -/
theorem torsion_of_finrank_eq [AddGroup.FG M] {A C : Submodule ℤ M} (h : C ≤ A)
    (e : Module.finrank ℤ C = Module.finrank ℤ A) {n : M} (hn : n ∈ A) :
    ∃ d : ℕ, d ≠ 0 ∧ d • n ∈ C := by
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.2 inferInstance
  let C' : Submodule ℤ A := C.comap A.subtype
  have h1 := Submodule.finrank_quotient_add_finrank C'
  have h2 : Module.finrank ℤ C' = Module.finrank ℤ C :=
    (Submodule.comapSubtypeEquivOfLe h).finrank_eq
  have h3 : Module.finrank ℤ (A ⧸ C') = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h3) (Submodule.Quotient.mk ⟨n, hn⟩)
  have h4 : a • n ∈ C := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
    exact hax
  have key : ∀ k : ℕ, (a = k ∨ a = -k) → k • n ∈ C := by
    rintro k (rfl | rfl)
    · simpa using h4
    · simpa using C.neg_mem h4
  exact ⟨a.natAbs, Int.natAbs_ne_zero.2 ha, key _ (Int.natAbs_eq a)⟩

lemma unitsSubgroup_mono {L K : AddSubmonoid M} (h : L ≤ K) : unitsSubgroup L ≤ unitsSubgroup K := by
  rintro x ⟨hx, y, hy, e⟩
  exact ⟨h hx, y, h hy, e⟩

/-- Among the finite intersections of a family, one whose units have minimal rank: its units meet each smaller intersection in the
units of that one. -/
theorem exists_units_min [AddGroup.FG M] {s : Set (AddSubmonoid M)} (hne : s.Nonempty) :
    ∃ J₀ ⊆ s, J₀.Finite ∧ J₀.Nonempty ∧ ∀ J ⊆ s, J.Finite → J₀ ⊆ J → ∀ n ∈ sInf J,
      n ∈ unitsSubgroup (sInf J₀) → n ∈ unitsSubgroup (sInf J) := by
  classical
  haveI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.2 inferInstance
  let rk : Set (AddSubmonoid M) → ℕ := fun J =>
    Module.finrank ℤ (AddSubgroup.toIntSubmodule (unitsSubgroup (sInf J)))
  have hex : ∃ k, ∃ J ⊆ s, J.Finite ∧ J.Nonempty ∧ rk J = k := by
    obtain ⟨N, hN⟩ := hne
    exact ⟨_, {N}, by simpa using hN, Set.finite_singleton _, Set.singleton_nonempty _, rfl⟩
  obtain ⟨J₀, hJs, hJf, hJn, hk⟩ := Nat.find_spec hex
  refine ⟨J₀, hJs, hJf, hJn, fun J hJ hJ' hsub n hnJ hn => ?_⟩
  have hle : unitsSubgroup (sInf J) ≤ unitsSubgroup (sInf J₀) :=
    unitsSubgroup_mono (sInf_le_sInf hsub)
  have hne' : J.Nonempty := hJn.mono hsub
  have e : rk J = rk J₀ := by
    refine le_antisymm (Submodule.finrank_mono (AddSubgroup.toIntSubmodule.monotone hle)) ?_
    rw [hk]
    exact Nat.find_min' hex ⟨J, hJ, hJ', hne', rfl⟩
  obtain ⟨d, hd, hdn⟩ := torsion_of_finrank_eq (AddSubgroup.toIntSubmodule.monotone hle) e
    (n := n) hn
  have hneg : -(d • n) ∈ sInf J := by
    have h2 : d • n ∈ unitsSubgroup (sInf J) := hdn
    exact ((unitsSubgroup (sInf J)).neg_mem h2).1
  exact ⟨hnJ, -n, neg_mem_of_nsmul hnJ hd hneg, add_neg_cancel n⟩

/-- For `L ≤ K` with `L ∩ K^× = L^×`, the vertex of `𝔸(L)` is the image of the vertex of `𝔸(K)`. -/
theorem vertex_eq [AddMonoid.FG M] {act : AAction (fppfO B S hS) M X} {L K : AddSubmonoid M} (h : L ≤ K)
    (hu : ∀ n ∈ L, n ∈ unitsSubgroup K → n ∈ unitsSubgroup L) {T : BigFppfOver B S hS}
    (ψ : AttractorPt act L T) :
    (AttractorPt.ofFace (isFace_units K) (AttractorPt.ofLE h ψ)).toPoint =
      (AttractorPt.ofFace (isFace_units L) ψ).toPoint := by
  have e : ∀ {U : (BigFppfOver B S hS)ᵒᵖ},
      APt.restrict h (APt.faceExt (isFace_units K) (1 : APt (fppfO B S hS) _ U)) =
        APt.faceExt (isFace_units L) (1 : APt (fppfO B S hS) _ U) := by
    intro U
    refine MonoidHom.ext fun (n : Multiplicative L) => ?_
    change APt.faceExt (isFace_units K) (1 : APt (fppfO B S hS) _ U)
      ((AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) n) = _
    by_cases hn : ((Multiplicative.toAdd n : L) : M) ∈ (unitsSubgroup L).toAddSubmonoid
    · refine (APt.faceExt_pos (isFace_units K) _ (unitsSubgroup_mono h hn)).trans ?_
      rw [APt.faceExt_pos (isFace_units L) _ hn]
      rfl
    · exact (APt.faceExt_neg (isFace_units K) _
        (fun hk => hn (hu _ (Multiplicative.toAdd n : L).2 hk))).trans
        (APt.faceExt_neg (isFace_units L) _ hn).symm
  exact congrArg (ψ.app _) e

variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- The geometric step of `exists_atlas_lift_of_isZFPR` for one chart, not surjective: a point `x` of `X^L` with vertex `v` lifts
over the pullback of the chart along `v`. -/
theorem chart_lift [AddMonoid.FG M] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {L : AddSubmonoid M} (hl : IsLimitPreserving X) (heq : IsEquivariant aU aX f)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hZ : IsZFPR heq (unitsSubgroup L)) {T : BigFppfOver B S hS} (x : AttractorPt aX L T)
    {v : X.obj (op T)} (hv : (AttractorPt.ofFace (isFace_units L) x).toPoint = v) :
    ∃ w : AttractorPt aU L (het.rep.pullback (yonedaEquiv.symm v)),
      AttractorPt.push ⟨f, heq⟩ w = AttractorPt.baseChange (het.rep.snd (yonedaEquiv.symm v)) x := by
  subst hv
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  let F : EquivariantHom aU aX := ⟨f, heq⟩
  let Z := unitsSubgroup L
  have hQ : IsFace Z.toAddSubmonoid L := isFace_units L
  let x₀ : AttractorPt aX Z.toAddSubmonoid T := AttractorPt.ofFace hQ x
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := het.rep
  let T' := rep.pullback g₀
  let q : T' ⟶ T := rep.snd g₀
  let u : T' ⟶ U := rep.fst' g₀
  have hu : f.app (op T') u = X.map q.op x₀.toPoint := by
    have h2 : yoneda.map u ≫ f = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have h4 : (yoneda.map u ≫ f).app (op T') (𝟙 T') = f.app (op T') u := by
      change f.app (op T') (𝟙 T' ≫ u) = _
      rw [Category.id_comp]
    have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
      change g₀.app (op T') (𝟙 T' ≫ q) = _
      rw [Category.id_comp]
      simp [g₀, yonedaEquiv_symm_app_apply]
    exact h4.symm.trans (h3.trans h5)
  have hfix : u ∈ (fixedPoints (quotientAction aU Z)).obj (op T') := by
    refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := f) heq
      (QuotientAddGroup.mk' Z))).mp hZ (op T') u ?_
    rw [hu, ← AttractorPt.toPoint_baseChange]
    exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
  have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op W)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS W :=
    fun a => extSieve_mem Z a
  let wZ : AttractorPt aU Z.toAddSubmonoid T' :=
    attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T' ⟨u, hfix⟩
  have hwZ : wZ.toPoint = u := congrArg Subtype.val
    ((attractorFixedEquivOfCover (act := aU) (BigFppfOver.isSheaf_of_type_yoneda_obj U)
      hcov T').symm_apply_apply ⟨u, hfix⟩)
  have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange q x) = AttractorPt.push F wZ := by
    apply attractor_toPoint_injective_sep hX hsep
    change (AttractorPt.baseChange q x₀).toPoint = f.app (op T') wZ.toPoint
    rw [AttractorPt.toPoint_baseChange, hwZ, hu]
  have hEt : Space.IsEtale B S hS f := fun V φ hφ => MorphismProperty.comp_mem _ _ _ hφ het
  have hcart : IsFaceCartesian F hQ := isFaceCartesian_of_separated hX hsep hl F hEt hQ
  obtain ⟨w, hw⟩ := (hcart T').2 ⟨(AttractorPt.baseChange q x, wZ), hpush⟩
  exact ⟨w, congrArg (fun p => p.1.1) hw⟩

omit [IsAffineHom U.hom.hom] in
/-- Finitely many of a family of étale morphisms to `T` cover `T`, for `T` affine: the sieve they generate is covering. -/
theorem exists_finite_cover {A : Type u} {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    {T' : A → BigFppfOver B S hS} (q : ∀ a, T' a ⟶ T) (he : ∀ a, Etale ((SCH).map (q a)))
    (hc : ∀ τ : (SCH).obj T, ∃ a, τ ∈ Set.range ((SCH).map (q a))) :
    ∃ F : Finset A, Sieve.generate (Presieve.ofArrows (fun a : F => T' a.1) (fun a => q a.1)) ∈
      BigFppfOver.topology B S hS T := by
  have ho : ∀ a, IsOpen (Set.range ((SCH).map (q a))) := fun a =>
    have := he a; ((SCH).map (q a)).isOpenMap.isOpen_range
  obtain ⟨F, hF⟩ := (isCompact_univ (X := (SCH).obj T)).elim_finite_subcover _ ho
    (fun τ _ => Set.mem_iUnion.2 (hc τ))
  refine ⟨F, BigFppfOver.sieve_generate_ofArrows_mem_topology _ _ ?_⟩
  refine Scheme.etalePrecoverage_le_fppfPrecoverage _ ?_
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).2 ⟨fun τ => ?_, fun a => he a.1⟩
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ τ))
  exact ⟨⟨a, haF⟩, ha⟩

variable [AddGroup.FG M] (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Fact 3.34 (ii)**, arbitrary family, `X` separated, locally of finite presentation, not necessarily quasi-compact, `S`
separated, no atlas in the hypotheses. -/
theorem fact334_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) {s : Set (AddSubmonoid M)} (y) (hne : s.Nonempty)
    (hy : ∀ N ∈ s, attractorImage act N = y) : attractorImage act (sInf s) = y := by
  classical
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨A, U, L, -⟩ := exists_small_charts hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep act
  have hsep' := isSeparatedOver_iff_space.1 hsep
  have hlim := isLimitPreserving_of_lfp hX hfp
  have hft := chartsOfFiniteType_of_lfp hfp
  have hinst : ∀ a, IsAffineHom (U a).hom.hom := fun a =>
    isAffineHom_structMap (S := S) (hS := hS) (L.affine a)
  have hlft : ∀ a, LocallyOfFiniteType (U a).hom.hom := fun a => hft _ _ (L.etale a)
  have hfin : ∀ J ⊆ s, J.Finite → J.Nonempty → attractorImage act (sInf J) = y := fun J hJ hf hn =>
    fact334_finite_weak hX hsep' hlim hf
      (fun _ _ _ => existsZFPRAtlas_nonqc hZ hM hX hsep hfp act _) y hn fun N hN => hy N (hJ hN)
  obtain ⟨J₀, hJ₀s, hJ₀f, hJ₀n, hmin⟩ := exists_units_min hne
  obtain ⟨N₀, hN₀⟩ := id hne
  refine le_antisymm ((attractorImage_monotone act (sInf_le hN₀)).trans_eq (hy N₀ hN₀)) ?_
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hinj := fun (P : AddSubmonoid M) T => attractor_toPoint_injective_sep (aX := act) hX hsep' P T
  have key : ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] (t : X.obj (op T)),
      t ∈ y T → ∃ φ : AttractorPt act (sInf s) T, φ.toPoint = t := by
    intro T _ t ht
    have ht₀ := ht
    rw [← hfin J₀ hJ₀s hJ₀f hJ₀n] at ht₀
    obtain ⟨ψ₀, hψ₀⟩ := ht₀
    let v : X.obj (op T) := (AttractorPt.ofFace (isFace_units (sInf J₀)) ψ₀).toPoint
    let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm v
    obtain ⟨F, hF⟩ := exists_finite_cover (fun a => (L.etale a).rep.snd g₀)
      (fun a => (L.etale a).property_snd g₀) (L.covers T g₀)
    have hE := fun a => haveI := hinst a; haveI := hlft a; exists_closure_of_affine_base T (L.actU a)
    choose E hEf hcl using hE
    let E' : Set M := ⋃ a ∈ F, E a
    have hE' : E'.Finite := F.finite_toSet.biUnion fun a _ => hEf a
    have hP : ((fun N : AddSubmonoid M => (N : Set M) ∩ E') '' s).Finite :=
      (hE'.finite_subsets).subset (by rintro _ ⟨N, -, rfl⟩; exact Set.inter_subset_right)
    have hrep : ∀ p : ((fun N : AddSubmonoid M => (N : Set M) ∩ E') '' s),
        ∃ N ∈ s, (N : Set M) ∩ E' = p.1 := fun p => p.2
    choose r hrs hre using hrep
    have := hP.to_subtype
    let J : Set (AddSubmonoid M) := J₀ ∪ Set.range r
    have hJs : J ⊆ s := Set.union_subset hJ₀s (by rintro _ ⟨p, rfl⟩; exact hrs p)
    have hJf : J.Finite := hJ₀f.union (Set.finite_range r)
    have hJsub : J₀ ⊆ J := Set.subset_union_left
    have hJn : J.Nonempty := hJ₀n.mono hJsub
    have ht₁ := ht
    rw [← hfin J hJs hJf hJn] at ht₁
    obtain ⟨ψ, hψ⟩ := ht₁
    have hle₀ : sInf J ≤ sInf J₀ := sInf_le_sInf hJsub
    have hlift : AttractorPt.ofLE hle₀ ψ = ψ₀ := hinj _ _ ((hψ).trans hψ₀.symm)
    have hv : (AttractorPt.ofFace (isFace_units (sInf J)) ψ).toPoint = v := by
      rw [← vertex_eq hle₀ (hmin J hJs hJf hJsub) ψ, hlift]
    have hle : ∀ a ∈ F, AddSubmonoid.closure (((sInf J : AddSubmonoid M) : Set M) ∩ E a) ≤ sInf s := by
      intro a ha
      refine AddSubmonoid.closure_le.mpr fun m hm => ?_
      have hmE : m ∈ E' := Set.mem_biUnion (Finset.mem_coe.2 ha) hm.2
      refine (AddSubmonoid.mem_sInf.mpr fun N hN => ?_)
      have hNp : (N : Set M) ∩ E' ∈ ((fun N : AddSubmonoid M => (N : Set M) ∩ E') '' s) := ⟨N, hN, rfl⟩
      have e := hre ⟨_, hNp⟩
      have h1 : m ∈ (r ⟨_, hNp⟩ : AddSubmonoid M) :=
        (AddSubmonoid.mem_sInf.mp hm.1) _ (Or.inr ⟨_, rfl⟩)
      have h2 : m ∈ ((r ⟨_, hNp⟩ : AddSubmonoid M) : Set M) ∩ E' := ⟨h1, hmE⟩
      rw [e] at h2
      exact h2.1
    refine exists_toPoint_of_sieve hsX (hinj _) _ _ hF ?_
    rintro Y g ⟨W, b, c, ⟨a⟩, rfl⟩
    haveI := hinst a.1
    obtain ⟨w, hw⟩ := chart_lift hX hsep' hlim (L.equivariant a.1) (L.etale a.1)
      (L.strong a.1 _) ψ hv
    obtain ⟨u, hu⟩ := hcl a.1 (sInf J) ((L.etale a.1).rep.snd g₀) w
    refine ⟨AttractorPt.baseChange b (AttractorPt.ofLE (hle a.1 a.2)
      (AttractorPt.push ⟨L.f a.1, L.equivariant a.1⟩ u)), ?_⟩
    have h1 : (AttractorPt.push ⟨L.f a.1, L.equivariant a.1⟩ u).toPoint =
        (AttractorPt.baseChange ((L.etale a.1).rep.snd g₀) ψ).toPoint := by
      rw [← hw]
      exact congrArg ((L.f a.1).app (op _)) hu
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_ofLE, h1,
      AttractorPt.toPoint_baseChange, ← Functor.map_comp_apply, ← op_comp, hψ]
  intro T t ht
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
  refine exists_toPoint_of_sieve hsX (hinj _) t _ hcov ?_
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  have hrest : X.map (π i).op t ∈ y (V i) := by
    rw [← hy N₀ hN₀] at ht ⊢
    obtain ⟨χ, rfl⟩ := ht
    exact ⟨AttractorPt.baseChange (π i) χ, AttractorPt.toPoint_baseChange _ _⟩
  obtain ⟨φ, hφ⟩ := key (V i) _ hrest
  refine ⟨AttractorPt.baseChange a φ, ?_⟩
  rw [AttractorPt.toPoint_baseChange, hφ, ← Functor.map_comp_apply, ← op_comp]

include hZ in
/-- The order conclusion of Fact 3.34 for the same `X`. -/
theorem attractorOrder_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) : AttractorOrder (attractorImage act) where
  monotone := attractorImage_monotone act
  sInf_of_const _ y hne hy := fact334_nonqc hZ hM hX hsep hfp act y hne hy

include hZ in
/-- **Theorem 15.3**, `X` not necessarily quasi-compact: pure magnets are in bijection with attractors. -/
noncomputable def thm153_nonqc [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) :
    pureMagnets (attractorImage act) ≃ Set.range (attractorImage act) :=
  pureEquivRange (attractorOrder_nonqc hZ hM hX hsep hfp act)

end AlgMag.Final

#print axioms AlgMag.Final.fact334_nonqc
#print axioms AlgMag.Final.thm153_nonqc
