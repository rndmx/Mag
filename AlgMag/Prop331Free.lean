/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalAtlasFree
import AlgMag.Prop331Spaces
import AlgMag.FinalNonQCFact
import AlgMag.FinalNonQCLocal

/-!
# Proposition 3.31 (ii) for algebraic spaces, no atlas in the hypotheses

`X` separated, locally of finite presentation and quasi-compact over a separated `S`, `M`, `Z` finitely generated
abelian groups. `prop331_ii_free`: `X` quasi-compact, the atlas of `AlgMag.prop331_ii_spaces` from `thm68_qc_spaces`.
`prop331_ii_general`: `X` not necessarily quasi-compact, the `S`-affine charts of `exists_small_charts` used one at a time
(`chart_lift331`), finitely many over each affine `T`, as in `fact334_nonqc`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M Z : Type u} [AddCommGroup M] [AddGroup.FG M] [AddCommGroup Z] [AddMonoid.FG Z]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- **Proposition 3.31 (ii)**, `X` an algebraic space, no atlas in the hypotheses: `X^{f⁻¹(Y)}_M = X^Y_Z`. -/
theorem prop331_ii_free [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hsep' : Space.IsSeparatedOver B S hS X)
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (LimThm.toT1 X))
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (act : AAction (fppfO B S hS) M X)
    (f : M →+ Z) (Y : AddSubmonoid Z) (T : BigFppfOver B S hS) :
    Function.Bijective
      (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) := by
  have : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨V, actV, v, h1, -, h3⟩ := thm68_qc_spaces hZ hM hX hlfp hsep' hq act
  haveI := (hasFiniteAffineDecomposition_iff _).mp h3.2
  exact prop331_ii_spaces hX hsep f Y (h1.isZFPRAtlas _) (Or.inr (isLimitPreserving_of_lfp hX hfp)) T

section General

variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)} {aX : AAction (fppfO B S hS) M X}
  {π : yoneda.obj U ⟶ X}

omit [AddGroup.FG M] in
/-- The local step of `prop331_ii_spaces` for one `S`-affine chart, not surjective: a point `ψ` of `X^Y_Z` with vertex `v`
gives a point of `X^{f⁻¹(Y)}_M` over the pullback of the chart along `v`. -/
theorem chart_lift331 [AddMonoid.FG M] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hl : IsLimitPreserving X) (f : M →+ Z) {Y : AddSubmonoid Z} (heq : IsEquivariant aU aX π)
    (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) π)
    (hK : IsZFPR heq ((unitsSubgroup Y).comap f)) {T : BigFppfOver B S hS}
    (ψ : AttractorPt (actAlong f aX) Y T) {v : X.obj (op T)}
    (hv : (AttractorPt.ofFace (isFace_units Y) ψ).toPoint = v) :
    ∃ χ : AttractorPt aX (Y.comap f) (het.rep.pullback (yonedaEquiv.symm v)),
      χ.toPoint = X.map (het.rep.snd (yonedaEquiv.symm v)).op ψ.toPoint := by
  subst hv
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  have : Countable M := countable_of_fg M
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  let F : EquivariantHom aU aX := ⟨π, heq⟩
  let FZ := homAlong f F
  let Q := unitsSubgroup Y
  have hQ : IsFace Q.toAddSubmonoid Y := isFace_units _
  let K : AddSubgroup M := Q.comap f
  let x₀ := AttractorPt.ofFace hQ ψ
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := het.rep
  let T' := rep.pullback g₀
  let q : T' ⟶ T := rep.snd g₀
  let u : T' ⟶ U := rep.fst' g₀
  have hu : π.app (op T') u = X.map q.op x₀.toPoint := by
    have h2 : yoneda.map u ≫ π = yoneda.map q ≫ g₀ := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact rep.w g₀
    have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
    have h4 : (yoneda.map u ≫ π).app (op T') (𝟙 T') = π.app (op T') u := by
      change π.app (op T') (𝟙 T' ≫ u) = _
      rw [Category.id_comp]
    have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = X.map q.op x₀.toPoint := by
      change g₀.app (op T') (𝟙 T' ≫ q) = _
      rw [Category.id_comp]
      simp [g₀, yonedaEquiv_symm_app_apply]
    exact h4.symm.trans (h3.trans h5)
  have hfixX : X.map q.op x₀.toPoint ∈ (fixedPoints (quotientAction aX K)).obj (op T') := by
    apply mem_fixed_comap_of_along hsX aX f Q
    rw [← AttractorPt.toPoint_baseChange]
    exact (AttractorPt.baseChange q x₀).toPoint_mem_fixedPoints
  have hfixU : u ∈ (fixedPoints (quotientAction aU K)).obj (op T') :=
    (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := π) heq
      (QuotientAddGroup.mk' K))).mp hK (op T') u (by rw [hu]; exact hfixX)
  have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) K.toAddSubmonoid (op W)),
      extSieve (fppfO B S hS) K a ∈ BigFppfOver.topology B S hS W :=
    fun a => extSieve_mem K a
  let w₀ : AttractorPt aU (Q.toAddSubmonoid.comap f) T' :=
    attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T' ⟨u, hfixU⟩
  have hw₀ : w₀.toPoint = u := congrArg Subtype.val ((attractorFixedEquivOfCover (act := aU)
    (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T').symm_apply_apply ⟨u, hfixU⟩)
  let w : AttractorPt (actAlong f aU) Q.toAddSubmonoid T' := ptAlong aU (Y := Q.toAddSubmonoid) w₀
  have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange q ψ) = AttractorPt.push FZ w := by
    apply attractor_toPoint_injective_sep hX hsep
    change (AttractorPt.baseChange q x₀).toPoint = π.app (op T') (ptAlong aU w₀).toPoint
    rw [AttractorPt.toPoint_baseChange, toPoint_ptAlong, hw₀, hu]
  have hEt : Space.IsEtale B S hS π := fun V φ hφ => MorphismProperty.comp_mem _ _ _ hφ het
  have hcart : IsFaceCartesian FZ hQ := isFaceCartesian_of_separated hX hsep hl FZ hEt hQ
  obtain ⟨w', hw'⟩ := (hcart T').2 ⟨(AttractorPt.baseChange q ψ, w), hpush⟩
  have hw'' : AttractorPt.push FZ w' = AttractorPt.baseChange q ψ := congrArg (fun p => p.1.1) hw'
  obtain ⟨v₀, hv₀⟩ := (prop331_ii (f := f) (Y := Y) (aX := aU) T').2 w'
  refine ⟨AttractorPt.push F v₀, ?_⟩
  rw [← AttractorPt.toPoint_baseChange, ← hw'', ← hv₀]
  rfl

end General

include hZ in
/-- **Proposition 3.31 (ii)**, `X` a separated algebraic space, locally of finite presentation, not necessarily
quasi-compact, `S` separated, no atlas in the hypotheses: `X^{f⁻¹(Y)}_M = X^Y_Z`. -/
theorem prop331_ii_general [S.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (f : M →+ Z) (Y : AddSubmonoid Z) (T : BigFppfOver B S hS) :
    Function.Bijective
      (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) := by
  classical
  haveI : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance
  obtain ⟨A, U, L, -⟩ := exists_small_charts hZ hM hX ((lfp_toT1_iff hX).2 hfp) hsep act
  have hsep' := isSeparatedOver_iff_space.1 hsep
  have hlim := isLimitPreserving_of_lfp hX hfp
  have hinst : ∀ a, IsAffineHom (U a).hom.hom := fun a =>
    isAffineHom_structMap (S := S) (hS := hS) (L.affine a)
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hinjN := fun T => attractor_toPoint_injective_sep (aX := act) hX hsep' (Y.comap f) T
  constructor
  · intro χ χ' h
    apply hinjN
    rw [← toPoint_ptAlong χ, ← toPoint_ptAlong χ', h]
  · intro ψ
    suffices hχ : ∃ χ : AttractorPt act (Y.comap f) T, χ.toPoint = ψ.toPoint by
      obtain ⟨χ, hχ⟩ := hχ
      exact ⟨χ, attractor_toPoint_injective_sep hX hsep' _ _ ((toPoint_ptAlong χ).trans hχ)⟩
    have key : ∀ (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
        (ψ : AttractorPt (actAlong f act) Y T), ∃ χ : AttractorPt act (Y.comap f) T,
          χ.toPoint = ψ.toPoint := by
      intro T _ ψ
      let v : X.obj (op T) := (AttractorPt.ofFace (isFace_units Y) ψ).toPoint
      let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm v
      obtain ⟨F, hF⟩ := exists_finite_cover (fun a => (L.etale a).rep.snd g₀)
        (fun a => (L.etale a).property_snd g₀) (L.covers T g₀)
      refine exists_toPoint_of_sieve hsX hinjN _ _ hF ?_
      rintro W g ⟨W', b, c, ⟨a⟩, rfl⟩
      haveI := hinst a.1
      obtain ⟨χ, hχ⟩ := chart_lift331 hX hsep' hlim f (L.equivariant a.1) (L.etale a.1)
        (L.strong a.1 _) ψ (v := v) rfl
      refine ⟨AttractorPt.baseChange b χ, ?_⟩
      rw [AttractorPt.toPoint_baseChange, hχ, ← Functor.map_comp_apply, ← op_comp]
    obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover T
    refine exists_toPoint_of_sieve hsX hinjN _ _ hcov ?_
    rintro W g ⟨W', a, b, ⟨i⟩, rfl⟩
    have := hV i
    obtain ⟨φ, hφ⟩ := key (V i) (AttractorPt.baseChange (π i) ψ)
    refine ⟨AttractorPt.baseChange a φ, ?_⟩
    rw [AttractorPt.toPoint_baseChange, hφ, AttractorPt.toPoint_baseChange, ← Functor.map_comp_apply,
      ← op_comp]

section AnyS

open LimOrbit CategoryTheory.OverShriek

include hZ in
/-- The statement over an object `T₀` of the site whose underlying scheme is separated. -/
theorem prop331_step (T₀ : BigFppfOver B S hS) [T₀.left.1.IsSeparated] (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (f : M →+ Z) (Y : AddSubmonoid Z)
    (W : BigFppfOver B T₀.left.1 T₀.left.2)
    (ψ : AttractorPt (actAlong f act) Y ((Over.map T₀.hom).obj W)) :
    ∃ χ : AttractorPt act (Y.comap f) ((Over.map T₀.hom).obj W), χ.toPoint = ψ.toPoint := by
  have hR := res_alg T₀ hX
  have hfp' := (lfp_toT1_iff hR).1 (res_lfp T₀ hX ((lfp_toT1_iff hX).2 hfp))
  let ψ₀ : AttractorPt (actAlong f (resAct (T₀ := T₀) act)) Y W := attrDown ψ
  obtain ⟨χ₀, hχ₀⟩ := (prop331_ii_general hZ hM hR (res_sep T₀ hX hsep) hfp'
    (resAct (T₀ := T₀) act) f Y W).2 ψ₀
  refine ⟨attrUp χ₀, ?_⟩
  rw [attrUp_toPoint, ← toPoint_ptAlong χ₀, hχ₀]
  exact attrDown_toPoint ψ

include hZ in
/-- **Proposition 3.31 (ii)**, `X` a separated algebraic space, locally of finite presentation, not necessarily
quasi-compact, `S` arbitrary, no atlas in the hypotheses: `X^{f⁻¹(Y)}_M = X^Y_Z`. -/
theorem prop331_ii_anyS (hM : B.Contains (Spec (ZMon M)))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (f : M →+ Z) (Y : AddSubmonoid Z) (T : BigFppfOver B S hS) :
    Function.Bijective
      (ptAlong act : AttractorPt act (Y.comap f) T → AttractorPt (actAlong f act) Y T) := by
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hsep' := isSeparatedOver_iff_space.1 hsep
  have hinjN := fun T => attractor_toPoint_injective_sep (aX := act) hX hsep' (Y.comap f) T
  constructor
  · intro χ χ' h
    apply hinjN
    rw [← toPoint_ptAlong χ, ← toPoint_ptAlong χ', h]
  intro ψ
  suffices hχ : ∃ χ : AttractorPt act (Y.comap f) T, χ.toPoint = ψ.toPoint by
    obtain ⟨χ, hχ⟩ := hχ
    exact ⟨χ, attractor_toPoint_injective_sep hX hsep' _ _ ((toPoint_ptAlong χ).trans hχ)⟩
  let I : Type u := { W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens //
    ∃ O : S.affineOpens, ∀ τ ∈ W.1, structMap T τ ∈ O.1 }
  have hC : ∀ i : I, B.Contains (i.1.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.1.ι T.left.property
  let V : I → BigFppfOver B S hS := fun i => siteObject B S hS (hC i) (i.1.1.ι ≫ T.hom.hom)
  let π : ∀ i, V i ⟶ T := fun i => siteHom i.1.1.ι rfl
  have hcov : Sieve.ofArrows V π ∈ BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS π
      (fun i => inferInstanceAs (IsOpenImmersion i.1.1.ι)) fun τ => ?_
    obtain ⟨_, ⟨O, hO, rfl⟩, hs, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (structMap T τ)) isOpen_univ
    have hopen : IsOpen (structMap T ⁻¹' O) :=
      O.isOpen.preimage (Scheme.Hom.continuous _)
    obtain ⟨_, ⟨W, hW, rfl⟩, hτ, hsub⟩ :=
      ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (show τ ∈ structMap T ⁻¹' O from hs) hopen
    refine ⟨⟨⟨W, hW⟩, ⟨O, hO⟩, fun τ' h' => hsub h'⟩, ⟨τ, hτ⟩, ?_⟩
    rfl
  obtain ⟨Yz, rfl⟩ : ∃ Yz, Yz = Y := ⟨Y, rfl⟩
  refine exists_toPoint_of_sieve hsX hinjN ψ.toPoint _ hcov ?_
  rintro Wt g ⟨Wt', a, b, ⟨i⟩, rfl⟩
  obtain ⟨W, ⟨O, hO⟩, hsub⟩ := i
  let i' : I := ⟨W, ⟨O, hO⟩, hsub⟩
  obtain ⟨l, -⟩ := exists_lift_openBase (O := O) (V i') (fun τ => by
    have : structMap (V i') τ = structMap T (W.1.ι τ) := rfl
    rw [this]
    exact hsub (τ : W.1.toScheme).1 (τ : W.1.toScheme).2)
  let T₀ := openBase (B := B) (hS := hS) O
  have hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := isAffine_openBase hO
  haveI : T₀.left.1.IsSeparated := by
    have : IsAffine T₀.left.1 := hAff
    infer_instance
  have hψ : l.left ≫ T₀.hom = (V i').hom := Over.w l
  let e := overMapMkIso T₀.hom hψ
  obtain ⟨φ, hφ⟩ := prop331_step hZ T₀ hM hX hsep hfp act f Yz (Over.mk l.left)
    (AttractorPt.baseChange e.inv (AttractorPt.baseChange (π i') ψ))
  refine ⟨AttractorPt.baseChange a (AttractorPt.baseChange e.hom φ), ?_⟩
  rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_baseChange, hφ, AttractorPt.toPoint_baseChange,
    AttractorPt.toPoint_baseChange, map_overMapMkIso_hom_inv T₀.hom X hψ, ← Functor.map_comp_apply, ← op_comp]

end AnyS

end AlgMag.Final#print axioms AlgMag.Final.prop331_ii_free
#print axioms AlgMag.Final.prop331_ii_general
#print axioms AlgMag.Final.prop331_ii_anyS