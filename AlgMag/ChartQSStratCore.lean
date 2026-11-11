/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratum

/-!
# The affine stratum lemma for quasi-separated `X`

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
A nonempty quasi-separated, locally noetherian algebraic space with `D(M)`-action has a nonempty
`D(M)`-stable affine open. The separated version `ChartStratum.affineStratum` uses separatedness for
quasi-separatedness of `Y → A` (Step 6) and for the generic stabilizer `exists_generic_stabilizer`
(Step 2). Here the first comes from quasi-separatedness of `X`, and the second is the named
proposition `GenericStabilizerQS`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartQSStrat

open AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `isQuasiSeparated_of_mono`, assuming only `X` quasi-separated. -/
theorem isQuasiSeparated_of_mono_qs {X Y G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : Y ⟶ X) [Mono ι]
    (r : Y ⟶ G) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) :
    Space.IsQuasiSeparated B S hS r :=
  Space.isQuasiCompact_of_isPullback B S hS
    (isPullback_diagonal_of_mono ι r (terminal.from X) (terminal.from G) (terminal.hom_ext _ _)) hqs

/-- The generic stabilizer on étale charts with integral noetherian affine source, at `act`. -/
def GenericStabilizerAt {M : Type u} [AddCommGroup M] (act : AAction (fppfO B S hS) M X) : Prop :=
  ∀ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V)) (_ : IsDomain Γ((SCH).obj V, ⊤))
    (_ : IsNoetherianRing Γ((SCH).obj V, ⊤)) (p : X.obj (op V))
    (_ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p)),
    ∃ (s : Γ((SCH).obj V, ⊤)) (_ : s ≠ 0) (Z : AddSubgroup M),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ V), IsUnit (((SCH).map t).appTop.hom s) →
        ∀ h : APt (fppfO B S hS) M (op T),
          act.smul h (X.map t.op p) = X.map t.op p ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1

/-- **Named hypothesis**: the generic stabilizer, for every quasi-separated algebraic space with an
action of `D(M)`, `M` finitely generated. Proved for separated `X` by `exists_generic_stabilizer`. -/
def GenericStabilizerQS (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
    IsAlgebraicSpace B S hS X → Space.IsQuasiSeparated B S hS (terminal.from X) →
    ∀ act : AAction (fppfO B S hS) M X, GenericStabilizerAt act

section Main
variable {M : Type u} [AddCommGroup M] [Countable M] [AddGroup.FG M]

/-- **Affine stratum lemma, steps 4 to 8**: from an étale chart on whose open orbit the stabilizers are `D(M/Z)`,
lying over an affine open of `S`, for `X` quasi-separated. -/
theorem exists_stable_affine_of_orbit_qs {W : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X)
    (c : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X)) (hc : Space.IsEtale B S hS c) (Z : AddSubgroup M)
    (hst : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      ∀ h : APt (fppfO B S hS) M (op T),
        act.smul h x = x ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1)
    (A : BigFppfOver B S hS) (hAa : IsAffine ((SCH).obj A))
    (hAo : AlgebraicGeometry.IsOpenImmersion (structMap A))
    (hrange : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      Nonempty (T ⟶ A))
    (hWne : Nonempty ((SCH).obj W)) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f : yoneda.obj U ⟶ X), IsAffine ((SCH).obj U) ∧ Nonempty ((SCH).obj U) ∧
        IsEquivariant actU act f ∧ Space.IsOpenImmersion B S hS f := by
  classical
  have hOp := orbSub_isOpen act c hX hc
  let Yf := orbSub act c
  let Y := Yf.toFunctor
  have hY : IsAlgebraicSpace B S hS Y := hOp.1
  have hYsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hY.isSheaf
  have inj : ∀ T, Function.Injective (Yf.ι.app T) := fun T a b e => Subtype.ext e
  let actY : AAction (fppfO B S hS) M Y := actOfMono act Yf.ι inj (fun {T} h t =>
    ⟨⟨act.smul h t.1, smul_mem_orbSub act c hX hc (T := T.unop) h t.2⟩, rfl⟩)
  have hspec : IsEquivariant actY act Yf.ι := actOfMono_spec _ _ _ _
  have hiff : ∀ {T : BigFppfOver B S hS} (x : Y.obj (op T)) (h : APt (fppfO B S hS) M (op T)),
      actY.smul h x = x ↔ TrivialOn Z h := by
    intro T x h
    rw [trivialOn_iff, ← hst x.2 h]
    constructor
    · intro e
      have := hspec h x
      rw [e] at this
      exact this.symm
    · intro e
      refine inj _ ?_
      exact (hspec h x).trans e
  have hfix : ∀ {T : BigFppfOver B S hS} (x : Y.obj (op T)) (h : APt (fppfO B S hS) M (op T)),
      TrivialOn Z h → actY.smul h x = x := fun x h => (hiff x h).2
  let β := descAction hYsh hfix
  have hfree' : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (a b : APt (fppfO B S hS) Z.toAddSubmonoid T)
      (x : Y.obj T), β.smul a x = β.smul b x → a = b := by
    intro T a b x e
    have h1 : β.smul (zInv a * b) x = x := by
      rw [β.mul_smul, ← e, ← β.mul_smul, zInv_mul, β.one_smul]
    have h2 := descAction_free hYsh hfix (fun x h e => (hiff x h).1 e) (T := T.unop) _ x h1
    have h3 : a * (zInv a * b) = a := by rw [h2, mul_one]
    rw [← mul_assoc, mul_comm a, zInv_mul, one_mul] at h3
    exact h3.symm
  haveI : AddMonoid.FG Z.toAddSubmonoid := fg_toAddSubmonoid Z
  letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) := AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf (relJ β)).obj :=
    quotient_isAlgebraicSpace β hY hfree'
  have hR := relP_isAlgebraicSpace (Z := Z) hY
  have hj := relJ_isEquivalenceRelation β hfree'
  let π := Space.toQuotientSheaf (relJ β)
  -- the map to the affine open `A`
  have hAm : Mono (structMap A) := inferInstance
  have hsub := hom_subsingleton hAm
  let r : Y ⟶ yoneda.obj A :=
    { app := fun T => ↾ fun x => Classical.choice (hrange (T := T.unop) x.2)
      naturality := fun T T' f => by
        ext1
        refine DFunLike.ext _ _ fun x => ?_
        haveI := hsub T'.unop
        exact Subsingleton.elim _ _ }
  have hcond : (relJ β).target.left ≫ r = (relJ β).source.left ≫ r := by
    refine NatTrans.ext (funext fun T => ?_)
    ext1
    refine DFunLike.ext _ _ fun x => ?_
    haveI := hsub T.unop
    exact Subsingleton.elim _ _
  let shA : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj A, BigFppfOver.isSheaf_yoneda_obj B S hS A⟩
  let f : (Space.quotientSheaf (relJ β)).obj ⟶ yoneda.obj A :=
    (Space.quotientSheafDesc (relJ β) shA r hcond).hom
  have hfac : π ≫ f = r := Space.toQuotientSheaf_quotientSheafDesc (relJ β) shA r hcond
  have hYX : Mono Yf.ι := inferInstance
  have hqsf : Space.IsQuasiSeparated B S hS f := by
    refine isQuasiSeparated_quotient (relJ β) hR hY hj hQ (isAlgebraicSpace_yoneda B S hS A) f ?_ ?_
    · rw [hfac]; exact isQuasiSeparated_of_mono_qs Yf.ι r hqsX
    · exact isQuasiCompact_of_isAffineHom _ hR hY (relJ_source_isAffineHom β)
  have hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal
      (Space.quotientSheaf (relJ β)).obj :=
    Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hQ
      (Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal A hAa) hqsf
  -- a point of the quotient
  let x₀ : Y.obj (op W) := ⟨c.app (op W) (𝟙 W), by
    have := orbMap_mem act c (T := op W) (ptTop 1, 𝟙 W)
    have e : (orbMap act c).app (op W) (ptTop 1, 𝟙 W) = c.app (op W) (𝟙 W) := by
      change act.smul (topPt (ptTop 1)) _ = _
      rw [topPt_ptTop, act.one_smul]
      rfl
    rw [e] at this
    exact this⟩
  obtain ⟨w⟩ := hWne
  have hne : Nonempty (Space.points B S hS (Space.quotientSheaf (relJ β)).obj) :=
    ⟨Space.pointsMap B S hS (yoneda.obj W) (yonedaEquiv.symm (π.app (op W) x₀))
      ((Space.pointsEquivScheme B S hS W).symm w)⟩
  obtain ⟨D, ξ, hDa, hDne, hξ⟩ := exists_affine_open_of_absQS hQ hqs hne
  obtain ⟨U, pU, q, hUa, pb⟩ :=
    exists_affine_preimage_gen (relJ β) hR hY hj (relJ_source_isAffineHom β) hQ D hDa ξ
  have hpU : Space.IsOpenImmersion B S hS pU := by
    have := Space.inverseImage_isStableUnderBaseChange B S hS
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
    have hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    exact hs.of_isPullback pb.flip hξ
  have hpUm : Mono pU := Space.mono_of_isOpenImmersion B S hS pU hpU
  have hm : Space.IsOpenImmersion B S hS (pU ≫ Yf.ι) :=
    Space.isOpenImmersion_comp B S hS _ _ hpU hOp.2
  have hmono : Mono (pU ≫ Yf.ι) := mono_comp _ _
  have hinj : ∀ T, Function.Injective ((pU ≫ Yf.ι).app T) := fun T =>
    (CategoryTheory.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono T)
  -- `π` is invariant
  have hinv : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (y : Y.obj T),
      π.app T (actY.smul h y) = π.app T y := by
    intro T h y
    have e1 : actY.smul h y = β.smul (APt.toMagnet Z.toAddSubmonoid h) y :=
      (descAction_toMagnet hYsh hfix (T := T.unop) h y).symm
    have e2 := ConcreteCategory.congr_hom
      (NatTrans.congr_app (Space.target_toQuotientSheaf_eq_source (relJ β)) T)
      ((APt.toMagnet Z.toAddSubmonoid h, y) : (relP Y Z).obj T)
    rw [e1]
    simp only [relJ_target, relJ_source] at e2
    exact e2
  have hst' : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T)
      (t : (yoneda.obj U).obj T), ∃ t', (pU ≫ Yf.ι).app T t' = act.smul h ((pU ≫ Yf.ι).app T t) := by
    intro T h t
    have pbT := pb.map ((evaluation _ _).obj T)
    rw [Types.isPullback_iff] at pbT
    obtain ⟨hw, -, hsurj⟩ := pbT
    have hwt := ConcreteCategory.congr_hom hw t
    obtain ⟨t', e1, e2⟩ := hsurj (actY.smul h (pU.app T t)) ((yoneda.map q).app T t) (by
      refine (hinv h _).trans ?_
      exact hwt)
    refine ⟨t', ?_⟩
    have e1' : pU.app T t' = _ := e1
    change Yf.ι.app T (pU.app T t') = act.smul h (Yf.ι.app T (pU.app T t))
    rw [e1']
    exact hspec h _
  -- `U` is nonempty
  have hUne : Nonempty ((SCH).obj U) := by
    obtain ⟨V', f', hF, hL, hS', a, ha⟩ := Space.exists_single_fppf_lift_of_isLocallySurjective
      B S hS hY.isSheaf hQ.isSheaf π (Space.isLocallySurjective_toQuotientSheaf (relJ β)) D
      (yonedaEquiv ξ)
    have hcomm : yonedaEquiv.symm a ≫ π = yoneda.map f' ≫ ξ := by
      apply yonedaEquiv.injective
      rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
      simpa only [Equiv.apply_symm_apply] using ha
    let t : V' ⟶ U := yoneda.preimage (pb.lift _ _ hcomm)
    obtain ⟨d⟩ := hDne
    obtain ⟨v, -⟩ := hS'.surj d
    exact ⟨(SCH).map t v⟩
  exact ⟨U, actOfMono act (pU ≫ Yf.ι) hinj hst', pU ≫ Yf.ι, hUa, hUne, actOfMono_spec _ _ _ _, hm⟩

theorem exists_stable_affine_of_chart_qs {V : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X)
    (hVa : IsAffine ((SCH).obj V)) (hVd : IsDomain Γ((SCH).obj V, ⊤))
    (hVn : IsNoetherianRing Γ((SCH).obj V, ⊤)) (p : X.obj (op V))
    (hX : IsAlgebraicSpace B S hS X) (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hgen : GenericStabilizerAt act)
    (hc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p))
    (A : BigFppfOver B S hS) (hAa : IsAffine ((SCH).obj A))
    (hAo : AlgebraicGeometry.IsOpenImmersion (structMap A)) (v : V ⟶ A) :
    ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (f : yoneda.obj U ⟶ X), IsAffine ((SCH).obj U) ∧ Nonempty ((SCH).obj U) ∧
        IsEquivariant actU act f ∧ Space.IsOpenImmersion B S hS f := by
  classical
  obtain ⟨s, hs, Z, hZ⟩ := hgen V hVa hVd hVn p hc
  let W := Space.opensObject B S hS V (((SCH).obj V).basicOpen s)
  let ι : W ⟶ V := Space.opensObjectι B S hS V _
  have hιo : AlgebraicGeometry.IsOpenImmersion ((SCH).map ι) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj V) _)
    infer_instance
  have hunit : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W),
      IsUnit (((SCH).map (t ≫ ι)).appTop.hom s) := fun T t => by
    rw [Functor.map_comp]
    exact isUnit_of_factor_basicOpen s ((SCH).map t)
  let c : yoneda.obj W ⟶ X := yoneda.map ι ≫ yonedaEquiv.symm p
  have hcE : Space.IsEtale B S hS c := by
    rw [Space.isEtale_iff_presheaf_of_yoneda]
    let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)
    have : MorphismProperty.IsStableUnderComposition (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      (inferInstance : MorphismProperty.IsMultiplicative
        (@Etale.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
    have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
    have : P.IsStableUnderBaseChange :=
      ⟨fun sq hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Etale.{u}) (sq.map (SCH)) hg⟩
    have h1 : P.presheaf (yoneda.map ι) :=
      MorphismProperty.relative_map (F := yoneda) (show Etale ((SCH).map ι) from inferInstance)
    exact MorphismProperty.comp_mem _ _ _ h1 hc
  have hXsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf
  have hst : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      ∀ h : APt (fppfO B S hS) M (op T),
        act.smul h x = x ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := fun hx h =>
    smul_eq_iff_of_orbitLocal hXsh hZ (orbitLocal_of_mem act p s ι hunit hX hcE hx) h
  have hrange : ∀ {T : BigFppfOver B S hS} {x : X.obj (op T)}, x ∈ (orbSub act c).obj (op T) →
      Nonempty (T ⟶ A) := by
    intro T x hx
    obtain ⟨U, q, r, -, -, -, hS'⟩ := exists_lift_of_mem_orbSub act c hX hcE hx
    refine nonempty_hom_of_range hAo ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := hS'.surj y
    have e1 : (SCH).map q ≫ structMap T = structMap U :=
      congrArg (B.inclusion.map) (Over.w q)
    let t : U ⟶ A := r.2 ≫ ι ≫ v
    have e2 : (SCH).map t ≫ structMap A = structMap U :=
      congrArg (B.inclusion.map) (Over.w t)
    refine ⟨(SCH).map t u, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2, ← e1, Scheme.Hom.comp_apply]
  have hWne : Nonempty ((SCH).obj W) := by
    have hred : IsReduced ((SCH).obj V) := by
      haveI : IsReduced Γ((SCH).obj V, ⊤) := inferInstance
      exact isReduced_of_isAffine_isReduced _
    have hbo : ((SCH).obj V).basicOpen s ≠ ⊥ := fun e =>
      hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 e)
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.1 hbo
    exact ⟨⟨x, hx⟩⟩
  exact exists_stable_affine_of_orbit_qs act c hX hqsX hcE Z hst A hAa hAo hrange hWne

end Main

/-- **Affine stratum lemma**: a nonempty quasi-separated, locally noetherian algebraic space with an action of `D(M)`,
for `M` finitely generated, has a nonempty affine `D(M)`-stable open. -/
theorem affineStratum_qs {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
    (hgen : GenericStabilizerQS B S hS)
    (hX : IsAlgebraicSpace B S hS X) (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (act : AAction (fppfO B S hS) M X) : ChartMain.AffineStratum X act := by
  classical
  rintro ⟨W, ⟨w⟩, ⟨x₀⟩⟩
  haveI : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  haveI : Countable M := countable_of_fg M
  have hneX : Nonempty (Space.points B S hS X) :=
    ⟨Space.pointsMap B S hS _ (yonedaEquiv.symm x₀) ((Space.pointsEquivScheme B S hS W).symm w)⟩
  obtain ⟨N, K, ⟨T₁, ⟨t₁⟩, ⟨x₁⟩, hu₁⟩, htors, hK⟩ := exists_unit_data (M := M) hneX
  haveI : AddGroup.FG (M ⧸ K) := inferInstance
  haveI : Countable (M ⧸ K) := countable_of_fg _
  -- `Z = X[1/N]`
  let Zf := invSub X N
  have hZo := invSub_isOpen hX N
  let Z := Zf.toFunctor
  have hZ : IsAlgebraicSpace B S hS Z := hZo.1
  have hNZ : ∀ (T : BigFppfOver B S hS) (_ : Z.obj (op T)), IsUnit (N : Γ((SCH).obj T, ⊤)) :=
    fun T z => (mem_invSub_iff N z.1).1 z.2
  have injZ : ∀ T, Function.Injective (Zf.ι.app T) := fun T a b e => Subtype.ext e
  let actZ : AAction (fppfO B S hS) M Z := actOfMono act Zf.ι injZ (fun {T} h t =>
    ⟨⟨act.smul h t.1, (mem_invSub_iff N _).2 (hNZ T.unop t)⟩, rfl⟩)
  have hactZ : IsEquivariant actZ act Zf.ι := actOfMono_spec _ _ _ _
  -- the reduction, with `D(M/K)`
  let Rd := Space.reduction B S hS Z hZ
  have hcl : Space.IsClosedSubspace B S hS Rd :=
    (Space.isAlgebraicSpaceStructure_reduction B S hS Z hZ).isClosedSubspace
  have hRa : IsAlgebraicSpace B S hS Rd.toFunctor := hcl.1
  let act' := actZ.comap (QuotientAddGroup.mk' K)
  have injR : ∀ T, Function.Injective (Rd.ι.app T) := fun T a b e => Subtype.ext e
  let act2 : AAction (fppfO B S hS) (M ⧸ K) Rd.toFunctor := actOfMono act' Rd.ι injR (fun {T} h t =>
    ⟨⟨act'.smul h t.1, smul_mem_reduction act' hZ N hNZ htors (T := T.unop) h t.2⟩, rfl⟩)
  have hact2 : IsEquivariant act2 act' Rd.ι := actOfMono_spec _ _ _ _
  -- a chart of the reduction
  have hqsZ : Space.IsQuasiSeparated B S hS (terminal.from Z) :=
    isQuasiSeparated_of_mono_qs Zf.ι _ hqsX
  have hqsR : Space.IsQuasiSeparated B S hS (terminal.from Rd.toFunctor) :=
    isQuasiSeparated_of_mono_qs Rd.ι _ hqsZ
  have hlft : Space.IsLocallyOfFiniteType B S hS (Rd.ι ≫ Zf.ι) :=
    Space.isLocallyOfFiniteType_comp B S hS hRa hZ hX Rd.ι Zf.ι
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS Rd.ι hcl.2)
      (isLocallyOfFiniteType_of_etale _ (Space.isEtale_of_isOpenImmersion B S hS hZo.2))
  have hNoeR := Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hRa hX _ hlft hNoe
  have hneZ : Nonempty (Space.points B S hS Z) :=
    ⟨Space.pointsMap B S hS _ (yonedaEquiv.symm (⟨x₁, (mem_invSub_iff N _).2 hu₁⟩ : Z.obj (op T₁)))
      ((Space.pointsEquivScheme B S hS T₁).symm t₁)⟩
  have hneR : Nonempty (Space.points B S hS Rd.toFunctor) := by
    obtain ⟨z⟩ := hneZ
    obtain ⟨r, -⟩ := Space.surjective_pointsMap_ι_reduction B S hS Z hZ z
    exact ⟨r⟩
  obtain ⟨V, p, A, hVa, hVd, hVn, hE, hAa, hAo, ⟨v⟩⟩ := exists_integral_chart hRa
    (Space.hasEtaleLocalProperty_isReduced_reduction B S hS Z hZ) hNoeR hneR
  obtain ⟨U', actU', f', hU'a, hU'n, hf'e, hf'o⟩ :=
    exists_stable_affine_of_chart_qs act2 hVa hVd hVn p hRa hqsR (by haveI : AddMonoid.FG (M ⧸ K) := AddGroup.fg_iff_addMonoid_fg.mp inferInstance; exact hgen (M ⧸ K) hRa hqsR act2) hE A hAa hAo v
  obtain ⟨G, hG, ⟨T, hTa, ⟨e⟩⟩, ⟨W', hW'n, ⟨g₀⟩⟩, hst⟩ := exists_stable_open_of_reduction actZ hZ K act2 hact2
    (fun hk b z h => hK hk b z.1 ((mem_invSub_iff N z.1).1 z.2) h) actU' f' hU'a hU'n hf'e hf'o
  -- the stable affine open of `X`
  let f : yoneda.obj T ⟶ X := e.inv ≫ G.ι ≫ Zf.ι
  have hfo : Space.IsOpenImmersion B S hS f := by
    have h1 : Space.IsOpenImmersion B S hS (G.ι ≫ Zf.ι) :=
      Space.isOpenImmersion_comp B S hS _ _ hG.2 hZo.2
    exact MorphismProperty.RespectsIso.precomp _ e.inv _ h1
  have hfm : Mono f := Space.mono_of_isOpenImmersion B S hS f hfo
  have hinj : ∀ T', Function.Injective (f.app T') := fun T' =>
    (CategoryTheory.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hfm T')
  have hstab : ∀ {T' : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T')
      (t : (yoneda.obj T).obj T'), ∃ t', f.app T' t' = act.smul h (f.app T' t) := by
    intro T' h t
    let g := e.inv.app T' t
    let g' : G.toFunctor.obj T' := ⟨actZ.smul h g.1, hst (T := T'.unop) h g.2⟩
    refine ⟨e.hom.app T' g', ?_⟩
    have e1 : e.inv.app T' (e.hom.app T' g') = g' :=
      ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id T') g'
    change Zf.ι.app T' (G.ι.app T' (e.inv.app T' (e.hom.app T' g'))) = _
    rw [e1]
    exact hactZ h g.1
  have hTn : Nonempty ((SCH).obj T) := by
    let t : W' ⟶ T := e.hom.app (op W') ⟨g₀.1, g₀.2⟩
    obtain ⟨w'⟩ := hW'n
    exact ⟨(SCH).map t w'⟩
  exact ⟨T, actOfMono act f hinj hstab, f, hTa, hTn, actOfMono_spec _ _ _ _, hfo⟩

/-- **Affine stratum lemma** for quasi-separated `X`, in the form `ChartQS.effective_of_noetherian` asks for. -/
theorem affineStratum_closedStable_qs {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
    (hgen : GenericStabilizerQS B S hS)
    {act₀ : AAction (fppfO B S hS) M X} (hX : IsAlgebraicSpace B S hS X)
    (hqsX : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hNoe : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (C : ChartMain.ClosedStable act₀) : ChartMain.AffineStratum C.Z C.actZ := by
  have hm : Mono C.i := Space.mono_of_isClosedImmersion B S hS C.i C.closed
  exact affineStratum_qs hgen C.alg (isQuasiSeparated_of_mono_qs C.i _ hqsX)
    (Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS C.alg hX C.i
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hNoe) C.actZ

end AlgMag.ChartQSStrat

#print axioms AlgMag.ChartQSStrat.affineStratum_qs
#print axioms AlgMag.ChartQSStrat.affineStratum_closedStable_qs
