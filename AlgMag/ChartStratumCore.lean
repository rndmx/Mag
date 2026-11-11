/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumDecent

/-!
# A stable affine open from an integral étale chart (affine stratum lemma, step 8)

Let `p : V → X` be an étale chart with `V` affine, integral and noetherian, lying over an affine open
`A` of `S`. Then `X` has a nonempty affine `D(M)`-stable open.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- An action restricts along a monomorphism whose image is stable. -/
noncomputable def actOfMono {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F)
    (m : G ⟶ F) (hm : ∀ T, Function.Injective (m.app T))
    (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (t : G.obj T),
      ∃ t', m.app T t' = act.smul h (m.app T t)) : AAction (fppfO B S hS) M G where
  smul h t := (hst h t).choose
  one_smul {T} x := hm T (by rw [(hst 1 x).choose_spec, act.one_smul])
  mul_smul {T} g h x := hm T (by
    rw [(hst _ x).choose_spec, (hst g _).choose_spec, (hst h x).choose_spec, act.mul_smul])
  map_smul {T T'} f h x := hm T' (by
    have e1 := ConcreteCategory.congr_hom (m.naturality f) (hst h x).choose
    have e2 := ConcreteCategory.congr_hom (m.naturality f) x
    change m.app T' (G.map f _) = F.map f (m.app T _) at e1
    change m.app T' (G.map f x) = F.map f (m.app T x) at e2
    rw [e1, (hst h x).choose_spec, act.map_smul, (hst _ _).choose_spec, e2])

lemma actOfMono_spec {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (act : AAction (fppfO B S hS) M F)
    (m : G ⟶ F) (hm : ∀ T, Function.Injective (m.app T))
    (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) (t : G.obj T),
      ∃ t', m.app T t' = act.smul h (m.app T t)) :
    IsEquivariant (actOfMono act m hm hst) act m := fun h x => (hst h x).choose_spec

/-- An affine morphism is quasi-compact. -/
theorem isQuasiCompact_of_isAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : Space.IsAffineHom B S hS f) : Space.IsQuasiCompact B S hS f := by
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hF hG f ?_
  intro T hTaff h
  obtain ⟨W, p, q, hpb⟩ := hf ⟨T, hTaff⟩ h
  exact Space.isQuasiCompactSpace_of_iso B S hS
    (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback h f))
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _ W.property)

section Over

variable {A : BigFppfOver B S hS}

/-- Morphisms to an object whose structure map is a monomorphism are unique. -/
lemma hom_subsingleton (hA : Mono (structMap A)) (T : BigFppfOver B S hS) :
    Subsingleton (T ⟶ A) := by
  refine ⟨fun a b => ?_⟩
  apply (SCH).map_injective
  rw [← cancel_mono (structMap A)]
  have ha : (SCH).map a ≫ structMap A = structMap T :=
    congrArg (B.inclusion.map) (Over.w a)
  have hb : (SCH).map b ≫ structMap A = structMap T :=
    congrArg (B.inclusion.map) (Over.w b)
  rw [ha, hb]

/-- A morphism to an open of `S`, from the condition on the range. -/
theorem nonempty_hom_of_range {T : BigFppfOver B S hS}
    (hA : AlgebraicGeometry.IsOpenImmersion (structMap A))
    (h : Set.range (structMap T) ⊆ Set.range (structMap A)) : Nonempty (T ⟶ A) := by
  let l : (SCH).obj T ⟶ (SCH).obj A := AlgebraicGeometry.IsOpenImmersion.lift (structMap A) (structMap T) h
  have hl : l ≫ structMap A = structMap T := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (ObjectProperty.homMk l) ?_⟩
  apply B.inclusion.map_injective
  exact hl

end Over

section Main

variable [AddGroup.FG M]

lemma trivialOn_iff {Z : AddSubgroup M} {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T) :
    TrivialOn Z h ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  constructor
  · intro e z hz
    have := DFunLike.congr_fun e (Multiplicative.ofAdd (⟨z, hz⟩ : Z.toAddSubmonoid))
    simpa using this
  · intro e
    refine MonoidHom.ext fun w => ?_
    exact e _ (Multiplicative.toAdd w).2

/-- A point of the open orbit is fppf locally in the orbit of `p`. -/
theorem orbitLocal_of_mem {V W : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X)
    (p : X.obj (op V)) (s : Γ((SCH).obj V, ⊤)) (ι : W ⟶ V)
    (hunit : ∀ (T : BigFppfOver B S hS) (t : T ⟶ W), IsUnit (((SCH).map (t ≫ ι)).appTop.hom s))
    (hX : IsAlgebraicSpace B S hS X)
    (hc : Space.IsEtale B S hS (yoneda.map ι ≫ yonedaEquiv.symm p))
    {T : BigFppfOver B S hS} {x : X.obj (op T)}
    (hx : x ∈ (orbSub act (yoneda.map ι ≫ yonedaEquiv.symm p)).obj (op T)) :
    OrbitLocal act p s T x := by
  obtain ⟨U, q, r, e, hF, hL, hS'⟩ := exists_lift_of_mem_orbSub act _ hX hc hx
  refine ⟨_, Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hS' hF hL, ?_⟩
  rintro T' f ⟨U', z, q', hq', rfl⟩
  cases hq'
  refine ⟨z ≫ r.2 ≫ ι, APt.res z.op (topPt r.1), ?_, ?_⟩
  · have := hunit T' (z ≫ r.2)
    simpa [Category.assoc] using this
  · have e' : act.smul (topPt r.1) (X.map (r.2 ≫ ι).op p) = X.map q.op x := e
    rw [op_comp, Functor.map_comp_apply, ← e', act.map_smul, ← Functor.map_comp_apply, ← op_comp]

/-- **Affine stratum lemma, steps 4 to 8**: from an étale chart on whose open orbit the stabilizers are `D(M/Z)`,
lying over an affine open of `S`. -/
theorem exists_stable_affine_of_orbit {W : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X)
    (c : yoneda.obj W ⟶ X) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hc : Space.IsEtale B S hS c) (Z : AddSubgroup M)
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
    · rw [hfac]; exact isQuasiSeparated_of_mono Yf.ι r hsep
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

end Main

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.exists_stable_affine_of_orbit
