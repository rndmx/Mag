/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Limits

/-!
# Proposition 8.5: Tag 03I2 for the property "isomorphism"

Mayeux, *Algebraic Magnetism*, proof of Proposition 8.5: "`U^{N_i} → X^{N_i}` and `U^{N_c} → X^{N_c}` are étale and
surjective, the diagram is cartesian, the left vertical arrow is an isomorphism. Using [Tag 03I2] for the property
*isomorphism*, we deduce `X^{N_i} = X^{N_c}`".

* `AlgMag.isEffectiveDescent_isomorphisms`: the hypothesis of Tag 03I2 for `P = isomorphism`. Stacks does not
  record it for this `P`, so it is proved here, by gluing in a sheaf.
* `AlgMag.exists_ofLE_of_chart_03I2`: the printed step, through `Space.presheaf_of_surjectiveEtaleChart`.
  `AlgMag.exists_ofLE_of_chart` (on points) stays.
* `AlgMag.prop85_printed`: Proposition 8.5 through it, same hypotheses as `AlgMag.prop85`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- A morphism all of whose representable base changes are isomorphisms is an isomorphism; here only
the base change along the identity of a representable presheaf. -/
lemma isIso_of_presheaf_isomorphisms {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : BigFppfOver B S hS}
    {r : A ⟶ yoneda.obj c}
    (hr : ((MorphismProperty.isomorphisms Scheme.{u}).inverseImage (SCH)).presheaf r) : IsIso r := by
  have hp := hr.rep.isPullback (𝟙 _)
  have hi : IsIso ((SCH).map (hr.rep.snd (𝟙 _))) := hr.property_snd (𝟙 _)
  have hi' : IsIso (hr.rep.snd (𝟙 (yoneda.obj c))) := isIso_of_reflects_iso _ (SCH)
  have hi'' : IsIso (yoneda.map (hr.rep.snd (𝟙 (yoneda.obj c)))) := inferInstance
  have hf : IsIso (hr.rep.fst (𝟙 (yoneda.obj c))) := by
    have := hp.isIso_fst_of_isIso
    exact this
  have e : r = inv (hr.rep.fst (𝟙 (yoneda.obj c))) ≫ yoneda.map (hr.rep.snd (𝟙 _)) := by
    rw [IsIso.eq_inv_comp, hp.w, Category.comp_id]
  rw [e]
  infer_instance

/-- An isomorphism is representable with the property "isomorphism". -/
lemma presheaf_isomorphisms_of_isIso {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : A ⟶ C) [IsIso r] :
    ((MorphismProperty.isomorphisms Scheme.{u}).inverseImage (SCH)).presheaf r := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda r, ?_⟩
  intro a g a' g' r' hp
  have : IsIso (yoneda.map r') := hp.isIso_snd_of_isIso
  have : IsIso r' := isIso_of_reflects_iso _ yoneda
  exact (inferInstance : IsIso ((SCH).map r'))

/-- **The hypothesis of Tag 03I2 for the property "isomorphism"**: being an isomorphism descends along surjective
étale morphisms. -/
theorem isEffectiveDescent_isomorphisms :
    Space.IsEffectiveDescentAlongSurjectiveEtale B S hS (MorphismProperty.isomorphisms Scheme.{u}) := by
  intro X Yt f hX hY a c h q hqs hqe A m r sq hr
  have hrI : IsIso r := isIso_of_presheaf_isomorphisms hr
  have hX' : Presieve.IsSheaf (BigFppfOver.topology B S hS) X := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  have hY' : Presieve.IsSheaf (BigFppfOver.topology B S hS) Yt := (isSheaf_iff_isSheaf_of_type _ _).mp hY
  -- `X` has at most one point over `w ≫ q`
  have huniq : ∀ {W : BigFppfOver B S hS} (w : W ⟶ c) (x x' : X.obj (op W)),
      f.app _ x = h.app _ (w ≫ q) → f.app _ x' = h.app _ (w ≫ q) → x = x' := by
    intro W w x x' e e'
    have hT := (Types.isPullback_iff _ _ _ _).mp (sq.map ((evaluation _ _).obj (op W)))
    obtain ⟨z, hz, hzr⟩ := hT.2.2 x w (e.trans (by rfl))
    obtain ⟨z', hz', hzr'⟩ := hT.2.2 x' w (e'.trans (by rfl))
    have : z = z' := by
      have hb := (NatTrans.isIso_iff_isIso_app r).1 hrI (op W)
      exact ((isIso_iff_bijective _).1 hb).1 (hzr.trans hzr'.symm)
    rw [← hz, ← hz', this]
  -- and one, over `w ≫ q`
  have hex : ∀ {W : BigFppfOver B S hS} (w : W ⟶ c), ∃ x : X.obj (op W), f.app _ x = h.app _ (w ≫ q) := by
    intro W w
    have hb := (NatTrans.isIso_iff_isIso_app r).1 hrI (op W)
    obtain ⟨z, hz⟩ := ((isIso_iff_bijective _).1 hb).2 w
    have hT := (Types.isPullback_iff _ _ _ _).mp (sq.map ((evaluation _ _).obj (op W)))
    have e : f.app _ (m.app _ z) = (yoneda.map q ≫ h).app _ (r.app _ z) :=
      congrArg (fun k => k.app (op W) z) sq.w
    refine ⟨m.app _ z, e.trans ?_⟩
    rw [hz]
    rfl
  have hE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe
  have hS' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have hIso : IsIso (pullback.snd f h) := by
    refine (NatTrans.isIso_iff_isIso_app _).2 fun T => (isIso_iff_bijective _).2 ?_
    have hT := (Types.isPullback_iff _ _ _ _).mp
      ((IsPullback.of_hasPullback f h).map ((evaluation _ _).obj T))
    -- the cover of `T`
    have cover : ∀ t : unop T ⟶ a, ∃ (W : BigFppfOver B S hS) (π : W ⟶ unop T) (t' : W ⟶ c),
        π ≫ t = t' ≫ q ∧ Sieve.generate (Presieve.singleton π) ∈ BigFppfOver.topology B S hS (unop T) := by
      intro t
      let g₀ : yoneda.obj (unop T) ⟶ yoneda.obj a := yoneda.map t
      let R := hE.rep
      have hp := R.isPullback g₀
      have e' : Etale ((SCH).map (R.snd g₀)) := hE.property_snd g₀
      have s' : Surjective ((SCH).map (R.snd g₀)) :=
        (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1
          ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hp hS')
      let t₀ : R.pullback g₀ ⟶ c := (R.fst g₀).app (op (R.pullback g₀)) (𝟙 (R.pullback g₀))
      refine ⟨R.pullback g₀, R.snd g₀, t₀, ?_,
        Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _ s'
          (inferInstanceAs (Flat ((SCH).map _))) (inferInstanceAs (LocallyOfFinitePresentation ((SCH).map _)))⟩
      have := congrArg (fun k => k.app (op (R.pullback g₀)) (𝟙 _)) hp.w
      simpa [g₀] using this.symm
    constructor
    · intro p p' e
      refine hT.2.1 p p' ⟨?_, e⟩
      obtain ⟨W, π, t', hc, hmem⟩ := cover ((pullback.snd f h).app T p)
      refine (hX' _ hmem).isSeparatedFor.ext fun W' g hg => ?_
      obtain ⟨Y₀, g₁, _, ⟨⟩, rfl⟩ := hg
      have hw : ∀ z : (pullback f h).obj T, f.app T ((pullback.fst f h).app T z) =
          h.app T ((pullback.snd f h).app T z) := fun z =>
        congrArg (fun k => k.app T z) (pullback.condition (f := f) (g := h))
      have key : ∀ z : (pullback f h).obj T, (pullback.snd f h).app T z = (pullback.snd f h).app T p →
          f.app _ (X.map (g₁ ≫ π).op ((pullback.fst f h).app T z)) =
            h.app _ ((g₁ ≫ t') ≫ q) := by
        intro z hz
        rw [NatTrans.naturality_apply, hw z, ← NatTrans.naturality_apply]
        change h.app _ ((g₁ ≫ π) ≫ (pullback.snd f h).app T z) = _
        rw [hz, Category.assoc, hc, Category.assoc]
      have := huniq (g₁ ≫ t') _ _ (key p rfl) (key p' e.symm)
      simpa [FunctorToTypes.map_comp_apply] using this
    · intro t
      obtain ⟨W, π, t', hc, hmem⟩ := cover t
      obtain ⟨x', hx'⟩ := hex t'
      have hsf : (Presieve.ofArrows (fun _ : PUnit.{1} => W) (fun _ => π)).IsSheafFor X := by
        rw [Presieve.ofArrows_pUnit, Presieve.isSheafFor_iff_generate]
        exact hX' _ hmem
      obtain ⟨x, hx, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf (fun _ => x') (by
        intro _ _ W' g₁ g₂ e
        have e₁ : f.app _ (X.map g₁.op x') = h.app _ ((g₁ ≫ t') ≫ q) := by
          rw [NatTrans.naturality_apply, hx', ← NatTrans.naturality_apply]
          change h.app _ (g₁ ≫ t' ≫ q) = _
          rw [Category.assoc]
        have e₂ : f.app _ (X.map g₂.op x') = h.app _ ((g₁ ≫ t') ≫ q) := by
          rw [NatTrans.naturality_apply, hx', ← NatTrans.naturality_apply]
          change h.app _ (g₂ ≫ t' ≫ q) = _
          rw [← hc, ← Category.assoc, ← e, Category.assoc, hc, Category.assoc]
        exact huniq _ _ _ e₁ e₂)
      have hxf : f.app T x = h.app T t := by
        refine (hY' _ hmem).isSeparatedFor.ext fun W' g hg => ?_
        obtain ⟨Y₀, g₁, _, ⟨⟩, rfl⟩ := hg
        have hx₁ : X.map π.op x = x' := hx PUnit.unit
        have e₁ : Yt.map π.op (f.app T x) = f.app _ x' := by
          rw [← hx₁, NatTrans.naturality_apply]
        have e₂ : Yt.map π.op (h.app T t) = h.app _ (t' ≫ q) := by
          rw [← hc]
          exact (NatTrans.naturality_apply h π.op t).symm
        change Yt.map (g₁ ≫ π).op _ = Yt.map (g₁ ≫ π).op _
        simp only [op_comp, FunctorToTypes.map_comp_apply]
        rw [e₁, e₂, hx']
      obtain ⟨z, -, hz⟩ := hT.2.2 x t hxf
      exact ⟨z, hz⟩
  exact presheaf_isomorphisms_of_isIso _

section Main

variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
  {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {A' : Type u} {V : A' → ((BigFppfOver.toScheme B S hS).obj U).Opens}

set_option maxHeartbeats 1000000 in
/-- **The descent step of Proposition 8.5**, as printed: the chart `U^{N''} → X^{N''}` is étale and surjective,
the base change of `X^{N'} → X^{N''}` along it is the isomorphism `U^{N'} = U^{N''}`, so Tag 03I2 for the property
"isomorphism" applies. `X^{N'}`, `X^{N''}` are represented (Theorem 8.3). -/
theorem exists_ofLE_of_chart_03I2 (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (g : yoneda.obj U ⟶ X) {Z : AddSubgroup M} (hg : IsZFPRAtlas actU actX g Z)
    (hV : IsAffineDecomposition actU V) {N' N'' : AddSubmonoid M} (h : N' ≤ N'')
    (hF : IsFace Z.toAddSubmonoid N'') (hl : IsLimitPreserving X)
    {P' P'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (r' : RepresentsAttractor actX N' P') (r'' : RepresentsAttractor actX N'' P'')
    (a' : IsAlgebraicSpace B S hS P') (a'' : IsAlgebraicSpace B S hS P'')
    (hstep : ∀ {T : BigFppfOver B S hS} (φ : AttractorPt actU N'' T),
      ∃ φ' : AttractorPt actU N' T, φ'.toPoint = φ.toPoint)
    {T : BigFppfOver B S hS} (ψ : AttractorPt actX N'' T) :
    ∃ ξ : AttractorPt actX N' T, AttractorPt.ofLE h ξ = ψ := by
  classical
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hshU : Presieve.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) :=
    BigFppfOver.isSheaf_of_type_yoneda_obj U
  have hcov : ∀ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T := fun a => extSieve_mem Z a
  let f : EquivariantHom actU actX := ⟨g, fun {T} h x => hg.atlas.equivariant h x⟩
  have hc : IsFaceCartesian f hF := by
    refine isFaceCartesian_of_pieces hsh hV f _ fun b => ?_
    have hA : IsAffineHom (openObj (V b)).hom.hom := hV.isAffineHom b
    exact isFaceCartesian_of_separated hX hsep hl _ (isEtale_piece_comp hg.atlas.etale) _
  obtain ⟨rN⟩ := exists_chartAttr hV N''
  -- `z : X^{N'} → X^{N''}`
  let z : P' ⟶ P'' :=
    { app := fun W => ↾ fun p => (r''.equiv (unop W)).symm (AttractorPt.ofLE h (r'.equiv (unop W) p))
      naturality := fun W W₁ s => by
        ext p
        apply (r''.equiv (unop W₁)).injective
        change r''.equiv _ ((r''.equiv _).symm _) = r''.equiv _ (P''.map s ((r''.equiv _).symm _))
        have e := r''.naturality s.unop ((r''.equiv (unop W)).symm (AttractorPt.ofLE h (r'.equiv (unop W) p)))
        have e' := r'.naturality s.unop p
        rw [Equiv.apply_symm_apply] at e ⊢
        refine Eq.trans ?_ e.symm
        exact congrArg (AttractorPt.ofLE h) e' }
  have hz : ∀ W p, r''.equiv W (z.app (op W) p) = AttractorPt.ofLE h (r'.equiv W p) := fun W p =>
    Equiv.apply_symm_apply _ _
  have hzinj : ∀ W, Function.Injective (z.app (op W)) := by
    intro W p p' e
    apply (r'.equiv W).injective
    apply ofLE_injective hX hsep h W
    rw [← hz, ← hz, e]
  -- the chart `U^{N''} → X^{N''}`
  let c : yoneda.obj rN.W ⟶ P'' :=
    { app := fun W => ↾ fun y => (r''.equiv (unop W)).symm (AttractorPt.push f (rN.r.equiv (unop W) y))
      naturality := fun W W₁ s => by
        ext y
        apply (r''.equiv (unop W₁)).injective
        change r''.equiv _ ((r''.equiv _).symm _) = r''.equiv _ (P''.map s ((r''.equiv _).symm _))
        have e := r''.naturality s.unop ((r''.equiv (unop W)).symm (AttractorPt.push f (rN.r.equiv (unop W) y)))
        have e' := rN.r.naturality s.unop y
        rw [Equiv.apply_symm_apply] at e ⊢
        refine Eq.trans ?_ e.symm
        exact congrArg (AttractorPt.push f) e' }
  have hcv : ∀ W y, r''.equiv W (c.app (op W) y) = AttractorPt.push f (rN.r.equiv W y) := fun W y =>
    Equiv.apply_symm_apply _ _
  -- the point of `X` under `X^{N''}`
  let pr : P'' ⟶ X :=
    { app := fun W => ↾ fun p => (AttractorPt.ofFace hF (r''.equiv (unop W) p)).toPoint
      naturality := fun W W₁ s => by
        ext p
        change (AttractorPt.ofFace hF (r''.equiv _ (P''.map s p))).toPoint = X.map s _
        rw [show P''.map s p = P''.map s.unop.op p from rfl, r''.naturality s.unop p, ofFace_baseChange]
        exact AttractorPt.toPoint_baseChange s.unop _ }
  let eU := fun W => attractorFixedEquivOfCover (act := actU) hshU hcov W
  let eX := fun W => attractorFixedEquivOfCover (act := actX) hsh hcov W
  have hUinj : ∀ W (φ χ : AttractorPt actU Z.toAddSubmonoid W), φ.toPoint = χ.toPoint → φ = χ := by
    intro W φ χ e
    exact (eU W).symm.injective (Subtype.ext e)
  have hXinj : ∀ W (φ χ : AttractorPt actX Z.toAddSubmonoid W), φ.toPoint = χ.toPoint → φ = χ := by
    intro W φ χ e
    exact (eX W).symm.injective (Subtype.ext e)
  -- the chart is the base change of `U → X`, along `X^{N''} → X`
  let vt : yoneda.obj rN.W ⟶ yoneda.obj U :=
    { app := fun W => ↾ fun y => (AttractorPt.ofFace hF (rN.r.equiv (unop W) y)).toPoint
      naturality := fun W W₁ s => by
        ext y
        change (AttractorPt.ofFace hF (rN.r.equiv _ ((yoneda.obj rN.W).map s y))).toPoint =
          (yoneda.obj U).map s _
        rw [show (yoneda.obj rN.W).map s y = (yoneda.obj rN.W).map s.unop.op y from rfl,
          rN.r.naturality s.unop y, ofFace_baseChange]
        exact AttractorPt.toPoint_baseChange s.unop _ }
  have hsq : IsPullback vt c g pr := by
    refine IsPullback.of_forall_isPullback_app fun W => ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · refine ConcreteCategory.hom_ext _ _ fun y => ?_
      change g.app W (AttractorPt.ofFace hF (rN.r.equiv (unop W) y)).toPoint =
        (AttractorPt.ofFace hF (r''.equiv (unop W) (c.app W y))).toPoint
      have e := hcv (unop W) y
      change r''.equiv (unop W) (c.app W y) = _ at e
      rw [e]
      rfl
    · rintro y y' ⟨e₁, e₂⟩
      apply (rN.r.equiv (unop W)).injective
      apply (hc (unop W)).1
      refine Subtype.ext (Prod.ext ?_ ?_)
      · have := congrArg (r''.equiv (unop W)) e₂
        exact (hcv (unop W) y).symm.trans (this.trans (hcv (unop W) y'))
      · exact hUinj _ _ _ e₁
    · intro u p e
      let u' : unop W ⟶ U := u
      have hfix : u' ∈ (fixedPoints (quotientAction actU Z)).obj (op (unop W)) := by
        refine (isFPR_iff (IsEquivariant.comap (actU := actU) (actX := actX) (f := g)
          hg.atlas.equivariant (QuotientAddGroup.mk' Z))).1 hg.isZFPR (op (unop W)) u' ?_
        have e' : g.app W u = (AttractorPt.ofFace hF (r''.equiv (unop W) p)).toPoint := e
        change g.app W u ∈ _
        rw [e']
        exact AttractorPt.toPoint_mem_fixedPoints _
      let w := eU (unop W) ⟨u', hfix⟩
      have hw : w.toPoint = u' := congrArg Subtype.val ((eU (unop W)).symm_apply_apply ⟨u', hfix⟩)
      have hfc : AttractorPt.ofFace hF (r''.equiv (unop W) p) = AttractorPt.push f w := by
        apply hXinj
        change _ = g.app W w.toPoint
        rw [hw]
        exact e.symm
      obtain ⟨v, hv⟩ := (hc (unop W)).2 ⟨(r''.equiv (unop W) p, w), hfc⟩
      have hv₁ : AttractorPt.push f v = r''.equiv (unop W) p := congrArg (fun q => q.1.1) hv
      have hv₂ : AttractorPt.ofFace hF v = w := congrArg (fun q => q.1.2) hv
      refine ⟨(rN.r.equiv (unop W)).symm v, ?_, ?_⟩
      · change (AttractorPt.ofFace hF (rN.r.equiv _ ((rN.r.equiv _).symm v))).toPoint = u'
        rw [Equiv.apply_symm_apply, hv₂, hw]
      · apply (r''.equiv (unop W)).injective
        refine (hcv (unop W) _).trans ?_
        rw [Equiv.apply_symm_apply, hv₁]
  have he := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hg.atlas.etale
  have hs := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hg.atlas.surjective
  -- the base change of `z` along the chart is the isomorphism `U^{N'} = U^{N''}`
  have hlift : ∀ W (y : (yoneda.obj rN.W).obj (op W)), ∃ p : P'.obj (op W), z.app (op W) p = c.app (op W) y := by
    intro W y
    obtain ⟨φ', hφ'⟩ := hstep (rN.r.equiv W y)
    refine ⟨(r'.equiv W).symm (AttractorPt.push f φ'), ?_⟩
    apply (r''.equiv W).injective
    rw [hz, hcv, Equiv.apply_symm_apply]
    have hle : AttractorPt.ofLE h φ' = rN.r.equiv W y :=
      toPoint_injective_U hV ((AttractorPt.toPoint_ofLE h φ').trans hφ')
    rw [← hle]
    rfl
  choose mf hmf using hlift
  let m : yoneda.obj rN.W ⟶ P' :=
    { app := fun W => ↾ mf (unop W)
      naturality := fun W W₁ s => by
        ext y
        apply hzinj (unop W₁)
        change z.app _ (mf _ _) = z.app _ (P'.map s (mf _ _))
        rw [hmf, NatTrans.naturality_apply z s, hmf]
        exact (NatTrans.naturality_apply c s y) }
  have hsqi : IsPullback m (𝟙 _) z c := by
    refine IsPullback.of_forall_isPullback_app fun W => ?_
    refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ConcreteCategory.hom_ext _ _ fun y => hmf (unop W) y
    · rintro y y' ⟨-, e⟩
      exact e
    · intro p y e
      exact ⟨y, hzinj (unop W) ((hmf (unop W) y).trans e.symm), rfl⟩
  have hsn : IsIso (pullback.snd z c) := by
    have e : pullback.snd z c = hsqi.isoPullback.inv ≫ 𝟙 _ := by
      rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
    rw [e]
    infer_instance
  have hz03 := Space.presheaf_of_surjectiveEtaleChart isEffectiveDescent_isomorphisms a'.isSheaf a''.isSheaf
    hs he (presheaf_isomorphisms_of_isIso (pullback.snd z c))
  -- `z` is surjective
  let p := (r''.equiv T).symm ψ
  let gp : yoneda.obj T ⟶ P'' := yonedaEquiv.symm p
  have hb := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_hasPullback z gp) hz03
  have hI := isIso_of_presheaf_isomorphisms hb
  have hbi := (NatTrans.isIso_iff_isIso_app _).1 hI (op T)
  obtain ⟨q, hq⟩ := ((isIso_iff_bijective _).1 hbi).2 (𝟙 T)
  refine ⟨r'.equiv T ((pullback.fst z gp).app _ q), ?_⟩
  have hcond : z.app _ ((pullback.fst z gp).app _ q) = gp.app _ ((pullback.snd z gp).app _ q) :=
    congrArg (fun k => k.app (op T) q) (pullback.condition (f := z) (g := gp))
  rw [← hz, hcond, hq]
  have : gp.app (op T) (𝟙 T) = p := by
    simp [gp, yonedaEquiv]
  rw [this]
  exact Equiv.apply_symm_apply _ _


set_option maxHeartbeats 1000000 in
/-- **Proposition 8.5**, printed proof: the same statement as `AlgMag.prop85`, the step `X^{N_i} = X^{N_c}` being
Tag 03I2 for the property "isomorphism". -/
theorem prop85_printed [CompactSpace S] (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) (N : AddSubmonoid M)
    (hat : ∃ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
      (g : yoneda.obj U ⟶ X), IsZFPRAtlas actU actX g (unitsSub N) ∧
        HasFiniteAffineDecomposition actU) :
    ∃ (Nc : AddSubmonoid M) (hc : Nc ≤ N), Nc.FG ∧ unitsSub Nc = unitsSub N ∧
      ∀ T : BigFppfOver B S hS, Function.Bijective (AttractorPt.ofLE (act := actX) (T := T) hc) := by
  obtain ⟨U, actU, g, hg, A', hA', V, hV⟩ := hat
  have hl := isLimitPreserving_of_lfp hX hfp
  have hU := lfp_structMap hfp g hg.atlas.etale
  obtain ⟨κ, Uk, D, hUk, hD⟩ := exists_finset_degrees hU hV
  haveI : Countable M := countable_of_fg83
  obtain ⟨ν, hν⟩ := exists_surjective_nat N
  obtain ⟨c, hc⟩ := exists_index N ν hν D
  have hle := chainN337_le N ν c
  have hZ : ∀ i, (unitsSub N).toAddSubmonoid ≤ chainN337 N ν i := fun i => by
    rw [chainN337_def]; exact le_sup_left
  have hrep : ∀ i, Nonempty (Thm83Repr actX (chainN337 N ν i)) := fun i => by
    refine thm83_repr hX hsep _ ⟨U, actU, g, ?_⟩ (Or.inl (chainN337_fg N ν i))
    rw [unitsSub_of_between (hZ i) (chainN337_le N ν i)]
    exact hg
  have hstep : ∀ {i} (hi : c ≤ i) {T : BigFppfOver B S hS} (ψ : AttractorPt actX (chainN337 N ν i) T),
      ∃ ξ : AttractorPt actX (chainN337 N ν c) T, AttractorPt.ofLE (chainN337_mono N ν hi) ξ = ψ := by
    intro i hi T ψ
    obtain ⟨ri⟩ := hrep i
    obtain ⟨rc⟩ := hrep c
    refine exists_ofLE_of_chart_03I2 hX hsep g hg hV (chainN337_mono N ν hi)
      (isFace_between (hZ i) (chainN337_le N ν i)) hl rc.rP ri.rP rc.algP ri.algP (fun φ => ?_) ψ
    exact exists_att_of_ideal_le hV Uk hUk
      (hD _ _ fun d hd hdi => hc d hd (chainN337_le N ν i hdi)) φ
  have hshc := isSheaf_attractor actX (chainN337 N ν c) _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
  have hshN := isSheaf_attractor actX N _ ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
  refine ⟨chainN337 N ν c, hle, chainN337_fg N ν c, unitsSub_of_between (hZ c) hle, fun T => ?_⟩
  refine ⟨ofLE_injective hX hsep hle T, fun ψ => ?_⟩
  obtain ⟨I, W, π, hW, hmem⟩ := exists_affine_cover T
  have hloc : ∀ j, ∃ ξ : AttractorPt actX (chainN337 N ν c) (W j),
      AttractorPt.ofLE hle ξ = AttractorPt.baseChange (π j) ψ := by
    intro j
    haveI : IsAffine ((SCH).obj (W j)) := hW j
    obtain ⟨P, hP, φ', hP₀, hPf, hφ'⟩ := prop337 hX hsep hfp hle (chainN337_fg N ν c)
      (AttractorPt.baseChange (π j) ψ)
    obtain ⟨i₀, hi₀⟩ := exists_le_chain N ν hν hP hPf
    let i := max c i₀
    have hPi : P ≤ chainN337 N ν i := hi₀.trans (chainN337_mono N ν (le_max_right _ _))
    obtain ⟨ξ, hξ⟩ := hstep (le_max_left c i₀) (AttractorPt.ofLE hPi φ')
    refine ⟨ξ, ?_⟩
    rw [← hφ']
    have := congrArg (AttractorPt.ofLE (chainN337_le N ν i)) hξ
    exact this
  choose ξ hξ using hloc
  have hsf : (Presieve.ofArrows W π).IsSheafFor (attractor actX (chainN337 N ν c)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hshc _ hmem
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf ξ (by
    intro a b Y ga gb e
    apply ofLE_injective hX hsep hle Y
    change AttractorPt.baseChange ga (AttractorPt.ofLE hle (ξ a)) =
      AttractorPt.baseChange gb (AttractorPt.ofLE hle (ξ b))
    rw [hξ, hξ]
    change AttractorPt.baseChange (ga ≫ π a) ψ = AttractorPt.baseChange (gb ≫ π b) ψ
    rw [e])
  refine ⟨t, (hshN _ hmem).isSeparatedFor.ext fun Y p hp => ?_⟩
  obtain ⟨_, r, s', ⟨j⟩, rfl⟩ := hp
  have e : AttractorPt.baseChange (π j) (AttractorPt.ofLE hle t) = AttractorPt.baseChange (π j) ψ :=
    (congrArg (AttractorPt.ofLE hle) (ht j)).trans (hξ j)
  exact congrArg (AttractorPt.baseChange r) e

end Main

end AlgMag

#print axioms AlgMag.isEffectiveDescent_isomorphisms
#print axioms AlgMag.prop85_printed
