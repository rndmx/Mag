/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3IntersectionsWeak
import AlgMag.Sec8Limits

/-!
# Fact 3.34, Theorem 15.3, Proposition 15.5, Theorem 15.4 (ii), examples of §15, final forms

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §3 and §15.

## Main results

* `AlgMag.chartsOfFiniteType_of_lfp`: an étale chart of a space locally of finite presentation over `S`
  is locally of finite type over `S`: `ChartsOfFiniteType` is not an added hypothesis.
* `AlgMag.fact334_strong`: **Fact 3.34 (ii)** for an arbitrary family, with one `S`-affine atlas which is
  `(⋂ J)^×`-FPR for the finite subfamilies `J`. `S` is arbitrary.
* `AlgMag.thm153_strong`: **Theorem 15.3** under the same assumption.
* `AlgMag.prop155_printed`: **Proposition 15.5** along the printed route, through Theorem 8.3 and the
  étale surjective charts `U^N → X^N` (`AlgMag.chartToAttr_isPullback`). `AlgMag.prop155` stays as an
  alternative.
* `AlgMag.thm154_ii_lfp`, `AlgMag.rem156_lfp`, `AlgMag.thm154_ii_of_linearizable`,
  `AlgMag.thm154_ii_of_linearizable_qc`: **Theorem 15.4 (ii)**, **Remark 15.6**, and the Zariski locally
  linearizable case through **Fact 7.3**.
* Examples after **Fact 15.11**, (i), (ii), (iii), (v). Example (iv) is `AlgMag.pureMagnets_p1`.

## Departure in Proposition 15.5

The printed steps "`q` is étale by Tag 0AHE" and "an étale universally injective surjection is an
isomorphism, Tag 05W5" are replaced by their common core: `q` is a monomorphism of sheaves, and it is
locally surjective since `U^L → X^L` is an étale surjection factoring through it. Corollary 11.6 is used
for `U → X` only, where it follows from the Cartesian squares of Proposition 5.1.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
set_option linter.unusedSectionVars false

namespace AlgMag

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
local notation "Sch" => BigFppfOver.toScheme B S hS
attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Strong

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
variable {U : BigFppfOver B S hS} [IsAffineHom U.hom.hom]
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
  {f : yoneda.obj U ⟶ X}

/-- The geometric step of **Proposition 15.5** with `L^×`-FPR only: a point of `X^L` lifts, after a
surjective étale base change, to a point of `U^L`. -/
theorem exists_atlas_lift_of_isZFPR (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    {L : AddSubmonoid M} (hb : L.FG ∨ IsLimitPreserving X) (hat : IsEquivariantAtlas aU aX f)
    (hZ : IsZFPR hat.equivariant (unitsSubgroup L)) {T : BigFppfOver B S hS} (x : AttractorPt aX L T) :
    ∃ (T' : BigFppfOver B S hS) (q : T' ⟶ T) (w : AttractorPt aU L T'),
      Surjective ((Sch).map q) ∧ Etale ((Sch).map q) ∧
      AttractorPt.push ⟨f, hat.equivariant⟩ w = AttractorPt.baseChange q x := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  let F : EquivariantHom aU aX := ⟨f, hat.equivariant⟩
  let Z := unitsSubgroup L
  have hQ : IsFace Z.toAddSubmonoid L := isFace_units L
  let x₀ : AttractorPt aX Z.toAddSubmonoid T := AttractorPt.ofFace hQ x
  let g₀ : yoneda.obj T ⟶ X := yonedaEquiv.symm x₀.toPoint
  let rep := hat.etale.rep
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
    refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := f) hat.equivariant
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
  have hcart : IsFaceCartesian F hQ := by
    rcases hb with hL | hl
    · exact isFaceCartesian_of_fg hX hsep F (isEtale_of_atlas hat) hQ hL
    · exact isFaceCartesian_of_separated hX hsep hl F (isEtale_of_atlas hat) hQ
  obtain ⟨w, hw⟩ := (hcart T').2 ⟨(AttractorPt.baseChange q x, wZ), hpush⟩
  exact ⟨T', q, w, hat.surjective.property_snd g₀, hat.etale.property_snd g₀,
    congrArg (fun p => p.1.1) hw⟩

/-- The proof of **Theorem 15.4 (i)** over an affine `T₀`, with no assumption on `S`: a finite set
`E ⊆ M` such that every point of `U^N` over `T₀` lies in `U^{⟨N ∩ E⟩}`. -/
theorem exists_closure_of_affine_base (T₀ : BigFppfOver B S hS) [IsAffine ((Sch).obj T₀)]
    [LocallyOfFiniteType U.hom.hom] (aU : AAction (fppfO B S hS) M (yoneda.obj U)) :
    ∃ E : Set M, E.Finite ∧ ∀ (N : AddSubmonoid M) {Y : BigFppfOver B S hS} (_ : Y ⟶ T₀)
      (φ : AttractorPt aU N Y),
      ∃ φ' : AttractorPt aU (AddSubmonoid.closure ((N : Set M) ∩ E)) Y, φ'.toPoint = φ.toPoint := by
  obtain ⟨γ, hγ, hγp⟩ := exists_gamma T₀ U aU
  obtain ⟨G, E, hE, hG, hEd⟩ := exists_chart_degrees T₀ U γ
  refine ⟨E, hE, fun N Y s φ => ?_⟩
  obtain ⟨I, V, π, hV, hcov⟩ := exists_affine_cover Y
  refine exists_toPoint_of_sieve (BigFppfOver.isSheaf_of_type_yoneda_obj U)
    (fun T => toPoint_injective_affine _ T) _ _ hcov ?_
  rintro Z g ⟨W, a, b, ⟨i⟩, rfl⟩
  have := hV i
  obtain ⟨φ', hφ'⟩ := exists_closure_inter (aU := aU) (Y := V i) (π i ≫ s) hG hEd hγ hγp
    (AttractorPt.baseChange (π i) φ)
  refine ⟨AttractorPt.baseChange a φ', ?_⟩
  rw [AttractorPt.toPoint_baseChange, hφ', AttractorPt.toPoint_baseChange,
    ← Functor.map_comp_apply, ← op_comp]

/-- **Fact 3.34 (ii)** for an arbitrary family. `M` is a finitely generated abelian group, `X` a separated
algebraic space, limit preserving, and `U → X` one `S`-affine atlas, locally of finite type over `S`,
which is `(⋂ J)^×`-FPR for the finite nonempty subfamilies `J`. The base `S` is arbitrary, and FPR for
`(⋂ I)^×` itself is not needed.

As in the printed proof one passes to finite subfamilies. The printed colimit step is replaced by: over
an affine `T`, the finitely many degrees `E` of generators of `U_T` see only finitely many subsets
`N ∩ E`, so a single finite `J` has `(⋂ J) ∩ E ⊆ N` for all `N` in the family. -/
theorem fact334_strong [LocallyOfFiniteType U.hom.hom] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) (hat : IsEquivariantAtlas aU aX f)
    {s : Set (AddSubmonoid M)}
    (hZ : ∀ J ⊆ s, J.Finite → J.Nonempty → IsZFPR hat.equivariant (unitsSubgroup (sInf J)))
    (y) (hne : s.Nonempty) (hy : ∀ N ∈ s, attractorImage aX N = y) :
    attractorImage aX (sInf s) = y := by
  obtain ⟨N₀, hN₀⟩ := id hne
  refine le_antisymm ((attractorImage_monotone aX (sInf_le hN₀)).trans_eq (hy N₀ hN₀)) ?_
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hinj := fun (P : AddSubmonoid M) T => attractor_toPoint_injective_sep (aX := aX) hX hsep P T
  have key : ∀ (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (t : X.obj (op T)),
      t ∈ y T → ∃ φ : AttractorPt aX (sInf s) T, φ.toPoint = t := by
    intro T _ t ht
    obtain ⟨E, hE, hcl⟩ := exists_closure_of_affine_base T aU
    classical
    have hP : ((fun N : AddSubmonoid M => (N : Set M) ∩ E) '' s).Finite :=
      (hE.finite_subsets).subset (by rintro _ ⟨N, -, rfl⟩; exact Set.inter_subset_right)
    have hrep : ∀ p : ((fun N : AddSubmonoid M => (N : Set M) ∩ E) '' s),
        ∃ N ∈ s, (N : Set M) ∩ E = p.1 := fun p => p.2
    choose r hrs hre using hrep
    have := hP.to_subtype
    let J : Set (AddSubmonoid M) := insert N₀ (Set.range r)
    have hJs : J ⊆ s := Set.insert_subset hN₀ (by rintro _ ⟨p, rfl⟩; exact hrs p)
    have hJf : J.Finite := (Set.finite_range r).insert _
    have hJn : J.Nonempty := Set.insert_nonempty _ _
    have hJy : attractorImage aX (sInf J) = y :=
      fact334_finite_weak hX hsep hlim hJf
        (fun J' hJ' hn => ⟨U, aU, f, hat, hZ J' (hJ'.trans hJs) (hJf.subset hJ') hn⟩)
        y hJn fun N hN => hy N (hJs hN)
    rw [← hJy] at ht
    obtain ⟨ψ, rfl⟩ := ht
    obtain ⟨T', q, w, hs, he, hw⟩ := exists_atlas_lift_of_isZFPR hX hsep (Or.inr hlim) hat
      (hZ J hJs hJf hJn) ψ
    obtain ⟨v, hv⟩ := hcl (sInf J) q w
    have hle : AddSubmonoid.closure (((sInf J : AddSubmonoid M) : Set M) ∩ E) ≤ sInf s := by
      refine AddSubmonoid.closure_le.mpr fun m hm => ?_
      refine (AddSubmonoid.mem_sInf.mpr fun N hN => ?_)
      have hNp : (N : Set M) ∩ E ∈ ((fun N : AddSubmonoid M => (N : Set M) ∩ E) '' s) := ⟨N, hN, rfl⟩
      have e := hre ⟨_, hNp⟩
      have h1 : m ∈ (r ⟨_, hNp⟩ : AddSubmonoid M) :=
        (AddSubmonoid.mem_sInf.mp hm.1) _ (Set.mem_insert_of_mem _ ⟨_, rfl⟩)
      have h2 : m ∈ ((r ⟨_, hNp⟩ : AddSubmonoid M) : Set M) ∩ E := ⟨h1, hm.2⟩
      rw [e] at h2
      exact h2.1
    refine exists_toPoint_of_sieve hsX (hinj _) _ _
      (Space.sieve_generate_singleton_mem_topology_over B S hS q hs he) ?_
    rintro Y g ⟨W, a, b, ⟨⟩, rfl⟩
    refine ⟨AttractorPt.baseChange a (AttractorPt.ofLE hle
      (AttractorPt.push ⟨f, hat.equivariant⟩ v)), ?_⟩
    have h1 : (AttractorPt.push ⟨f, hat.equivariant⟩ v).toPoint =
        (AttractorPt.baseChange q ψ).toPoint := by
      rw [← hw]
      exact congrArg (f.app (op T')) hv
    rw [AttractorPt.toPoint_baseChange, AttractorPt.toPoint_ofLE, h1, AttractorPt.toPoint_baseChange,
      ← Functor.map_comp_apply, ← op_comp]
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

/-- `AttractorOrder` for `X` with one `S`-affine atlas, FPR for the units of the intersection of every
finite set of magnets having a common attractor. -/
theorem attractorOrder_strong [LocallyOfFiniteType U.hom.hom] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) (hat : IsEquivariantAtlas aU aX f)
    (hZ : ∀ J : Set (AddSubmonoid M), J.Finite → J.Nonempty →
      (∀ N ∈ J, ∀ L ∈ J, attractorImage aX N = attractorImage aX L) →
      IsZFPR hat.equivariant (unitsSubgroup (sInf J))) :
    AttractorOrder (attractorImage aX) where
  monotone := attractorImage_monotone aX
  sInf_of_const _ y hne hy := fact334_strong hX hsep hlim hat
    (fun J hJ hf hn => hZ J hf hn fun N hN L hL => (hy N (hJ hN)).trans (hy L (hJ hL)).symm) y hne hy

/-- **Theorem 15.3**: the bijection `N ↦ X^N` from pure magnets to attractors, with inverse
`Y ↦ ⋂ {N | X^N = Y}`, with one `S`-affine atlas and any base `S`. -/
noncomputable def thm153_strong [LocallyOfFiniteType U.hom.hom] (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) (hat : IsEquivariantAtlas aU aX f)
    (hZ : ∀ J : Set (AddSubmonoid M), J.Finite → J.Nonempty →
      (∀ N ∈ J, ∀ L ∈ J, attractorImage aX N = attractorImage aX L) →
      IsZFPR hat.equivariant (unitsSubgroup (sInf J))) :
    pureMagnets (attractorImage aX) ≃ Set.range (attractorImage aX) :=
  pureEquivRange (attractorOrder_strong hX hsep hlim hat hZ)

end Strong

section LFP

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale chart of an algebraic space locally of finite presentation over `S` is locally of finite
type over `S`. So `ChartsOfFiniteType` follows from the hypothesis of Theorem 15.4. -/
theorem chartsOfFiniteType_of_lfp
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) : ChartsOfFiniteType X := by
  intro V φ hφ
  have hT : IsIso (terminal.from (yoneda.obj (siteTop : BigFppfOver B S hS))) := by
    have hl : IsTerminal (yoneda.obj (siteTop : BigFppfOver B S hS)) :=
      IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
    have e : terminal.from (yoneda.obj (siteTop : BigFppfOver B S hS)) =
        (hl.uniqueUpToIso terminalIsTerminal).hom := Subsingleton.elim _ _
    rw [e]
    infer_instance
  have := Space.isMultiplicative_presheaf_etale B S hS
  have hb := hfp V siteTop φ (terminal.from (yoneda.obj (siteTop : BigFppfOver B S hS)))
    (Over.mkIdTerminal.from V : V ⟶ siteTop) hφ (MorphismProperty.of_isIso _ _)
    (Subsingleton.elim _ _)
  have e : (Sch).map (Over.mkIdTerminal.from V : V ⟶ siteTop) = V.hom.hom := by
    have := site_w (Over.mkIdTerminal.from V : V ⟶ siteTop)
    simp
  have hl : LocallyOfFinitePresentation ((Sch).map (Over.mkIdTerminal.from V : V ⟶ siteTop)) := hb
  rw [e] at hl
  infer_instance

end LFP

section Printed

variable {M : Type u} [AddCommGroup M] [AddMonoid.FG M]
variable {U : BigFppfOver B S hS}
  {aU : AAction (fppfO B S hS) M (yoneda.obj U)}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}

/-- The morphism `U^N → X^N` of represented attractors. -/
noncomputable def chartToAttr (F : EquivariantHom aU aX) {N : AddSubmonoid M}
    {W : BigFppfOver B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rW : RepresentsAttractor aU N (yoneda.obj W)) (r : RepresentsAttractor aX N P) :
    yoneda.obj W ⟶ P where
  app T := ↾ fun v => (r.equiv (unop T)).symm (AttractorPt.push F (rW.equiv (unop T) v))
  naturality T T' s := by
    refine ConcreteCategory.hom_ext _ _ fun v => ?_
    apply (r.equiv (unop T')).injective
    change r.equiv _ ((r.equiv _).symm (AttractorPt.push F (rW.equiv (unop T')
        ((yoneda.obj W).map s.unop.op v)))) =
      r.equiv (unop T') (P.map s.unop.op ((r.equiv (unop T)).symm
        (AttractorPt.push F (rW.equiv (unop T) v))))
    rw [Equiv.apply_symm_apply, r.naturality, Equiv.apply_symm_apply, rW.naturality]
    rfl

lemma chartToAttr_equiv (F : EquivariantHom aU aX) {N : AddSubmonoid M}
    {W : BigFppfOver B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rW : RepresentsAttractor aU N (yoneda.obj W)) (r : RepresentsAttractor aX N P)
    (T : BigFppfOver B S hS) (v : T ⟶ W) :
    r.equiv T ((chartToAttr F rW r).app (op T) v) = AttractorPt.push F (rW.equiv T v) :=
  Equiv.apply_symm_apply _ _

/-- The limit morphism `X^N → X^{N^×} ⊆ X` of a represented attractor. -/
noncomputable def limitToX {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {act : AAction (fppfO B S hS) M Y} {N : AddSubmonoid M}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (r : RepresentsAttractor act N P) : P ⟶ Y where
  app T := ↾ fun p => (AttractorPt.ofFace (isFace_units N) (r.equiv (unop T) p)).toPoint
  naturality T T' s := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    change (AttractorPt.ofFace (isFace_units N) (r.equiv (unop T') (P.map s.unop.op p))).toPoint =
      Y.map s (AttractorPt.ofFace (isFace_units N) (r.equiv (unop T) p)).toPoint
    rw [r.naturality s.unop p, ofFace_baseChange, AttractorPt.toPoint_baseChange]
    rfl

/-- The diagram in the proof of **Proposition 15.5**, by **Proposition 5.1** and `N^×`-FPR: the square
with sides `U^N → X^N`, `U^N → U`, `X^N → X`, `U → X` (the last three being the limits and `f`) is
Cartesian. -/
theorem chartToAttr_isPullback {f : yoneda.obj U ⟶ X} (hat : IsEquivariantAtlas aU aX f)
    {N : AddSubmonoid M} (hZ : IsZFPR hat.equivariant (unitsSubgroup N))
    (hc : IsFaceCartesian (⟨f, hat.equivariant⟩ : EquivariantHom aU aX) (isFace_units N))
    {W : BigFppfOver B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (rW : RepresentsAttractor aU N (yoneda.obj W)) (r : RepresentsAttractor aX N P) :
    IsPullback (limitToX rW) (chartToAttr ⟨f, hat.equivariant⟩ rW r) f (limitToX r) := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  let F : EquivariantHom aU aX := ⟨f, hat.equivariant⟩
  let Z := unitsSubgroup N
  have hQ : IsFace Z.toAddSubmonoid N := isFace_units N
  have hcov : ∀ {W : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op W)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS W :=
    fun a => extSieve_mem Z a
  let e := fun T => attractorFixedEquivOfCover (act := aU)
    (BigFppfOver.isSheaf_of_type_yoneda_obj U) hcov T
  have hUinj : ∀ T (φ ψ : AttractorPt aU Z.toAddSubmonoid T), φ.toPoint = ψ.toPoint → φ = ψ := by
    intro T φ ψ h
    exact (e T).symm.injective (Subtype.ext h)
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · refine ConcreteCategory.hom_ext _ _ fun v => ?_
    change f.app T (AttractorPt.ofFace hQ (rW.equiv (unop T) v)).toPoint =
      (AttractorPt.ofFace hQ (r.equiv (unop T) ((chartToAttr F rW r).app (op (unop T)) v))).toPoint
    rw [chartToAttr_equiv, ← AttractorPt.push_ofFace]
    rfl
  · rintro v v' ⟨e1, e2⟩
    apply (rW.equiv (unop T)).injective
    apply (hc (unop T)).1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · have := congrArg (r.equiv (unop T)) e2
      exact (chartToAttr_equiv F rW r (unop T) v).symm.trans
        (this.trans (chartToAttr_equiv F rW r (unop T) v'))
    · exact hUinj _ _ _ e1
  · intro u p hup
    have hup' : f.app T u = (AttractorPt.ofFace hQ (r.equiv (unop T) p)).toPoint := hup
    have hfix : u ∈ (fixedPoints (quotientAction aU Z)).obj T := by
      refine (isFPR_iff (IsEquivariant.comap (actU := aU) (actX := aX) (f := f) hat.equivariant
        (QuotientAddGroup.mk' Z))).mp hZ T u ?_
      rw [hup']
      exact AttractorPt.toPoint_mem_fixedPoints _
    have hwZ : (e (unop T) ⟨u, hfix⟩).toPoint = u :=
      congrArg Subtype.val ((e (unop T)).symm_apply_apply ⟨u, hfix⟩)
    have hpush : AttractorPt.ofFace hQ (r.equiv (unop T) p) =
        AttractorPt.push F (e (unop T) ⟨u, hfix⟩) := by
      apply attractor_toPoint_injective_sep hX hsep
      refine hup'.symm.trans ?_
      exact (congrArg (f.app T) hwZ).symm
    obtain ⟨w, hw⟩ := (hc (unop T)).2 ⟨(r.equiv (unop T) p, e (unop T) ⟨u, hfix⟩), hpush⟩
    refine ⟨(rW.equiv (unop T)).symm w, ?_, ?_⟩
    · change (AttractorPt.ofFace hQ (rW.equiv (unop T) ((rW.equiv (unop T)).symm w))).toPoint = u
      rw [Equiv.apply_symm_apply]
      have h2 : AttractorPt.ofFace hQ w = e (unop T) ⟨u, hfix⟩ := congrArg (fun q => q.1.2) hw
      rw [h2]
      exact hwZ
    · apply (r.equiv (unop T)).injective
      refine (chartToAttr_equiv F rW r (unop T) _).trans ?_
      rw [Equiv.apply_symm_apply]
      exact congrArg (fun q => q.1.1) hw

/-- **Corollary 11.6** for an equivariant atlas, and the surjectivity in the proof of **Proposition
15.5**: `U^N → X^N` is étale and surjective. -/
theorem chartToAttr_etale_surjective {f : yoneda.obj U ⟶ X} (hat : IsEquivariantAtlas aU aX f)
    {N : AddSubmonoid M} (hZ : IsZFPR hat.equivariant (unitsSubgroup N))
    (hc : IsFaceCartesian (⟨f, hat.equivariant⟩ : EquivariantHom aU aX) (isFace_units N))
    {W : BigFppfOver B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (rW : RepresentsAttractor aU N (yoneda.obj W)) (r : RepresentsAttractor aX N P) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (Sch))) (chartToAttr ⟨f, hat.equivariant⟩ rW r) ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (Sch)))
      (chartToAttr ⟨f, hat.equivariant⟩ rW r) := by
  have h := chartToAttr_isPullback hat hZ hc hX hsep rW r
  exact ⟨(MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h hat.etale,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h hat.surjective⟩

/-- The morphism `q : X^N → X^L` of the proof of **Proposition 15.5**, for `N ≤ L`. -/
noncomputable def attrLE {N L : AddSubmonoid M} (h : N ≤ L) {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (rP : RepresentsAttractor aX N P) (rQ : RepresentsAttractor aX L Q) : P ⟶ Q where
  app T := ↾ fun p => (rQ.equiv (unop T)).symm (AttractorPt.ofLE h (rP.equiv (unop T) p))
  naturality T T' s := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    apply (rQ.equiv (unop T')).injective
    change rQ.equiv _ ((rQ.equiv _).symm (AttractorPt.ofLE h (rP.equiv (unop T')
        (P.map s.unop.op p)))) =
      rQ.equiv (unop T') (Q.map s.unop.op ((rQ.equiv (unop T)).symm
        (AttractorPt.ofLE h (rP.equiv (unop T) p))))
    rw [Equiv.apply_symm_apply, rQ.naturality, Equiv.apply_symm_apply, rP.naturality]
    rfl

/-- The heart of the printed proof of **Proposition 15.5**. `N ≤ L` and `U^L ⊆ U^N`. The morphism
`U^L → X^L` is an étale surjection (Corollary 11.6, Proposition 5.1) factoring through the monomorphism
`q : X^N → X^L` (Proposition 3.29), hence `q` is an isomorphism. -/
theorem isIso_attrLE {f : yoneda.obj U ⟶ X} (hat : IsStronglyFPRAtlas aU aX f)
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X)
    {N L : AddSubmonoid M} (h : N ≤ L) (hU : attractorImage aU L ≤ attractorImage aU N)
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (rP : RepresentsAttractor aX N P)
    (rQ : RepresentsAttractor aX L Q) (hP : IsAlgebraicSpace B S hS P)
    (hQ : IsAlgebraicSpace B S hS Q) : IsIso (attrLE h rP rQ) := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  obtain ⟨A, V, hV⟩ := hat.atlas.decomposition
  obtain ⟨rW⟩ := exists_chartAttr hV L
  let F : EquivariantHom aU aX := ⟨f, hat.atlas.equivariant⟩
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hc : IsFaceCartesian F (isFace_units L) := by
    refine isFaceCartesian_of_pieces hsh hV F _ fun b => ?_
    have hA : IsAffineHom (openObj (V b)).hom.hom := hV.isAffineHom b
    exact isFaceCartesian_of_separated hX hsep hlim _ (isEtale_piece_comp hat.atlas.etale) _
  obtain ⟨hE, hS'⟩ := chartToAttr_etale_surjective hat.atlas (hat.isStronglyFPR _) hc hX hsep rW.r rQ
  let J := BigFppfOver.topology B S hS
  have hmono : Mono (attrLE h rP rQ) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun p p' e => ?_
    apply (rP.equiv (unop T)).injective
    refine attractor_toPoint_injective_sep hX hsep N (unop T) ?_
    have e' := congrArg (rQ.equiv (unop T)) e
    have e'' : AttractorPt.ofLE h (rP.equiv (unop T) p) = AttractorPt.ofLE h (rP.equiv (unop T) p') :=
      (Equiv.apply_symm_apply _ _).symm.trans (e'.trans (Equiv.apply_symm_apply _ _))
    have e3 := congrArg AttractorPt.toPoint e''
    rwa [AttractorPt.toPoint_ofLE, AttractorPt.toPoint_ofLE] at e3
  have hloc : Presheaf.IsLocallySurjective J (attrLE h rP rQ) := by
    refine ⟨fun {T} x => ?_⟩
    let g₀ : yoneda.obj T ⟶ Q := yonedaEquiv.symm x
    let rep := hE.rep
    let T' := rep.pullback g₀
    let q : T' ⟶ T := rep.snd g₀
    let u : T' ⟶ rW.W := rep.fst' g₀
    have hu : (chartToAttr F rW.r rQ).app (op T') u = Q.map q.op x := by
      have h2 : yoneda.map u ≫ chartToAttr F rW.r rQ = yoneda.map q ≫ g₀ := by
        rw [Functor.relativelyRepresentable.map_fst']
        exact rep.w g₀
      have h3 := congrArg (fun k => k.app (op T') (𝟙 T')) h2
      have h4 : (yoneda.map u ≫ chartToAttr F rW.r rQ).app (op T') (𝟙 T') =
          (chartToAttr F rW.r rQ).app (op T') u := by
        change (chartToAttr F rW.r rQ).app (op T') (𝟙 T' ≫ u) = _
        rw [Category.id_comp]
      have h5 : (yoneda.map q ≫ g₀).app (op T') (𝟙 T') = Q.map q.op x := by
        change g₀.app (op T') (𝟙 T' ≫ q) = _
        rw [Category.id_comp]
        simp [g₀, yonedaEquiv_symm_app_apply]
      exact h4.symm.trans (h3.trans h5)
    have hcov := Space.sieve_generate_singleton_mem_topology_over B S hS q
      (hS'.property_snd g₀) (hE.property_snd g₀)
    refine J.superset_covering ?_ hcov
    rintro Y g ⟨W', a, b, ⟨⟩, rfl⟩
    obtain ⟨φ, hφ⟩ := hU T' ⟨rW.r.equiv T' u, rfl⟩
    have hp0 : (attrLE h rP rQ).app (op T') ((rP.equiv T').symm (AttractorPt.push F φ)) =
        Q.map q.op x := by
      rw [← hu]
      apply (rQ.equiv T').injective
      refine (Equiv.apply_symm_apply _ _).trans ?_
      refine Eq.trans ?_ (chartToAttr_equiv F rW.r rQ T' u).symm
      rw [Equiv.apply_symm_apply]
      apply attractor_toPoint_injective_sep hX hsep
      rw [AttractorPt.toPoint_ofLE]
      exact congrArg (f.app (op T')) hφ
    refine ⟨P.map a.op ((rP.equiv T').symm (AttractorPt.push F φ)), ?_⟩
    rw [NatTrans.naturality_apply, hp0, ← Functor.map_comp_apply]
    rfl
  let g : (⟨P, hP.isSheaf⟩ : Sheaf J (Type u)) ⟶ ⟨Q, hQ.isSheaf⟩ :=
    ObjectProperty.homMk (attrLE h rP rQ)
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).1
    ⟨Presheaf.isLocallyInjective_of_injective J _
      fun T ↦ (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).1 hmono T), hloc⟩
  exact (sheafToPresheaf J (Type u)).map_isIso g

/-- The inclusion `X^L ⊆ X^N` from the isomorphism `q`, through the representing spaces of Theorem 8.3. -/
theorem attractorImage_le_printed {f : yoneda.obj U ⟶ X} (hat : IsStronglyFPRAtlas aU aX f)
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X)
    {N L : AddSubmonoid M} (h : N ≤ L) (hU : attractorImage aU L ≤ attractorImage aU N) :
    attractorImage aX L ≤ attractorImage aX N := by
  have : AddGroup.FG M := AddGroup.fg_iff_addMonoid_fg.mpr inferInstance
  obtain ⟨rN⟩ := thm83_repr hX hsep N ⟨U, aU, f, hat.isZFPRAtlas _⟩ (Or.inr hlim)
  obtain ⟨rL⟩ := thm83_repr hX hsep L ⟨U, aU, f, hat.isZFPRAtlas _⟩ (Or.inr hlim)
  have hi := isIso_attrLE hat hX hsep hlim h hU rN.rP rL.rP rN.algP rL.algP
  rintro T _ ⟨x, rfl⟩
  have hb := (isIso_iff_bijective _).1 ((NatTrans.isIso_iff_isIso_app _).1 hi (op T))
  obtain ⟨p, hp⟩ := hb.2 ((rL.rP.equiv T).symm x)
  refine ⟨rN.rP.equiv T p, ?_⟩
  have e := congrArg (rL.rP.equiv T) hp
  have e' : AttractorPt.ofLE h (rN.rP.equiv T p) = x :=
    (Equiv.apply_symm_apply _ _).symm.trans (e.trans (Equiv.apply_symm_apply _ _))
  rw [← e', AttractorPt.toPoint_ofLE]

/-- **Proposition 15.5**, printed route: `U → X` an `S`-affine strongly-FPR atlas of the separated
algebraic space `X`, limit preserving. Then `U^N = U^L` implies `X^N = X^L`. By Proposition 3.32 on `U`
one reduces to `N ≤ L`. -/
theorem prop155_printed [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) {N L : AddSubmonoid M}
    (hU : attractorImage aU N = attractorImage aU L) :
    attractorImage aX N = attractorImage aX L := by
  have hord := attractorOrder_of_isAffineHom aU
  have hinf : attractorImage aU (N ⊓ L) = attractorImage aU N := by
    rw [← sInf_pair]
    refine hord.sInf_of_const _ _ ⟨N, by simp⟩ ?_
    rintro K (rfl | rfl)
    · rfl
    · exact hU.symm
  have h1 := attractorImage_le_printed hat hX hsep hlim (inf_le_left : N ⊓ L ≤ N) hinf.ge
  have h2 := attractorImage_le_printed hat hX hsep hlim (inf_le_right : N ⊓ L ≤ L)
    (by rw [hinf, hU])
  exact le_antisymm (h1.trans (attractorImage_monotone aX inf_le_right))
    (h2.trans (attractorImage_monotone aX inf_le_left))

/-- **Proposition 15.5**, last assertion, printed route: `Π(a_X) ⊆ Π(a_U)`. -/
theorem prop155_printed_pure [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X) :
    pureMagnets (attractorImage aX) ⊆ pureMagnets (attractorImage aU) :=
  pureMagnets_subset_of_reflects fun _ _ h => prop155_printed hat hX hsep hlim h

/-- **Theorem 15.3** for `X` locally of finite presentation over `S` with an `S`-affine strongly-FPR
atlas: no added hypothesis, any `S`. -/
noncomputable def thm153_lfp [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) :
    pureMagnets (attractorImage aX) ≃ Set.range (attractorImage aX) :=
  have : LocallyOfFiniteType U.hom.hom := chartsOfFiniteType_of_lfp hfp U f hat.atlas.etale
  thm153_strong hX hsep (isLimitPreserving_of_lfp hX hfp) hat.atlas
    fun _ _ _ _ => hat.isStronglyFPR _

/-- **Theorem 15.4 (ii)** and **Remark 15.6**: `S` quasi-compact, `X` separated, locally of finite
presentation over `S`, with an `S`-affine strongly-FPR atlas. -/
theorem thm154_ii_lfp [CompactSpace S] [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite :=
  thm154_ii hX hsep (isLimitPreserving_of_lfp hX hfp) (chartsOfFiniteType_of_lfp hfp) hat

/-- **Remark 15.6**, as printed, with the hypotheses of `thm154_ii_lfp`. -/
theorem rem156_lfp [CompactSpace S] [IsAffineHom U.hom.hom] {f : yoneda.obj U ⟶ X}
    (hat : IsStronglyFPRAtlas aU aX f) (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) :
    (Set.range fun Z : AddSubgroup M => attractorImage aX Z.toAddSubmonoid).Finite :=
  rem156 hX hsep (isLimitPreserving_of_lfp hX hfp) (chartsOfFiniteType_of_lfp hfp) hat

/-- **Theorem 15.4 (ii)**, the case "the action is Zariski locally linearizable", for a finite cover,
through **Fact 7.3**: the disjoint union of the finitely many stable `S`-affine opens is an `S`-affine
strongly-FPR atlas. -/
theorem thm154_ii_of_linearizable [CompactSpace S] {A : Type u} [Finite A]
    {W : A → BigFppfOver B S hS} {V : BigFppfOver B S hS} {j : ∀ a, W a ⟶ V}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (Ln : ZariskiLocallyLinearizable aX A W) (hV : IsColimit (Cofan.mk V j)) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite := by
  obtain ⟨actV, v, h⟩ := fact73 hX Ln hV
  have hV' : IsAffineHom (structMap V) :=
    (hasFiniteAffineDecomposition_iff (coprodAction Ln.act hV)).1
      ⟨A, inferInstance, _, coprod_decomposition Ln.act hV Ln.isAffineHom⟩
  have : IsAffineHom V.hom.hom := hV'
  exact thm154_ii_lfp h hX hsep hfp

/-- A quasi-compact `X` needs only finitely many members of a Sumihiro cover. -/
theorem exists_finite_linearizable {A : Type u} {W : A → BigFppfOver B S hS}
    (hq : Space.IsQuasiCompactSpace B S hS X) (Ln : ZariskiLocallyLinearizable aX A W) :
    ∃ F : Finset A, Nonempty (ZariskiLocallyLinearizable aX F fun a => W a.1) := by
  obtain ⟨a₀, φ, hc, hs, -⟩ := hq
  have hcover : ∀ y : (Sch).obj a₀, ∃ a, y ∈ Set.range ((Sch).map ((Ln.isOpen a).rep.snd φ)) :=
    fun y => Ln.covers a₀ φ y
  have hoi : ∀ a, IsOpenImmersion ((Sch).map ((Ln.isOpen a).rep.snd φ)) :=
    fun a => (Ln.isOpen a).property_snd φ
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun a => Set.range ((Sch).map ((Ln.isOpen a).rep.snd φ)))
    (fun a => ((Sch).map ((Ln.isOpen a).rep.snd φ)).isOpenEmbedding.isOpen_range)
    (fun y _ => Set.mem_iUnion.mpr (hcover y))
  refine ⟨F, ⟨⟨fun a => Ln.act a.1, fun a => Ln.j a.1, fun a => Ln.equivariant a.1,
    fun a => Ln.isOpen a.1, fun a => Ln.isAffineHom a.1, ?_⟩⟩⟩
  intro T x t
  -- pull the surjection `a₀ → X` back to `T`
  let g₀ := x
  let rep := hs.rep
  let P := rep.pullback g₀
  let q : P ⟶ T := rep.snd g₀
  let u : P ⟶ a₀ := rep.fst' g₀
  have hsq : yoneda.map u ≫ φ = yoneda.map q ≫ x := by
    rw [Functor.relativelyRepresentable.map_fst']
    exact rep.w g₀
  have hq' : Surjective ((Sch).map q) := hs.property_snd g₀
  obtain ⟨p, hp⟩ := hq'.surj t
  obtain ⟨b, hbF, hb⟩ : ∃ b ∈ F, (Sch).map u p ∈
      Set.range ((Sch).map ((Ln.isOpen b).rep.snd φ)) := by
    have := hF (Set.mem_univ ((Sch).map u p))
    simpa using this
  refine ⟨⟨b, hbF⟩, ?_⟩
  have := hoi b
  obtain ⟨Y, i, hi, hr, -⟩ := exists_restrict_bigFppfOver P
    ((Sch).map u ⁻¹ᵁ ((Sch).map ((Ln.isOpen b).rep.snd φ)).opensRange)
  obtain ⟨c, hc'⟩ := exists_factor_open ((Ln.isOpen b).rep.snd φ) (i ≫ u) (by
    rintro _ ⟨z, rfl⟩
    have hz : (Sch).map i z ∈ Set.range ((Sch).map i) := ⟨z, rfl⟩
    rw [hr] at hz
    rw [(Sch).map_comp, Scheme.Hom.comp_apply]
    exact hz)
  have hw : yoneda.map (c ≫ (Ln.isOpen b).rep.fst' φ) ≫ Ln.j b = yoneda.map (i ≫ q) ≫ x := by
    rw [yoneda.map_comp, Category.assoc, Functor.relativelyRepresentable.map_fst',
      (Ln.isOpen b).rep.w φ, ← Category.assoc, ← yoneda.map_comp, hc', yoneda.map_comp, Category.assoc,
      hsq, yoneda.map_comp, Category.assoc]
  let m := (Ln.isOpen b).rep.lift' (c ≫ (Ln.isOpen b).rep.fst' φ) (i ≫ q) hw
  have hm : m ≫ (Ln.isOpen b).rep.snd x = i ≫ q := (Ln.isOpen b).rep.lift'_snd _ _ _
  have hpr : p ∈ Set.range ((Sch).map i) := by
    rw [hr]
    exact hb
  obtain ⟨z, rfl⟩ := hpr
  refine ⟨(Sch).map m z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← (Sch).map_comp, hm, (Sch).map_comp, Scheme.Hom.comp_apply]
  exact hp

/-- **Theorem 15.4 (ii)** for a Zariski locally linearizable action, `S` quasi-compact, `X` separated,
quasi-compact and locally of finite presentation over `S`, as "finitely presented" says. Finite
coproducts in the site replace the paper's category without size cutoff. -/
theorem thm154_ii_of_linearizable_qc [CompactSpace S] [HasFiniteCoproducts (BigFppfOver B S hS)]
    {A : Type u} {W : A → BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (Ln : ZariskiLocallyLinearizable aX A W) :
    (pureMagnets (attractorImage aX)).Finite ∧ (Set.range (attractorImage aX)).Finite := by
  obtain ⟨F, ⟨L'⟩⟩ := exists_finite_linearizable hq Ln
  let U' : F → BigFppfOver B S hS := fun a => W a.1
  have hV : IsColimit (Cofan.mk (∐ U') (Sigma.ι U')) :=
    (coproductIsCoproduct U').ofIsoColimit (Cocone.ext (Iso.refl _) (by
      rintro ⟨a⟩; simp))
  exact thm154_ii_of_linearizable hX hsep hfp L' hV

end Printed

section Examples

open Magnetism

variable {M : Type*} [AddCommMonoid M] [DecidableEq M] [IsCancelAdd M] (R : Type*) [CommRing R]
  [Nontrivial R]

/-- `𝔸(⟨e⟩)` with its action, `⟨e⟩` nonzero sharp: `Π(a) = {0, ⟨e⟩}`. -/
theorem pureMagnets_single (e : M) (he : e ≠ 0)
    (hb : ∀ x ∈ AddSubmonoid.closure ({e} : Set M), ∀ y ∈ AddSubmonoid.closure ({e} : Set M),
      x + y = 0 → x = 0) :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure ({e} : Set M)) R)) =
      {⊥, AddSubmonoid.closure {e}} := by
  rw [pureMagnets_self_eq R _ ?_ hb]
  · ext N
    constructor
    · rintro ⟨E', hE', rfl⟩
      rcases Set.subset_singleton_iff_eq.1 hE' with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨∅, by simp, AddSubmonoid.closure_empty⟩
      · exact ⟨_, Set.mem_powerset (Set.Subset.refl _), rfl⟩
  · intro E' hE' heq
    have h0 : E' = ∅ := by
      rcases Set.subset_singleton_iff_eq.1 hE'.1 with h | h
      · exact h
      · exact absurd h hE'.ne
    rw [h0, AddSubmonoid.closure_empty] at heq
    have : e ∈ (⊥ : AddSubmonoid M) := heq ▸ AddSubmonoid.subset_closure rfl
    exact he (by simpa using this)

/-- **Example (i) after Fact 15.11.** `𝔸(ℕ)` acting on itself: `Π(a) = {0, ℕ}`. -/
theorem pureMagnets_nat_self :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure ({1} : Set ℕ)) R)) =
      {⊥, AddSubmonoid.closure {1}} :=
  pureMagnets_single R 1 one_ne_zero fun x _ y _ h => by omega

lemma int_nonneg_of_mem {d : ℤ} (hd : 0 ≤ d) {x : ℤ} (hx : x ∈ AddSubmonoid.closure ({d} : Set ℤ)) :
    0 ≤ x := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hd
  | zero => exact le_rfl
  | add x y _ _ hx hy => exact add_nonneg hx hy

/-- **Example (ii) after Fact 15.11.** `D(ℤ)` acting on `𝔸(ℕ)` by multiplication: `Π(a) = {0, ℕ}`. -/
theorem pureMagnets_int_one :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure ({1} : Set ℤ)) R)) =
      {⊥, AddSubmonoid.closure {1}} :=
  pureMagnets_single R 1 one_ne_zero fun x hx y hy h => by
    have := int_nonneg_of_mem (by norm_num) hx
    have := int_nonneg_of_mem (by norm_num) hy
    omega

/-- **Example (iii) after Fact 15.11.** `D(ℤ)` acting on `𝔸(ℕ)` by `t · x = t² x`, which is `𝔸(2ℕ)` with
the inclusion `2ℕ ⊆ ℤ`: `Π(a) = {0, 2ℕ}`. -/
theorem pureMagnets_int_two :
    pureMagnets (affineY (magnetGrading (AddSubmonoid.closure ({2} : Set ℤ)) R)) =
      {⊥, AddSubmonoid.closure {2}} :=
  pureMagnets_single R 2 two_ne_zero fun x hx y hy h => by
    have := int_nonneg_of_mem (by norm_num) hx
    have := int_nonneg_of_mem (by norm_num) hy
    omega

/-- **Example (v) after Fact 15.11.** `D(ℤ²)` acting on `𝔸(ℕ²)` by multiplication:
`Π(a) = {0, ℕ × 0, 0 × ℕ, ℕ²}`. -/
theorem pureMagnets_int_prod :
    pureMagnets (affineY (magnetGrading
      (AddSubmonoid.closure ({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ))) R)) =
      {⊥, AddSubmonoid.closure {((1 : ℤ), (0 : ℤ))}, AddSubmonoid.closure {((0 : ℤ), (1 : ℤ))},
        AddSubmonoid.closure ({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ))} := by
  have hnn : ∀ x ∈ AddSubmonoid.closure ({((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)),
      0 ≤ x.1 ∧ 0 ≤ x.2 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> norm_num
    | zero => exact ⟨le_rfl, le_rfl⟩
    | add x y _ _ hx hy => exact ⟨add_nonneg hx.1 hy.1, add_nonneg hx.2 hy.2⟩
  have h1 : ∀ x ∈ AddSubmonoid.closure ({((0 : ℤ), (1 : ℤ))} : Set (ℤ × ℤ)), x.1 = 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
  have h2 : ∀ x ∈ AddSubmonoid.closure ({((1 : ℤ), (0 : ℤ))} : Set (ℤ × ℤ)), x.2 = 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => rw [Set.mem_singleton_iff.mp hx]
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
  rw [pureMagnets_self_eq R _ ?_ ?_]
  · ext N
    constructor
    · rintro ⟨E', hE', rfl⟩
      rw [Set.mem_powerset_iff, Set.subset_pair_iff_eq] at hE'
      rcases hE' with rfl | rfl | rfl | rfl <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨∅, by simp, AddSubmonoid.closure_empty⟩
      · exact ⟨{_}, by simp, rfl⟩
      · exact ⟨{_}, by simp, rfl⟩
      · exact ⟨_, Set.mem_powerset (Set.Subset.refl _), rfl⟩
  · intro E' hE' heq
    obtain ⟨e, he, heE'⟩ := Set.exists_of_ssubset hE'
    rcases he with rfl | he
    · have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {((0 : ℤ), (1 : ℤ))} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with h | h
          · exact absurd (h ▸ hx) heE'
          · exact h
      have := h1 _ (hle (heq ▸ AddSubmonoid.subset_closure (Or.inl rfl) :
        (((1 : ℤ), (0 : ℤ))) ∈ AddSubmonoid.closure E'))
      simp at this
    · rw [Set.mem_singleton_iff.mp he] at heE'
      have hle : AddSubmonoid.closure E' ≤ AddSubmonoid.closure {((1 : ℤ), (0 : ℤ))} :=
        AddSubmonoid.closure_mono fun x hx => by
          rcases hE'.1 hx with h | h
          · exact h
          · rw [Set.mem_singleton_iff.mp h] at hx
            exact absurd hx heE'
      have := h2 _ (hle (heq ▸ AddSubmonoid.subset_closure (Or.inr rfl) :
        (((0 : ℤ), (1 : ℤ))) ∈ AddSubmonoid.closure E'))
      simp at this
  · intro x hx y hy h
    have a := hnn x hx
    have b := hnn y hy
    have c1 := congrArg Prod.fst h
    have c2 := congrArg Prod.snd h
    simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at c1 c2
    exact Prod.ext (by simp; omega) (by simp; omega)

end Examples

end AlgMag

#print axioms AlgMag.chartsOfFiniteType_of_lfp
#print axioms AlgMag.fact334_strong
#print axioms AlgMag.attractorOrder_strong
#print axioms AlgMag.thm153_strong
#print axioms AlgMag.chartToAttr_isPullback
#print axioms AlgMag.chartToAttr_etale_surjective
#print axioms AlgMag.isIso_attrLE
#print axioms AlgMag.prop155_printed
#print axioms AlgMag.prop155_printed_pure
#print axioms AlgMag.thm153_lfp
#print axioms AlgMag.thm154_ii_lfp
#print axioms AlgMag.rem156_lfp
#print axioms AlgMag.thm154_ii_of_linearizable
#print axioms AlgMag.exists_finite_linearizable
#print axioms AlgMag.thm154_ii_of_linearizable_qc
#print axioms AlgMag.pureMagnets_nat_self
#print axioms AlgMag.pureMagnets_int_one
#print axioms AlgMag.pureMagnets_int_two
#print axioms AlgMag.pureMagnets_int_prod
