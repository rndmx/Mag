/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCAttRes
import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProduct
import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionCoproduct
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso

/-!
# `X^K` is an algebraic space, `S` arbitrary

Over each member of an affine open cover of `S` this is Theorem 8.3 on the site of that member. The members are glued by Stacks 04SK in
the form `isAlgebraicSpace_of_isCovering_of_atlas_size_le`, the atlases being bounded by `exists_small_atlas`: `X^K ⟶ X` is a monomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddGroup.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- For `X` a separated algebraic space, the map from the attractor `X^K` to `X` is a monomorphism. -/
theorem mono_attToX (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (act : AAction (fppfO B S hS) M X) (K : AddSubmonoid M) : Mono (attToX act K) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun p p' h => ?_
  refine ((attPRep act K).equiv (unop T)).injective ?_
  exact attractor_toPoint_injective_sep (aX := act) hX (isSeparatedOver_iff_space.1 hsep) K (unop T) h

/-- A morphism of the site that is a monomorphism to the final object: maps to it are unique. -/
lemma hom_to_yoneda_ext {T : BigFppfOver B S hS} (hm : Mono (Over.mkIdTerminal.from T : T ⟶ T1 B S hS))
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : Z ⟶ yoneda.obj T) : a = b := by
  ext U z
  exact (cancel_mono (Over.mkIdTerminal.from T : T ⟶ T1 B S hS)).1 (t1_ext _ _)

variable (hZ : B.Contains (⊤_ Scheme.{u}))

include hZ in
/-- Over an object whose scheme is separated and whose map to `S` is an open immersion: a bounded atlas and algebraicity. -/
theorem attP_local (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (K : AddSubmonoid M)
    {T₀' : Scheme.{u}} {hT : B.Contains T₀'} (a : B.obj hT ⟶ B.obj hS) [T₀'.IsSeparated]
    (ha : IsOpenImmersion (B.inclusion.map a)) :
    IsAlgebraicSpace B T₀' hT ((relocalizeRestrict a).obj (attP act K)) ∧
      Space.IsLocallyOfFinitePresentation B S hS (toT1 (yoneda.obj (Over.mk a) ⨯ attP act K)) := by
  let T₀ : BigFppfOver B S hS := Over.mk a
  haveI : T₀.left.1.IsSeparated := inferInstanceAs T₀'.IsSeparated
  have hR := res_alg T₀ hX
  have hfp' := (lfp_toT1_iff hR).1 (res_lfp T₀ hX ((lfp_toT1_iff hX).2 hfp))
  obtain ⟨r, -, -, -, hrfp⟩ := thm83_nonqc hZ hM hR (res_sep T₀ hX hsep) hfp' (resAct (T₀ := T₀) act) K
  have hI : InjData act T₀ := injData hX hsep
  let e := attResIso hI r.rP
  have hRa : IsAlgebraicSpace B T₀' hT ((relocalizeRestrict a).obj (attP act K)) :=
    Space.isAlgebraicSpace_of_iso B T₀' hT e.symm r.algP
  let rep' : RepresentsAttractor (resAct (T₀ := T₀) act) K ((relocalizeRestrict a).obj (attP act K)) :=
    { equiv := fun W => (attResEquiv hI r.rP W).trans (r.rP.equiv W)
      naturality := fun {W W'} s z => by
        have hn := congrArg (fun k => k z) (e.hom.naturality s.op)
        change r.rP.equiv W' (e.hom.app (op W') _) = (r.rP.equiv W (e.hom.app (op W) z)).baseChange s
        rw [← r.rP.naturality]
        exact congrArg _ hn }
  have hlp := limitPreserving_of_represents
    ((Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B T₀' hT hR).1 hfp') rep'
  have hRfp := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B T₀' hT hRa).2 hlp
  have htoT1 := (lfp_toT1_iff hRa).2 hRfp
  have e2 : toT1 ((relocalizeRestrict a).obj (attP act K)) =
      Space.toYonedaId B T₀' hT ((relocalizeRestrict a).obj (attP act K)) := toT1_ext _ _
  have h1 : Space.IsLocallyOfFinitePresentation B S hS (relocalizeToYoneda a _) :=
    (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B T₀' S hT hS a _ _).2 (e2 ▸ htoT1)
  have hL := isAlgebraicSpace_viewOver B T₀' S hT hS a _ hRa
  have hy := isAlgebraicSpace_yoneda B S hS
  have e3 : toT1 ((relocalizePresheafFunctor a).obj ((relocalizeRestrict a).obj (attP act K))) =
      relocalizeToYoneda a _ ≫ yoneda.map (Over.mkIdTerminal.from (Over.mk a)) := toT1_ext _ _
  have hoT : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from (Over.mk a) : (Over.mk a : BigFppfOver B S hS) ⟶ T1 B S hS)) := by
    have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
        (Over.mkIdTerminal.from (Over.mk a) : (Over.mk a : BigFppfOver B S hS) ⟶ T1 B S hS)) := by
      rw [show (BigFppfOver.toScheme B S hS).map
          (Over.mkIdTerminal.from (Over.mk a) : (Over.mk a : BigFppfOver B S hS) ⟶ T1 B S hS) = B.inclusion.map a from
        congrArg B.inclusion.map (Over.mkIdTerminal_from_left (Over.mk a : BigFppfOver B S hS))]
      exact ha
    infer_instance
  have h2 : Space.IsLocallyOfFinitePresentation B S hS
      (toT1 ((relocalizePresheafFunctor a).obj ((relocalizeRestrict a).obj (attP act K)))) := by
    rw [e3]
    exact Space.isLocallyOfFinitePresentation_comp B S hS hL (hy _) (hy _) _ _ h1
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS _ hoT)
  refine ⟨hRa, ?_⟩
  have hri := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B S hS (@LocallyOfFinitePresentation)
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (relocalizeRestrictIsoProduct a (attP act K))
    (Iso.refl _) (toT1_ext _ _))).1 h2

/-- The bounded atlas over an affine open of a member. -/
theorem attP_member_atlas (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (act : AAction (fppfO B S hS) M X) (K : AddSubmonoid M)
    {E₀ W WX : BigFppfOver B S hS} (hEo : IsOpenImmersion ((SCH).map (Over.mkIdTerminal.from E₀ : E₀ ⟶ T1 B S hS)))
    (hfi : IsAlgebraicSpace B S hS (yoneda.obj E₀ ⨯ attP act K))
    (hlfp : Space.IsLocallyOfFinitePresentation B S hS (toT1 (yoneda.obj E₀ ⨯ attP act K)))
    (j : W ⟶ E₀) (hjo : IsOpenImmersion ((SCH).map j)) {w : yoneda.obj WX ⟶ X}
    (hws : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) w)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hμS : S.size ≤ μ)
    (hμW : 2 ^ ((SCH).obj WX).size ≤ μ) :
    ∃ (Y : BigFppfOver B S hS)
      (b : yoneda.obj Y ⟶ pullback (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ yoneda.obj E₀) (yoneda.map j)),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) b ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) b ∧ ((SCH).obj Y).size ≤ μ := by
  have hy := isAlgebraicSpace_yoneda B S hS
  have hQ := isAlgebraicSpace_pullback B S hS (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _)
    (yoneda.map j) hfi (hy _) (hy _)
  have hmo : ∀ {T : BigFppfOver B S hS}, IsOpenImmersion ((SCH).map (Over.mkIdTerminal.from T : T ⟶ T1 B S hS)) →
      Mono (Over.mkIdTerminal.from T : T ⟶ T1 B S hS) := fun h =>
    have := h
    (SCH).mono_of_mono_map (IsOpenImmersion.mono _)
  have hWo : IsOpenImmersion ((SCH).map (Over.mkIdTerminal.from W : W ⟶ T1 B S hS)) := by
    rw [show (Over.mkIdTerminal.from W : W ⟶ T1 B S hS) = j ≫ Over.mkIdTerminal.from E₀ from
      t1_ext _ _, (SCH).map_comp]
    infer_instance
  have hEm := hmo hEo
  have hWm := hmo hWo
  haveI hmX := mono_attToX hX hsep act K
  haveI hm : Mono (pullback.fst (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j) ≫
      prod.snd ≫ attToX act K) := by
    refine ⟨fun {Z} a b hab => ?_⟩
    refine pullback.hom_ext (prod.hom_ext (hom_to_yoneda_ext hEm _ _) ?_) (hom_to_yoneda_ext hWm _ _)
    simp only [Category.assoc] at hab ⊢
    exact (cancel_mono (attToX act K)).1 hab
  have hopen : Space.IsLocallyOfFinitePresentation B S hS
      (pullback.fst (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j)) := by
    have hsq : IsPullback
        (ObjectProperty.homMk (pullback.snd (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j)) :
          (⟨_, hQ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy W⟩)
        (ObjectProperty.homMk (pullback.fst (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j)) :
          (⟨_, hQ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hfi⟩)
        (ObjectProperty.homMk (yoneda.map j) : (⟨_, hy W⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy E₀⟩)
        (ObjectProperty.homMk prod.fst : (⟨_, hfi⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hy E₀⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F))
        (IsPullback.of_hasPullback (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j)).flip
    exact (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq
      (Space.isLocallyOfFinitePresentation_yoneda_map B S hS j inferInstance)
  have hlf : Space.IsLocallyOfFinitePresentation B S hS
      (toT1 (pullback (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j))) := by
    rw [show toT1 (pullback (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j)) =
      pullback.fst _ _ ≫ toT1 _ from toT1_ext _ _]
    exact Space.isLocallyOfFinitePresentation_comp B S hS hQ hfi (hy _) _ _
      hopen hlfp
  exact exists_small_atlas hQ (chartsOfFiniteType_of_lfp ((lfp_toT1_iff hQ).1 hlf))
    (pullback.fst (prod.fst : yoneda.obj E₀ ⨯ attP act K ⟶ _) (yoneda.map j) ≫ prod.snd ≫ attToX act K) hws hℵ hμ hμS hμW

include hZ in
/-- `X^K` is an algebraic space, `X` separated, locally of finite presentation, `S` arbitrary, no atlas. -/
theorem attP_alg (hM : B.Contains (Spec (ZMon M))) (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (act : AAction (fppfO B S hS) M X) (K : AddSubmonoid M) :
    IsAlgebraicSpace B S hS (attP act K) := by
  classical
  have hsX := (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hsF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (attP act K) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_attP act K hsX)
  obtain ⟨V, hV, htaut⟩ := exists_isCovering_tautologicallyEquivalent_openCover B (B.obj hS)
    (S.affineCover)
  obtain ⟨β, hβ⟩ := htaut.2
  have hj : ∀ j, IsOpenImmersion (B.inclusion.map (V.f j)) ∧ IsAffine (B.inclusion.obj (V.X j)) := by
    intro j
    obtain ⟨e₀, he⟩ := hβ j
    let e : B.inclusion.obj (V.X j) ≅ S.affineCover.X (β j) := e₀
    constructor
    · have : B.inclusion.map (V.f j) = e.hom ≫ S.affineCover.f (β j) := he.symm
      rw [this]
      infer_instance
    · exact .of_isIso e.hom
  let E : PreZeroHypercover.{u + 1} (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) :=
    ⟨V.I₀, fun i => Over.mk (V.f i), fun i => Over.homMk (V.f i) (Category.comp_id _)⟩
  obtain ⟨WX, w, hws, -⟩ := hX.exists_atlas
  have hμ : max ℵ₀ (max S.size (2 ^ ((SCH).obj WX).size)) < B.cutoff := max_lt B.aleph0_lt_cutoff
    (max_lt hS (B.cutoff_isStrongPrelimit WX.left.property))
  have hloc := fun i : V.I₀ =>
    haveI : IsAffine (V.X i).1 := (hj i).2
    attP_local hZ hM hX hsep hfp act K (T₀' := (V.X i).1) (hT := (V.X i).2) (V.f i) (hj i).1
  have hfi : ∀ i : E.I₀, IsAlgebraicSpace B S hS (yoneda.obj (E.X i) ⨯ attP act K) := fun i =>
    (isAlgebraicSpace_restrict_iff_product B (V.X i).1 S (V.X i).2 hS (V.f i) _).1 (hloc i).1
  refine isAlgebraicSpace_of_isCovering_of_atlas_size_le hsF E hV hfi hμ
    fun i W j hWaff hjo => ?_
  have hEo : IsOpenImmersion ((SCH).map (Over.mkIdTerminal.from (E.X i) : E.X i ⟶ T1 B S hS)) := by
    rw [show (SCH).map (Over.mkIdTerminal.from (E.X i) : E.X i ⟶ T1 B S hS) = B.inclusion.map (V.f i) from
      congrArg B.inclusion.map (Over.mkIdTerminal_from_left (E.X i))]
    exact (hj i).1
  exact attP_member_atlas hX hsep act K hEo (hfi i) (hloc i).2 j hjo hws (le_max_left _ _) hμ
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))

end AlgMag.Final
