/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSAsmTower
import AlgMag.ChartS5Close
import AlgMag.ChartMain
import AlgMag.ChartQSStratOrbit
import AlgMag.ChartQSTop
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# `ChartLemmaQS` from named hypotheses (the chart-lemma proof without separatedness, §§1, 8)

The assembly `ChartAssembly.chartLemmaFG_of_section5` for `X` quasi-separated, with no separatedness:

* `exists_section5_input_qs`: `exists_section5_input`, `X` any algebraic space.
* `exists_chart_at_point_qs`: `exists_chart_at_point`, `X` decent.
* `section5Output_qs`: `section5FromEffectivity`, `X` decent.
* `exists_orbit_data_qs`: `exists_orbit_data`, `X` quasi-separated, from `ChartPoint.Lemma11QS`.
* `EffectivityQS`: Theorem 4.1 existence for `X` quasi-separated. A named hypothesis.
* `chartLemmaQS_of_props`: `ChartQSTop.ChartLemmaQS` from `Lemma11QS` and `EffectivityQS`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

set_option synthInstance.maxHeartbeats 400000

namespace AlgMag.ChartQSAsm

open ChartMain ChartS5 ChartPoint ChartConclude ChartAssembly AlgMag.ChartQSStrat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] Space.pointTopology

section Input

variable [IsAffine S] [AddMonoid.FG M] [DecidableEq M]

/-- **The bridge**, `X` any algebraic space (§§2–4 of the chart-lemma proof): `T = Spec C`, `φ : T → X` from
Theorem 4.1, and the inputs of §5. -/
theorem exists_section5_input_qs (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    (N : AddSubgroup M) [AddMonoid.FG N] (o : yoneda.obj (Ob p.P N) ⟶ X) (u : p.P ⟶ Ob p.P N)
    (ho : ClosedP o) (hoe : IsEquivariant (oAct N) actX o) (hux : yoneda.map u ≫ o = p.x)
    (heff : ChartConclude.EquivariantEffectivity X actX) :
    Finite (RT p.P) ∧
    ∃ (T : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
      (actT : AAction (fppfO B S hS) M (yoneda.obj T))
      (m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (φ : yoneda.obj T ⟶ X) (u' : p.P ⟶ T),
      Section5Input actX p actT m φ u' := by
  haveI hP := isAffine_of_chartPoint p
  have hK := isField_of_chartPoint p
  have hfin := finite_of_chartPoint_lft hSft hX hlft p
  refine ⟨hfin, ?_⟩
  obtain ⟨Ua, φa, hs, he⟩ := hX.exists_atlas
  have hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Ua) := by
    haveI := lft_chart hSft hlft he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
    exact LocallyOfFiniteType.isLocallyNoetherian (terminal.from _)
  let D0 : OrbitInput actX := ⟨Ob p.P N, inferInstance, oAct N, o, ho, hoe⟩
  obtain ⟨Y, c, hcm, hcr, hce, hcj⟩ := exists_affineTower_qs D0 hX hs he hN
  haveI := hcm 0
  obtain ⟨e0, he0i, he0⟩ := exists_orbit_iso ho hs he (hcr 0)
  haveI := he0i
  have hinj := fun A => (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (mono_of_closedP ho) A)
  have hf0 : IsEquivariant (Y.act 0) (oAct N) (yoneda.map (inv e0)) := fun {A} g t => hinj A (by
    have e1 : ∀ x, o.app A ((yoneda.map (inv e0)).app A x) = (c 0).app A x := fun x => by
      have : yoneda.map (inv e0) ≫ o = c 0 := by
        rw [← he0, ← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]
      exact congrArg (fun z => z.app A x) this
    rw [e1, hoe, e1]
    exact hce 0 g t)
  obtain ⟨hc, hk⟩ := tower_complete hK Y (inv e0) hf0
  let D := ofAffineTower Y hc hk
  obtain ⟨φ, hφe, hφ⟩ := D.exists_phi c hcj actX hce heff
  have hcl : ∀ n, ClosedP (c n) := fun n => by
    haveI := hcm n
    exact closedP_of_range (hcr n) (isClosedSubspace_thickening ho hX hs he n).2
  refine ⟨D.Tb, inferInstance, D.actTb, D.mTb, φ, u ≫ e0 ≫ D.sn 0, ?_⟩
  let e0' : Ob p.P N ⟶ D.U 0 := e0
  haveI : IsIso e0' := he0i
  exact CTower.section5Input D c hcj actX hce hφ hφe p hK hfin ho hoe u hux e0' he0 (hcm 0) hcl
    (fun n V _ e => by
      haveI := hcm n
      exact thick_data ho hs he n (hcr n) e)

/-- **The chart at a closed point**, `X` decent. Stacks 0BBP at the point of `X` given by `p`: an affine `V`, étale
over `X`, with one point `w` above `p` and `κ(p) = κ(w)`. By uniqueness of monomorphic field-valued
representatives, `P → X` factors through `Spec κ(w) → V`. The fibre of `V → X` over the closed `P → X` is
a closed subscheme of `V` with support `w`, so `w` is closed in `V`, `Spec κ(w) → V` is a closed
immersion, and `Γ(V) → Γ(P)` is onto. -/
theorem exists_chart_at_point_qs [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hdec : Space.IsDecentSpace B S hS X) (p : AlgMag.ChartPoint X) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V))
      (e : yoneda.obj V ⟶ X) (v : p.P ⟶ V),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) e ∧
      yoneda.map v ≫ e = p.x ∧
      Function.Surjective ((SCH).map v).appTop.hom := by
  classical
  letI := p.field
  haveI hPs := subsingleton_points_chartPoint p
  -- the field-valued point of `X`
  let q₀ := pointField p
  let q := Space.FieldValuedPoint.map B S hS (yoneda.obj p.P) p.x q₀
  let x₀ : Space.points B S hS X := q.class B S hS X
  have hx₀ : ∀ t : Space.points B S hS (yoneda.obj p.P), Space.pointsMap B S hS _ p.x t = x₀ := fun t => by
    rw [Subsingleton.elim t (q₀.class B S hS _)]
    rfl
  obtain ⟨E, hEa, huniq, φ, hφ, g, hgS, hgsq⟩ :=
    Space.exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec x₀
  -- `fieldMorphism q` is the composite with `P ≅ Spec k`
  let iso' : q.siteObject B S hS X ≅ p.P := pointFieldIso p
  have hfm : yonedaEquiv.symm q.value = yoneda.map iso'.hom ≫ p.x := by
    have hq₀ : yonedaEquiv.symm q₀.value = yoneda.map (pointFieldIso p).hom := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
      apply Over.OverMorphism.ext
      rfl
    have h := yonedaEquiv_symm_naturality_right (q₀.siteObject B S hS (yoneda.obj p.P)) p.x q₀.value
    rw [hq₀] at h
    exact h.symm
  haveI hmx : Mono p.x := ChartMain.mono_of_closedP p.isClosed
  haveI hmq : Mono (yonedaEquiv.symm q.value) := by
    rw [hfm]
    exact mono_comp _ _
  -- the chosen representative
  let r := (Space.residueFieldRepresentative B S hS X hdec x₀).1
  haveI hmr : Mono (yonedaEquiv.symm r.value) := (Space.residueFieldRepresentative B S hS X hdec x₀).2.2
  obtain ⟨e₀, he₀⟩ := Space.iso_of_mono_of_point_eq B S hS X hX r q
    (Space.residueFieldRepresentative B S hS X hdec x₀).2.1
  have hrq : yoneda.map e₀.hom ≫ yonedaEquiv.symm q.value = yonedaEquiv.symm r.value := by
    rw [yonedaEquiv_symm_naturality_left e₀.hom X q.value, he₀]
  -- `g` is invertible
  haveI hφi : IsIso (CommRingCat.ofHom φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hφ
  haveI hgi : IsIso g := by
    haveI : IsIso (B.inclusion.map ((Over.forget (B.obj hS)).map g)) := by
      show IsIso (B.inclusion.map g.left)
      rw [hgS]
      exact CategoryTheory.Functor.map_isIso Scheme.Spec (CommRingCat.ofHom φ).op
    haveI : IsIso ((Over.forget (B.obj hS)).map g) := isIso_of_reflects_iso _ B.inclusion
    exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  let w := E.point
  let hw := E.residueField_contained
  let resW := Space.residueFieldMap B S hS E.scheme w hw
  let v : p.P ⟶ E.scheme := iso'.inv ≫ e₀.inv ≫ inv g ≫ resW
  have hvx : yoneda.map v ≫ E.toSpace = p.x := by
    have h1 : yoneda.map resW ≫ E.toSpace = yoneda.map g ≫ yonedaEquiv.symm r.value := hgsq.symm
    have h2 : yoneda.map (inv g) ≫ yoneda.map resW ≫ E.toSpace = yonedaEquiv.symm r.value := by
      rw [h1, ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have h3 : yoneda.map e₀.inv ≫ yonedaEquiv.symm r.value = yonedaEquiv.symm q.value := by
      rw [← hrq, ← Category.assoc, ← CategoryTheory.Functor.map_comp, e₀.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [v, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [h2, h3, hfm, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  -- a map to `V` lying over `P` hits only `w`
  have honly : ∀ {T : BigFppfOver B S hS} (t : T ⟶ E.scheme) (b : T ⟶ p.P),
      yoneda.map t ≫ E.toSpace = yoneda.map b ≫ p.x → ∀ τ : (SCH).obj T, (SCH).map t τ = w := by
    intro T t b hsq τ
    have hc := B.residueField_spec_contains T.left.property τ
    have hc' := B.residueField_spec_contains E.scheme.left.property ((SCH).map t τ)
    have hu : Space.pointsMap B S hS _ E.toSpace
        (Space.presheafPoint B S hS E.scheme ((SCH).map t τ) hc') = x₀ := by
      have e1 := Space.pointsMap_presheafPoint B S hS T E.scheme t τ hc hc'
      calc Space.pointsMap B S hS _ E.toSpace
            (Space.presheafPoint B S hS E.scheme ((SCH).map t τ) hc')
          = Space.pointsMap B S hS _ E.toSpace (Space.pointsMap B S hS _ (yoneda.map t)
              (Space.presheafPoint B S hS T τ hc)) := congrArg _ e1.symm
        _ = Space.pointsMap B S hS _ (yoneda.map t ≫ E.toSpace)
              (Space.presheafPoint B S hS T τ hc) := (Space.pointsMap_comp_apply ..).symm
        _ = Space.pointsMap B S hS _ (yoneda.map b ≫ p.x)
              (Space.presheafPoint B S hS T τ hc) := by rw [hsq]
        _ = Space.pointsMap B S hS _ p.x (Space.pointsMap B S hS _ (yoneda.map b)
              (Space.presheafPoint B S hS T τ hc)) := Space.pointsMap_comp_apply ..
        _ = x₀ := hx₀ _
    have h := huniq _ hu
    have h2 := congrArg (Space.pointsToScheme B S hS E.scheme) h
    rwa [Space.pointsToScheme_presheafPoint, Space.pointsToScheme_presheafPoint] at h2
  -- the fibre over the closed `P → X`
  have hrep := p.isClosed.rep
  have sq := hrep.isPullback E.toSpace
  let Y := hrep.pullback E.toSpace
  let ι : Y ⟶ E.scheme := hrep.snd E.toSpace
  obtain ⟨toP, htoP⟩ := yoneda.map_surjective (hrep.fst E.toSpace)
  have hcl : IsClosedImmersion ((SCH).map ι) := p.isClosed.property_snd E.toSpace
  have hιw : ∀ y : (SCH).obj Y, (SCH).map ι y = w := fun y =>
    honly ι toP (by rw [htoP]; exact sq.w.symm) y
  have hl : yoneda.map (𝟙 p.P) ≫ p.x = yoneda.map v ≫ E.toSpace := by simp [hvx]
  let lift0 := sq.lift (yoneda.map (𝟙 p.P)) (yoneda.map v) hl
  obtain ⟨l, hl0⟩ := yoneda.map_surjective lift0
  have hPne : Nonempty ((SCH).obj p.P) := ⟨p.iso.inv (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum p.k)⟩
  obtain ⟨y₀⟩ := hPne
  have hrange : Set.range ((SCH).map ι) = {w} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact hιw y
    · rintro rfl
      exact ⟨(SCH).map l y₀, hιw _⟩
  have hclw : IsClosed ({w} : Set E.scheme.left.1) := by
    rw [← hrange]
    exact ((SCH).map ι).isClosedEmbedding.isClosed_range
  haveI hci : IsClosedImmersion (E.scheme.left.1.fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.1 hclw
  haveI hEa' : IsAffine ((SCH).obj E.scheme) := hEa
  haveI hci' : IsClosedImmersion ((SCH).map resW) := hci
  haveI hi0 : IsIso (iso'.inv ≫ e₀.inv ≫ inv g) := inferInstance
  haveI hi1 : IsIso ((SCH).map (iso'.inv ≫ e₀.inv ≫ inv g)) := CategoryTheory.Functor.map_isIso _ _
  have hvcl : IsClosedImmersion ((SCH).map v) := by
    have hv : (SCH).map v = (SCH).map (iso'.inv ≫ e₀.inv ≫ inv g) ≫ (SCH).map resW := by
      rw [← CategoryTheory.Functor.map_comp]
      simp only [v, Category.assoc]
    rw [hv]
    infer_instance
  exact ⟨E.scheme, hEa, E.toSpace, v, Space.presheaf_etale_of_isEtale B S hS E.etale_toSpace, hvx,
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map v)).2⟩


/-- **§5**, `X` decent: `Section5FromEffectivity` with `X` decent in place of `X` separated. -/
theorem section5Output_qs [AddMonoid.FG M] [DecidableEq M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hdec : Space.IsDecentSpace B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    (N : AddSubgroup M) [AddMonoid.FG N] (o : yoneda.obj (Ob p.P N) ⟶ X) (u : p.P ⟶ Ob p.P N)
    (ho : ClosedP o) (hoe : IsEquivariant (oAct N) actX o) (hux : yoneda.map u ≫ o = p.x)
    (heff : EquivariantEffectivity X actX) : Section5Output actX p := by
  obtain ⟨hfin, T, hTa, actT, m, φ, u', D⟩ :=
    exists_section5_input_qs hSft hX hlft actX p N o u ho hoe hux heff
  obtain ⟨V, hVa, e, v, he, hve, hvs⟩ := exists_chart_at_point_qs hX hdec p
  letI := gradedRingOfAction actT
  haveI := D.noeth
  haveI := isNoetherianRing_chart' hSft hlft he
  haveI := finiteType_top (B := B) (hS := hS) hSft
  haveI : Finite p.k := by
    letI := p.field
    let e1 : Γ((BigFppfOver.toScheme B S hS).obj p.P, ⊤) ≃+* Γ(Spec (.of p.k), ⊤) :=
      (Scheme.Γ.mapIso p.iso.symm.op).commRingCatIsoToRingEquiv
    let e2 : Γ(Spec (.of p.k), ⊤) ≃+* p.k := (Scheme.ΓSpecIso (.of p.k)).commRingCatIsoToRingEquiv
    exact Finite.of_surjective _ (e1.trans e2).surjective
  have hXft : Space.IsLocallyOfFiniteType B S hS (toBase X) := by
    intro U' V' f' g' α hf' hg' c
    haveI := Space.isMultiplicative_presheaf_etale B S hS
    have hY : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
      (Over.mkIdTerminal).isTerminalObj yoneda
    have hiso : IsIso (terminal.from (yoneda.obj (siteTop (B := B) (S := S) (hS := hS)))) :=
      ⟨hY.from _, hY.hom_ext _ _, terminal.hom_ext _ _⟩
    have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (g' ≫ terminal.from _) :=
      MorphismProperty.comp_mem _ _ _ hg' (MorphismProperty.of_isIso _ _)
    exact hlft U' V' f' (g' ≫ terminal.from _) α hf' hb (terminal.hom_ext _ _)
  obtain ⟨Tg, hTg, hgen⟩ := D.hgen
  exact section5Output_of_input actT ChartArtin.artinApproxFP (toCompletePair D.complete) actX hX hXft
    (limitPreserving_of_lft hSft hX hlft) φ D.equivariant p u' D.liesOver D.kills D.surj Tg hTg hgen
    D.hOfC D.hMono he v hve hvs (fun j hj => by
      obtain ⟨hoj, hi⟩ := D.thick j hj
      exact ⟨hoj, hi e v hve⟩)

end Input


section Orbit

variable [IsAffine S] [AddMonoid.FG M]

set_option maxHeartbeats 4000000 in
/-- **§1**, `X` quasi-separated, from `Lemma11QS`: `ChartPoint.exists_orbitInput` with the orbit made explicit: the orbit is `O = Ob P N`
(which `OrbitInput` forgets), with its point `u` a section of `O → P`. -/
theorem exists_orbit_data_qs (hL11 : Lemma11QS B S hS) (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hqs : Space.IsQuasiSeparated B S hS (terminal.from X))
    (hft : Space.IsFiniteType B S hS (terminal.from X))
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X) :
    ∃ (Zp : BigFppfOver B S hS) (ιz : p.P ⟶ Zp) (X'' : Subfunctor (XP X Zp))
      (hst : ∀ {T : (BigFppfOver B S hS)ᵒᵖ} (h : APt (fppfO B S hS) M T)
        (x : X''.toFunctor.obj T),
        ∃ y, X''.ι.app T y = (actProd Zp actX).smul h (X''.ι.app T x))
      (N : AddSubgroup M) (_ : AddMonoid.FG N) (o : yoneda.obj (Ob p.P N) ⟶ X''.toFunctor)
      (u : p.P ⟶ Ob p.P N),
      IsAffine ((SCH).obj Zp) ∧
      ClosedP o ∧ IsEquivariant (oAct N) (actOfMono (actProd Zp actX) X''.ι hst) o ∧
      Etale ((SCH).map (toTop Zp)) ∧ Mono ιz ∧ Space.IsOpenSubspace B S hS X'' ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH)))
        (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) ∧
      u ≫ Oπ p.P N = 𝟙 _ ∧
      yoneda.map u ≫ o ≫ X''.ι = FunctorToTypes.prod.lift p.x (yoneda.map ιz) := by
  have hK := isField_of_chartPoint p
  haveI hP := isAffine_of_chartPoint p
  have hfin := finite_of_chartPoint hSft hX hft p
  obtain ⟨Zp, ιz, hZa, hιm, hZe⟩ := exists_Zp (P := p.P) hK hfin
  haveI := hZa
  haveI := hιm
  obtain ⟨hA, hE⟩ := xp_props_qs (X := X) hX hZe
  have hs' := isQuasiSeparated_toBase_XP (X := X) hA hX hqs (Zp := Zp)
  let x' : yoneda.obj p.P ⟶ XP X Zp := FunctorToTypes.prod.lift p.x (yoneda.map ιz)
  let act' := actProd Zp actX
  obtain ⟨Z₀, hZ₀⟩ := exists_stabilizer_closedPoint hK actX p.x p.isClosed
  have hZ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ p.P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      act'.smul (U := op T) h (x'.app (op T) t) = x'.app (op T) t ↔
        ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1 := by
    intro T t h
    rw [← hZ₀ t h]
    constructor
    · intro e
      exact congrArg Prod.fst e
    · intro e
      exact Prod.ext e rfl
  haveI hfg : AddMonoid.FG Z₀ := fg_addSubgroup Z₀
  obtain ⟨o, ho⟩ := exists_orbit (N := Z₀) hK hA hZ
  have hoe : IsEquivariant (oAct Z₀) act' o := orbit_equivariant hK hA ho
  have hoi : ∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob p.P Z₀),
      o.app (op T) a = o.app (op T) b → a = b := fun a b hab =>
    orbit_injective hK hA hZ ho FunctorToTypes.prod.snd (fun _ _ => rfl) ιz rfl a b hab
  -- finiteness
  have hSft' : LocallyOfFiniteType (terminal.from ((SCH).obj (siteTop (B := B) (S := S) (hS := hS)))) :=
    hSft
  have hPZ : LocallyOfFiniteType (toZ p.P) := by
    refine (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2 ?_
    classical
    haveI : Fintype (RT p.P) := @Fintype.ofFinite _ hfin
    letI := (toZ p.P).appTop.hom.toAlgebra
    refine (⟨⟨Finset.univ, ?_⟩⟩ : Algebra.FiniteType Γ(Spec (.of (ULift.{u} ℤ)), ⊤) (RT p.P))
    rw [eq_top_iff]
    intro x _
    exact Algebra.subset_adjoin (by simp)
  have hO : LocallyOfFiniteType (toZ (Ob p.P Z₀)) := by
    have e : toZ (Ob p.P Z₀) = (SCH).map (Oπ p.P Z₀) ≫ toZ p.P := (comp_toZ _).symm
    rw [e]
    have : LocallyOfFiniteType ((SCH).map (Oπ p.P Z₀)) := by
      change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom _) ≫ ((SCH).obj p.P).isoSpec.inv)
      have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.singleZeroRingHom : RT p.P →+* RN p.P Z₀))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        change (algebraMap (RT p.P) (RN p.P Z₀)).FiniteType
        exact (RingHom.finiteType_algebraMap).2 (AddMonoidAlgebra.finiteType_of_fg _ _)
      infer_instance
    infer_instance
  have hUlft : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ XP X Zp),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) φ → LocallyOfFiniteType (toZ U) := by
    intro U φ hφ
    have hcomp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change Etale _
      rw [Functor.map_comp]
      have : Etale ((SCH).map f) := hf
      have : Etale ((SCH).map g) := hg
      infer_instance⟩
    have hφX := MorphismProperty.comp_mem _ _ _ hφ hE
    let T1 : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
    let hT : IsTerminal T1 := Over.mkIdTerminal
    let hY : IsTerminal (yoneda.obj T1) := Limits.IsTerminal.isTerminalObj yoneda T1 hT
    let bb : yoneda.obj T1 ≅ ⊤_ _ := hY.uniqueUpToIso terminalIsTerminal
    have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (SCH)).presheaf bb.hom := Space.presheaf_etale_of_iso B S hS bb
    have hl : LocallyOfFiniteType ((SCH).map (hT.from U)) :=
      hft.1 U T1 _ bb.hom (hT.from U) hφX hb (Subsingleton.elim _ _ |>.trans rfl)
    change LocallyOfFiniteType ((SCH).map (toTop U) ≫ _ ≫ _)
    have : LocallyOfFiniteType ((SCH).map (toTop U)) := hl
    infer_instance
  obtain ⟨X'', hle, hop, hst, hcl⟩ := hL11 hA hs' hK act' o hoe hoi hO hUlft
  obtain ⟨σ, hσ1, hσ2⟩ := exists_gk_lift (T := p.P) (M := M) (𝟙 p.P) 1
  let u : p.P ⟶ Ob p.P Z₀ := σ ≫ qN Z₀
  have hu : o.app (op p.P) u = x'.app (op p.P) (𝟙 p.P) := by
    have e1 : o.app (op p.P) (σ ≫ qN Z₀) = (orbMap act' x').app (op p.P) σ :=
      congrArg (fun k => k.app (op p.P) σ) ho
    rw [e1, orbMap_app, hσ1, hσ2]
    exact act'.one_smul (U := op p.P) _
  refine ⟨Zp, ιz, X'', hst, Z₀, hfg, Subfunctor.lift o hle, u, hZa, hcl, ?_, hZe, hιm,
    hop, hE, ?_, ?_⟩
  · intro T h a
    have hinj : Function.Injective (X''.ι.app T) := fun _ _ h => Subtype.ext h
    apply hinj
    rw [actOfMono_spec]
    exact hoe h a
  · change (σ ≫ qN Z₀) ≫ Oπ p.P Z₀ = _
    rw [Category.assoc, qN_π]
    exact hσ1
  · apply yonedaEquiv.injective
    change o.app (op p.P) (𝟙 p.P ≫ u) = x'.app (op p.P) (𝟙 p.P)
    rw [Category.id_comp]
    exact hu

end Orbit

section Main

variable (B S hS M) in
/-- **Theorem 4.1, existence**, for quasi-separated spaces: a named hypothesis. `ChartQS.effective_of_noetherian`
with its inputs for `X` quasi-separated gives it. -/
def EffectivityQS : Prop :=
  IsAffine S → LocallyOfFiniteType (terminal.from S) →
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (_ : Space.IsQuasiSeparated B S hS (terminal.from X))
    (_ : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (_ : Space.IsQuasiCompactSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (_ : AddMonoid.FG M),
    @EquivariantEffectivity B S hS M _ ‹_› X actX

/-- A subspace of a quasi-separated space over the base, as an absolutely quasi-separated space. -/
theorem isAbsolutelyQuasiSeparated_of_mono [IsAffine S] {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (ι : Y ⟶ Z) [Mono ι]
    (hq : Space.IsQuasiSeparated B S hS (toBase Z)) :
    Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y := by
  have h1 : Space.IsQuasiSeparated B S hS (toBase Y) :=
    Space.isQuasiCompact_of_isPullback B S hS
      (diagPb ι (toBase Y) (toBase Z) (𝟙 _) (by
        rw [Category.comp_id]
        exact (Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).hom_ext _ _)) hq
  exact Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal hY
    (Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal
      (siteTop (B := B) (S := S) (hS := hS)) ‹IsAffine S›) h1

/-- `terminal.from Y` is quasi-separated if `Y` is absolutely quasi-separated. -/
theorem isQuasiSeparated_terminal_of_mono [IsAffine S] {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (h : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    Space.IsQuasiSeparated B S hS (terminal.from Y) :=
  Space.isQuasiSeparated_of_isQuasiSeparatedOver B S hS
    (Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS B.contains_terminal hY h) _

/-- **The chart lemma for quasi-separated spaces**, from Lemma 1.1 and Theorem 4.1 for them. The
assembly `ChartAssembly.chartLemmaFG_of_section5`. -/
theorem chartLemmaQS_of_props (h11 : ∀ [IsAffine S], Lemma11QS B S hS)
    (heffQS : EffectivityQS B S hS M) : ChartQSTop.ChartLemmaQS B S hS M := by
  intro hfg haff hSft X hX hqsA hft actX p
  classical
  haveI := hfg
  haveI := haff
  have hqs : Space.IsQuasiSeparated B S hS (terminal.from X) :=
    isQuasiSeparated_terminal_of_mono hX hqsA
  obtain ⟨Zp, ιz, X'', hst, N, hN, o, u, hZa, hoc, hoe, hZe, hιm, hop, hE, hus, hx⟩ :=
    exists_orbit_data_qs h11 hSft hX hqs hft actX p
  haveI := hZa
  haveI := hN
  obtain ⟨hA, -⟩ := xp_props_qs (X := X) hX hZe
  have hsP := isQuasiSeparated_toBase_XP (X := X) hA hX hqs (Zp := Zp)
  let act' := actOfMono (actProd Zp actX) X''.ι hst
  have hY := hop.1
  have hT := isAlgebraicSpace_terminal (B := B) (S := S) (hS := hS)
  have hEt : Space.IsLocallyOfFiniteType B S hS (FunctorToTypes.prod.fst (F := X) (G := yoneda.obj Zp)) :=
    ChartStratum.isLocallyOfFiniteType_of_etale _ (Space.isEtale_of_presheaf_etale B S hS hE)
  have hlP : Space.IsLocallyOfFiniteType B S hS (terminal.from (XP X Zp)) := by
    have h := Space.isLocallyOfFiniteType_comp B S hS hA hX hT _ (terminal.from X) hEt hft.1
    rwa [terminal.comp_from] at h
  have hlY : Space.IsLocallyOfFiniteType B S hS (terminal.from X''.toFunctor) := by
    have h := Space.isLocallyOfFiniteType_comp B S hS hY hA hT X''.ι (terminal.from _)
      (ChartStratum.isLocallyOfFiniteType_of_etale _ (Space.isEtale_of_isOpenImmersion B S hS hop.2)) hlP
    rwa [terminal.comp_from] at h
  have hqP : Space.IsQuasiCompactSpace B S hS (XP X Zp) := by
    have hZq : Space.IsQuasiCompactSpace B S hS (yoneda.obj Zp) :=
      Space.isQuasiCompact_yoneda_of_compact B S hS Zp inferInstance
    have h := hft.2 (yoneda.obj Zp) (isAlgebraicSpace_yoneda B S hS _) hZq (terminal.from _)
    let e : pullback (terminal.from (yoneda.obj Zp)) (terminal.from X) ⟶ XP X Zp :=
      FunctorToTypes.prod.lift (pullback.snd _ _) (pullback.fst _ _)
    let ei : XP X Zp ⟶ pullback (terminal.from (yoneda.obj Zp)) (terminal.from X) :=
      pullback.lift FunctorToTypes.prod.snd FunctorToTypes.prod.fst (terminal.hom_ext _ _)
    have e1 : e ≫ ei = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [ei, Category.assoc, pullback.lift_fst, Category.id_comp]; rfl
      · simp only [ei, Category.assoc, pullback.lift_snd, Category.id_comp]; rfl
    have hs1 : ei ≫ pullback.snd (terminal.from (yoneda.obj Zp)) (terminal.from X) =
        FunctorToTypes.prod.fst := pullback.lift_snd _ _ _
    have hf1 : ei ≫ pullback.fst (terminal.from (yoneda.obj Zp)) (terminal.from X) =
        FunctorToTypes.prod.snd := pullback.lift_fst _ _ _
    have e2 : ei ≫ e = 𝟙 _ := by
      apply NatTrans.ext
      funext T
      apply ConcreteCategory.hom_ext
      intro x
      refine Prod.ext ?_ ?_
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app hs1 T) x
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app hf1 T) x
    let E : pullback (terminal.from (yoneda.obj Zp)) (terminal.from X) ≅ XP X Zp :=
      ⟨e, ei, e1, e2⟩
    haveI : IsIso E.hom := ⟨ei, e1, e2⟩
    exact Space.IsQuasiCompactSpace.of_isSurjective B S hS
      (Space.isAlgebraicSpace_of_iso B S hS E.symm hA) hA
      (Space.pointsMap_surjective_of_isIso B S hS E.hom) h
  haveI := noetherianSpace_points hSft hlP (hasAffineAtlas_of_qc hA hqP)
  have hqY : Space.IsQuasiCompactSpace B S hS X''.toFunctor := by
    refine (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS _ hY).2 ?_
    have hemb := Space.isEmbedding_pointsMap_of_isImmersion B S hS hA X''.ι
      (isImmersion_of_open hop.2)
    haveI : TopologicalSpace.NoetherianSpace (Space.points B S hS X''.toFunctor) :=
      hemb.isInducing.noetherianSpace
    infer_instance
  have hqAY := isAbsolutelyQuasiSeparated_of_mono hY X''.ι hsP
  have hdecY : Space.IsDecentSpace B S hS X''.toFunctor :=
    Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS _ hY hqAY
  have heffY := heffQS haff hSft _ hY (isQuasiSeparated_terminal_of_mono hY hqAY) hlY hqY act' hfg
  let p'' : AlgMag.ChartPoint X''.toFunctor :=
    { P := p.P, k := p.k, field := p.field, iso := p.iso, x := yoneda.map u ≫ o,
      isClosed := isClosedP_comp_point o hoc u hus }
  have hs5 := section5Output_qs hSft hY hdecY hlY act' p'' N o u hoc hoe rfl heffY
  obtain ⟨U, actU, f', v, hch⟩ := exists_chart_of_section5 p'' hs5
  refine ⟨U, actU, f' ≫ X''.ι ≫ FunctorToTypes.prod.fst, v, ?_⟩
  have hc := isChartAt_of_XP actX p hE actU (f' ≫ X''.ι) v hch.affine ?_ ?_ ?_ ?_
  · have hc' : IsChartAt actX p U actU (f' ≫ X''.ι ≫ FunctorToTypes.prod.fst) v := by
      simpa [Category.assoc] using hc
    exact ⟨hc'.affine, hc'.equivariant, hc'.etale, hc'.lies_over⟩
  · intro T g a
    change X''.ι.app T (f'.app T (actU.smul g a)) = _
    rw [hch.equivariant]
    exact actOfMono_spec _ _ _ _ _
  · have hmap := Space.isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _ hch.etale
      (Space.presheaf_etale_of_isOpenImmersion B S hS hop.2)
  · have h1 : yoneda.map v ≫ f' = yoneda.map u ≫ o := hch.lies_over
    calc yoneda.map v ≫ (f' ≫ X''.ι) ≫ FunctorToTypes.prod.fst
        = (yoneda.map v ≫ f') ≫ X''.ι ≫ FunctorToTypes.prod.fst := by simp only [Category.assoc]
      _ = (yoneda.map u ≫ o ≫ X''.ι) ≫ FunctorToTypes.prod.fst := by
          rw [h1]; simp only [Category.assoc]
      _ = p.x := by rw [hx]; simp
  · intro T t g hfix
    refine hch.stabilizer t g ?_
    apply Subtype.ext
    exact (actOfMono_spec (actProd Zp actX) X''.ι hst g _).trans hfix

end Main

end AlgMag.ChartQSAsm

#print axioms AlgMag.ChartQSAsm.exists_section5_input_qs
#print axioms AlgMag.ChartQSAsm.exists_chart_at_point_qs
#print axioms AlgMag.ChartQSAsm.section5Output_qs
#print axioms AlgMag.ChartQSAsm.exists_orbit_data_qs
#print axioms AlgMag.ChartQSAsm.chartLemmaQS_of_props
