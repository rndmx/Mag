/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveAlg
import AlgMag.ChartDeligneInst
import AlgMag.ChartStratum
import AlgMag.ChartConclude
import AlgMag.ChartPointOrbitInput
import AlgMag.ChartPointReduce
import AlgMag.ChartTower
import AlgMag.ChartEtaleLocus
import AlgMag.StronglyFPR
import AlgMag.ChartStatement
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding

/-!
# The chart lemma: assembly of the chart-lemma proof

* `effective_of_lft`: **Theorem 4.1, existence**, `X` separated, locally of finite type and
  quasi-compact over `S` affine of finite type over `ℤ`.
* `equivariantEffectivity_of_lft`: the same in the form `ChartConclude.EquivariantEffectivity`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartAssembly

open ChartMain

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- An étale chart of a space locally of finite type over `S` is of finite type over `ℤ` locally. -/
lemma lft_chart (hSft : LocallyOfFiniteType (terminal.from S))
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) {U : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    LocallyOfFiniteType (terminal.from ((SCH).obj U)) := by
  let V₀ : BigFppfOver B S hS := Over.mk (𝟙 _)
  have hV₀ : IsTerminal V₀ := Over.mkIdTerminal
  have hY : IsTerminal (yoneda.obj V₀) := hV₀.isTerminalObj yoneda
  have hiso : IsIso (terminal.from (yoneda.obj V₀)) := by
    refine ⟨hY.from _, hY.hom_ext _ _, terminal.hom_ext _ _⟩
  have hmap := Space.isMultiplicative_presheaf_etale B S hS
  have hb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (terminal.from (yoneda.obj V₀)) :=
    MorphismProperty.of_isIso _ _
  have h1 : LocallyOfFiniteType ((SCH).map (hV₀.from U)) :=
    hlft U V₀ f (terminal.from _) (hV₀.from U) he hb (terminal.hom_ext _ _)
  have e : terminal.from ((SCH).obj U) = (SCH).map (hV₀.from U) ≫ terminal.from S :=
    terminal.hom_ext _ _
  rw [e]
  exact @MorphismProperty.comp_mem _ _ @LocallyOfFiniteType _ _ _ _ _ _ h1 hSft

lemma isAlgebraicSpace_terminal :
    IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  Space.isAlgebraicSpace_of_iso B S hS
    ((((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
      terminalIsTerminal)) (isAlgebraicSpace_yoneda B S hS _)

lemma terminal_noeth : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsNoetherianRing (CommRingCat.of (ULift.{u} ℤ)) := ‹IsNoetherianRing (ULift.{u} ℤ)›
  exact isLocallyNoetherian_of_isOpenImmersion (terminalIsoIsTerminal specULiftZIsTerminal).hom

lemma isNoetherianRing_chart' [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) {U : BigFppfOver B S hS}
    [IsAffine ((SCH).obj U)] {f : yoneda.obj U ⟶ X}
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    IsNoetherianRing Γ((SCH).obj U, ⊤) :=
  AlgMag.StronglyFPR.isNoetherianRing_of_lft (lft_chart hSft hlft he)

lemma hasAffineAtlas_of_qc (hX : IsAlgebraicSpace B S hS X)
    (hq : Space.IsQuasiCompactSpace B S hS X) : HasAffineAtlas X := by
  obtain ⟨U, f, h1, h2, h3⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1 hq
  exact ⟨U, f, h1, h2, Space.presheaf_etale_of_isEtale B S hS h3⟩

lemma noetherianSpace_points [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (hA : HasAffineAtlas X) : TopologicalSpace.NoetherianSpace (Space.points B S hS X) := by
  obtain ⟨V, φ, hV, hs, he⟩ := hA
  haveI := hV
  haveI := lft_chart hSft hlft he
  haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
  haveI : IsLocallyNoetherian ((SCH).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from ((SCH).obj V))
  haveI : IsNoetherian ((SCH).obj V) := {}
  let G : (SCH).obj V → Space.points B S hS X := fun x =>
    Space.pointsMap B S hS (yoneda.obj V) φ ((Space.pointsEquivScheme B S hS V).symm x)
  have hc : Continuous G := by
    refine ⟨fun O hO => ?_⟩
    have h1 := (Space.continuous_pointsMap B S hS φ).isOpen_preimage O hO
    have h2 := (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V _).1 h1
    convert h2 using 1
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, Equiv.apply_symm_apply (Space.pointsEquivScheme B S hS V) x⟩
    · rintro ⟨w, hw, rfl⟩
      change Space.pointsMap B S hS (yoneda.obj V) φ
        ((Space.pointsEquivScheme B S hS V).symm (Space.pointsEquivScheme B S hS V w)) ∈ O
      rw [Equiv.symm_apply_apply]
      exact hw
  have hsu : Function.Surjective G :=
    (Space.isSurjective_of_presheafSurjective B S hS φ hs).comp
      (Space.pointsEquivScheme B S hS V).symm.surjective
  exact TopologicalSpace.noetherianSpace_of_surjective G hc hsu

theorem effective_of_lft [AddMonoid.FG M] [DecidableEq M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (actX : AAction (fppfO B S hS) M X) :
    Effective actX := by
  have hA := hasAffineAtlas_of_qc hX hq
  haveI := noetherianSpace_points hSft hlft hA
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_terminal
  have hl : ∀ C : ClosedStable actX,
      Space.IsLocallyOfFiniteType B S hS (terminal.from C.Z) := fun C => by
    have h := Space.isLocallyOfFiniteType_comp B S hS C.alg hX hT C.i (terminal.from X)
      (Space.isLocallyOfFiniteType_of_isClosedImmersion B S hS C.i C.closed) hlft
    rwa [terminal.comp_from] at h
  have hs : ∀ C : ClosedStable actX, Space.IsSeparatedOver B S hS C.Z := fun C =>
    Space.isSeparatedOver_of_isSeparated B S hS hsep
      (Space.isSeparated_of_isClosedImmersion B S hS C.i C.closed)
  have hN : Space.HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    obtain ⟨U, φ, hsu, he⟩ := hX.exists_atlas
    haveI := lft_chart hSft hlft he
    haveI : IsLocallyNoetherian (⊤_ Scheme.{u}) := terminal_noeth
    exact ⟨U, φ, hsu, he, LocallyOfFiniteType.isLocallyNoetherian
      (terminal.from ((SCH).obj U))⟩
  exact effective_of_noetherian_atlas hX hA
    (fun C => ⟨hs C, noetherianAlgebraization_of_lft C.Z C.alg (hs C) (hl C)⟩)
    (fun C => ChartStratum.affineStratum_closedStable hX hsep hN C)
    (fun C => DeligneInst.strataOverChart_proved C (hs C)
      (fun V φ hV he => by haveI := hV; exact isNoetherianRing_chart' hSft (hl C) he))
    (ClosedStable.self actX hX)

/-- **Theorem 4.1, existence**, as `ChartConclude.EquivariantEffectivity`. -/
theorem equivariantEffectivity_of_lft [AddMonoid.FG M] [IsAffine S]
    (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hlft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (hq : Space.IsQuasiCompactSpace B S hS X) (actX : AAction (fppfO B S hS) M X) :
    ChartConclude.EquivariantEffectivity X actX := by
  intro T _ actT _ m hm φ h1 h2
  obtain ⟨y, hy, he⟩ := effective_of_lft hSft hX hsep hlft hq actX T actT m hm φ
    ⟨fun n k e he => h1 n k e he, fun n W t t' g ht => h2 n W t g t' ht⟩
  refine ⟨yonedaEquiv.symm y, ?_, fun n => ?_⟩
  · intro W g t
    exact he (W := W.unop) t g
  · exact hy n

section Orbit

open ChartPoint

variable [IsAffine S] [AddMonoid.FG M]

set_option maxHeartbeats 4000000 in
/-- **§1**, `ChartPoint.exists_orbitInput` with the orbit made explicit: the orbit is `O = Ob P N`
(which `OrbitInput` forgets), with its point `u` a section of `O → P`. -/
theorem exists_orbit_data (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
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
  obtain ⟨hA, hE, hSp⟩ := xp_props (X := X) hX hsep hZe
  have hs' := isSeparatedOver_of_space hSp
  let x' : yoneda.obj p.P ⟶ XP X Zp := FunctorToTypes.prod.lift p.x (yoneda.map ιz)
  let act' := actProd Zp actX
  obtain ⟨Z₀, hZ⟩ := exists_stabilizer hK hs' act' x'
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
  have hlfp := orbit_lfp (o := o) hA hs' hO hUlft
  obtain ⟨X'', hle, hop, hst, hcl⟩ := lemma11 hA hs' hK act' hoe hoi hlfp
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

open ChartPoint ChartConclude

/-- **What §5 has to prove** (`ChartConclude.Section5Output`, from Theorem 4.1): `X` separated, locally
of finite type and quasi-compact, `S` affine of finite type over `ℤ`, `p` a closed point in a closed
orbit `O = Ob P N`, and effectivity for `X`. -/
def Section5FromEffectivity (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] : Prop :=
  IsAffine S → LocallyOfFiniteType (terminal.from S) →
  ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
    (_ : Space.IsSeparatedOver B S hS X)
    (_ : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (_ : Space.IsQuasiCompactSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (p : AlgMag.ChartPoint X)
    (N : AddSubgroup M) (_ : AddMonoid.FG N) (o : yoneda.obj (Ob p.P N) ⟶ X) (u : p.P ⟶ Ob p.P N),
    ClosedP o → IsEquivariant (oAct N) actX o → yoneda.map u ≫ o = p.x →
    EquivariantEffectivity X actX → Section5Output actX p

variable [IsAffine S] [AddMonoid.FG M]

lemma isImmersion_of_open {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : Space.IsOpenImmersion B S hS f) : Space.IsImmersion B S hS f :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage _
      (fun _ _ f (_ : AlgebraicGeometry.IsOpenImmersion f) ↦
        (inferInstance : AlgebraicGeometry.IsImmersion f))) _ hf

lemma isClosedP_comp_point {p : AlgMag.ChartPoint X} {N : AddSubgroup M} [AddMonoid.FG N]
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (o : yoneda.obj (Ob p.P N) ⟶ Y) (ho : ClosedP o)
    (u : p.P ⟶ Ob p.P N) (hu : u ≫ Oπ p.P N = 𝟙 _) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map u ≫ o) := by
  haveI hP := isAffine_of_chartPoint p
  have h1 : IsClosedImmersion ((SCH).map u ≫ (SCH).map (Oπ p.P N)) := by
    rw [← Functor.map_comp, hu, CategoryTheory.Functor.map_id]; infer_instance
  have h2 : IsClosedImmersion ((SCH).map u) :=
    IsClosedImmersion.of_comp _ ((SCH).map (Oπ p.P N))
  have h3 : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map u) :=
    (Space.presheaf_yoneda_map_iff B S hS inferInstance u).2 h2
  exact MorphismProperty.comp_mem (Space.closedImmersionPresheafProperty B S hS) _ _ h3 ho

/-- **The chart lemma**, from §5. -/
theorem chartLemmaFG_of_section5 [DecidableEq M]
    (h5 : Section5FromEffectivity B S hS M) : ChartLemmaStatement B S hS M := by
  intro _ hSft X hX hsep hft actX p
  obtain ⟨Zp, ιz, X'', hst, N, hN, o, u, hZa, hoc, hoe, hZe, hιm, hop, hE, hus, hx⟩ :=
    exists_orbit_data hSft hX hsep hft actX p
  haveI := hZa
  obtain ⟨hA, -, hSp⟩ := xp_props (X := X) hX hsep hZe
  let act' := actOfMono (actProd Zp actX) X''.ι hst
  have hY := hop.1
  have hT := isAlgebraicSpace_terminal (B := B) (S := S) (hS := hS)
  have hsY : Space.IsSeparatedOver B S hS X''.toFunctor :=
    ChartStratum.isSeparatedOver_of_mono X''.ι hSp
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
  have heff := equivariantEffectivity_of_lft hSft hY hsY hlY hqY act'
  let p'' : AlgMag.ChartPoint X''.toFunctor :=
    { P := p.P, k := p.k, field := p.field, iso := p.iso, x := yoneda.map u ≫ o,
      isClosed := isClosedP_comp_point o hoc u hus }
  have hs5 := h5 inferInstance hSft _ hY hsY hlY hqY act' p'' N hN o u hoc hoe rfl heff
  obtain ⟨U, actU, f', v, hch⟩ := exists_chart_of_section5 p'' hs5
  refine ⟨U, actU, f' ≫ X''.ι ≫ FunctorToTypes.prod.fst, v, ?_⟩
  have hc := isChartAt_of_XP actX p hE actU (f' ≫ X''.ι) v hch.affine ?_ ?_ ?_ ?_
  · simpa [Category.assoc] using hc
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

omit [IsAffine S] [AddMonoid.FG M] in
/-- **The chart lemma** (`AlgMag.ChartLemmaStatementFG`, the chart-lemma proof, Theorem), with
§5 as a named hypothesis. -/
theorem chartLemmaStatementFG_of_section5
    (h5 : ∀ [AddMonoid.FG M] [DecidableEq M], Section5FromEffectivity B S hS M) :
    ChartLemmaStatementFG B S hS M := fun hfg haff => by
  classical
  haveI := hfg
  haveI := haff
  exact chartLemmaFG_of_section5 h5 haff

/-- What `Section5Output` asks beyond an étale neighbourhood: `EtaleLocusStable` is supplied by
`ChartEtale.etaleLocusStable` when `f` is locally of finite presentation. -/
theorem etaleLocusStable_of_lfp [AddMonoid.FG M] [DecidableEq M] (hX : IsAlgebraicSpace B S hS X)
    {actX : AAction (fppfO B S hS) M X} {W : BigFppfOver B S hS}
    [IsAffine ((SCH).obj W)] {actW : AAction (fppfO B S hS) M (yoneda.obj W)}
    {f : yoneda.obj W ⟶ X} (hf : IsEquivariant actW actX f)
    (hfp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) (SCH))) f) :
    EtaleLocusStable actW f :=
  ChartEtale.etaleLocusStable actW hX hf hfp

end Main

end AlgMag.ChartAssembly

#print axioms AlgMag.ChartAssembly.effective_of_lft
#print axioms AlgMag.ChartAssembly.chartLemmaStatementFG_of_section5
