/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartPointOrbitInput
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Lemma 1.1 for quasi-separated `X`: fibre products with the orbit

The fibre product `O ×_X T` is a scheme, quasi-compact over an affine `T`, not affine in general.
No quasi-affineness (Zariski's Main Theorem) is needed: only a finite cover by affine opens, and, at a
generic point of the image, a chart over which the fibre product is affine (`exists_chart_affine_pull`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AlgMag.ChartQSL11

open ChartMain AlgMag.ChartPoint

section Spec

/-- The closure of the image of a closed set under a ring map consists of specializations. -/
lemma exists_le_of_mem_closure {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
    (Z : Set (PrimeSpectrum C)) (hZ : IsClosed Z) (y : PrimeSpectrum A)
    (hy : y ∈ closure (PrimeSpectrum.comap φ '' Z)) :
    ∃ z ∈ Z, PrimeSpectrum.comap φ z ≤ y := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  have hle : J.comap φ ≤ y.asIdeal := by
    have hcl : y ∈ PrimeSpectrum.zeroLocus ((J.comap φ : Ideal A) : Set A) := by
      refine closure_minimal ?_ (PrimeSpectrum.isClosed_zeroLocus _) hy
      rintro _ ⟨z, hz, rfl⟩
      rw [hJ] at hz
      exact fun a ha => hz ha
    exact hcl
  obtain ⟨p, hp, hpy⟩ := Ideal.exists_minimalPrimes_le hle
  obtain ⟨P, hP, hJP, hPc⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ p hp
  refine ⟨⟨P, hP⟩, ?_, ?_⟩
  · rw [hJ]
    exact hJP
  · change P.comap φ ≤ y.asIdeal
    rw [hPc]
    exact hpy

/-- Affine form: a point in the closure of the image of a closed subset has a generization in the
image. -/
lemma exists_specializes_of_mem_closure {V T : Scheme.{u}} [IsAffine V] [IsAffine T] (f : V ⟶ T)
    (Z : Set V) (hZ : IsClosed Z) (t : T) (ht : t ∈ closure (f '' Z)) :
    ∃ z ∈ Z, f z ⤳ t := by
  let φ : Γ(T, ⊤) →+* Γ(V, ⊤) := f.appTop.hom
  have hnat : ∀ x : V, T.isoSpec.hom (f x) = PrimeSpectrum.comap φ (V.isoSpec.hom x) := by
    intro x
    have := Scheme.isoSpec_hom_naturality f
    have e := congrArg (fun k : V ⟶ _ => k x) this
    simp only [Scheme.Hom.comp_apply] at e
    exact e.symm

  let Z' : Set (PrimeSpectrum Γ(V, ⊤)) := V.isoSpec.hom '' Z
  have hZ' : IsClosed Z' := (V.isoSpec.hom.homeomorph).isClosedMap _ hZ
  have ht' : T.isoSpec.hom t ∈ closure (PrimeSpectrum.comap φ '' Z') := by
    have hc : Continuous (T.isoSpec.hom : T → _) := T.isoSpec.hom.continuous
    refine closure_mono ?_ (map_mem_closure hc ht (Set.mapsTo_image _ _))
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨V.isoSpec.hom x, ⟨x, hx, rfl⟩, (hnat x).symm⟩
  obtain ⟨z', ⟨z, hz, rfl⟩, hle⟩ := exists_le_of_mem_closure φ Z' hZ' _ ht'
  refine ⟨z, hz, ?_⟩
  rw [← hnat] at hle
  have hs : T.isoSpec.hom (f z) ⤳ T.isoSpec.hom t := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  exact ((T.isoSpec.hom.homeomorph).isInducing.specializes_iff).1 hs

end Spec

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `exists_pull` with no separatedness: the fibre product of two points of an algebraic space. -/
theorem exists_pull_qs (hX : IsAlgebraicSpace B S hS X) {Z U : BigFppfOver B S hS}
    (u : yoneda.obj U ⟶ X) (τ : yoneda.obj Z ⟶ X) :
    ∃ (E : BigFppfOver B S hS) (e₂ : E ⟶ U) (e₁ : E ⟶ Z),
      IsPullback (yoneda.map e₂) (yoneda.map e₁) u τ := by
  have hrep : yoneda.relativelyRepresentable u := hX.diagonal_representable.of_diag u
  obtain ⟨e₂, he₂⟩ := yoneda.map_surjective (hrep.fst τ)
  refine ⟨hrep.pullback τ, e₂, hrep.snd τ, ?_⟩
  rw [he₂]
  exact hrep.isPullback τ

variable {O : BigFppfOver B S hS}

/-- `O → X` is quasi-compact, `O` affine and `X` quasi-separated (Stacks 03KS). -/
theorem isQuasiCompact_of_affine [IsAffine S] [IsAffine ((SCH).obj O)] (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (toBase X)) (o : yoneda.obj O ⟶ X) :
    Space.IsQuasiCompact B S hS o := by
  have hterm : IsTerminal (yoneda.obj (siteTop (B := B) (S := S) (hS := hS))) :=
    Limits.IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal
  refine Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS o (toBase X)
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) ?_ hqs
  have e : o ≫ toBase X = yoneda.map (toTop O) := hterm.hom_ext _ _
  rw [e]
  refine Space.isQuasiCompact_of_isAffineHom' B S hS _ (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS _) ?_
  intro Z g
  obtain ⟨g', rfl⟩ := yoneda.map_surjective g
  haveI : IsAffine ((SCH).obj ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) :=
    preservesPullbacks_bigFppfOverToScheme B S hS
  have sq := IsPullback.of_hasPullback (toTop O) g'
  have hs := sq.map (SCH)
  haveI : IsAffineHom ((SCH).map (toTop O)) := isAffineHom_of_isAffine _
  have h1 : IsAffineHom ((SCH).map (pullback.snd (toTop O) g')) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hs inferInstance
  refine ⟨⟨pullback (toTop O) g', isAffine_of_isAffineHom ((SCH).map (pullback.snd (toTop O) g'))⟩,
    yoneda.map (pullback.fst (toTop O) g'), pullback.snd (toTop O) g', sq.map yoneda⟩

/-- A fibre product of `o : O → X`, `o` quasi-compact, with a point on an affine `T`, is quasi-compact. -/
theorem compactSpace_of_pull (hX : IsAlgebraicSpace B S hS X) {o : yoneda.obj O ⟶ X}
    (hqc : Space.IsQuasiCompact B S hS o) {T W : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    {g : yoneda.obj T ⟶ X} {p : W ⟶ O} {w : W ⟶ T}
    (sq : IsPullback (yoneda.map p) (yoneda.map w) o g) : CompactSpace ((SCH).obj W) := by
  exact Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    ((hqc (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      (Space.isQuasiCompactSpace_yoneda_obj B S hS inferInstance) g).of_iso B S hS
      sq.flip.isoPullback.symm)

/-- A finite cover by affine opens. -/
lemma exists_finite_affine_cover (W : Scheme.{u}) [CompactSpace W] :
    ∃ (t : Finset W) (A : t → W.Opens), (∀ i, IsAffineOpen (A i)) ∧ ∀ x : W, ∃ i, x ∈ A i := by
  have hx : ∀ x : W, ∃ A : W.Opens, IsAffineOpen A ∧ x ∈ A := fun x => by
    obtain ⟨A, hA, hm, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨A, hA, hm⟩
  choose A hA hm using hx
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (A x : Set W))
    (fun x => (A x).isOpen.mem_nhds (hm x))
  refine ⟨t, fun i => A i.1, fun i => hA _, fun x => ?_⟩
  have : x ∈ ⋃ y ∈ t, (A y : Set W) := by rw [ht]; trivial
  simp only [Set.mem_iUnion] at this
  obtain ⟨y, hy, hxy⟩ := this
  exact ⟨⟨y, hy⟩, hxy⟩

/-- A function vanishing on the opens of a cover vanishes. -/
lemma eq_zero_of_cover {W : Scheme.{u}} {ι : Type*} (A : ι → W.Opens) (hA : ∀ x : W, ∃ i, x ∈ A i)
    (a : Γ(W, ⊤)) (h : ∀ i, (A i).ι.appTop.hom a = 0) : a = 0 := by
  refine TopCat.Presheaf.section_ext W.sheaf ⊤ a 0 fun x hx => ?_
  obtain ⟨i, hi⟩ := hA x
  let y : (A i).toScheme := ⟨x, hi⟩
  have hinj := (ConcreteCategory.bijective_of_isIso ((A i).ι.stalkMap y)).1
  apply hinj
  have e := Scheme.Hom.germ_stalkMap_apply (A i).ι ⊤ y trivial a
  have e0 := Scheme.Hom.germ_stalkMap_apply (A i).ι ⊤ y trivial 0
  refine e.trans (Eq.trans ?_ e0.symm)
  have h0 := h i
  change ((A i).toScheme.presheaf.germ ⊤ y trivial) ((A i).ι.appTop.hom a) = _
  rw [h0, map_zero, map_zero, map_zero]

end AlgMag.ChartQSL11
