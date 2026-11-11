/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStratCore

/-!
# The generic stabilizer for quasi-separated `X`, from generic closedness

`genericStabilizerAt_of_closedGeneric` reduces `GenericStabilizerAt` to `StabClosedGeneric`: over a
nonempty open of an integral noetherian affine, the stabilizer of a point is a closed subscheme of
`D(M)`. The rest is `exists_stab_subgroup`.
Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.
 For separated `X`: `genericStabilizerAt_of_separated`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartQSStrat

open AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The conclusion of `exists_generic_stabilizer`, from an ideal describing the stabilizer. -/
theorem exists_generic_of_ideal {V : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] [AddMonoid.FG M]
    [IsDomain Γ((SCH).obj V, ⊤)] [IsNoetherianRing Γ((SCH).obj V, ⊤)]
    (act : AAction (fppfO B S hS) M X) (p : X.obj (op V)) (I : Ideal (gRing M V))
    (hI : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V) (h : APt (fppfO B S hS) M (op T)),
      act.smul h (X.map t.op p) = X.map t.op p ↔ ∀ f ∈ I, specRing t h f = 0) :
    ∃ (s : Γ((SCH).obj V, ⊤)) (_ : s ≠ 0) (Z : AddSubgroup M),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ V), IsUnit (((SCH).map t).appTop.hom s) →
        ∀ h : APt (fppfO B S hS) M (op T),
          act.smul h (X.map t.op p) = X.map t.op p ↔
            ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  have h1V : ∀ f ∈ I, specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) f = 0 := by
    refine (hI V (𝟙 V) 1).mp ?_
    exact act.one_smul _
  have h1 : ∀ f ∈ I, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) (FractionRing Γ((SCH).obj V, ⊤)) M 1 f = 0 := by
    intro f hf
    have e : ∀ x : gRing M V, AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) (FractionRing Γ((SCH).obj V, ⊤)) M 1 x =
        algebraMap _ _ (specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) x) := by
      intro x
      induction x using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | single n r =>
        have e' : specRing (𝟙 V) (1 : APt (fppfO B S hS) M (op V)) (AddMonoidAlgebra.single n r) = r := by
          rw [specRing_single]
          change ((SCH).map (𝟙 V)).appTop.hom r * 1 = r
          simp
        rw [e', AddMonoidAlgebra.lift_single, Algebra.smul_def, MonoidHom.one_apply, mul_one]
    rw [e, h1V f hf, map_zero]
  obtain ⟨s, hs, Z, hZ⟩ := exists_stab_subgroup I h1
    (fun A _ _ g h hg hh => hmul_of_stabIdeal act p I hI A g h hg hh)
  refine ⟨s, hs, Z, fun T t hu h => ?_⟩
  letI : Algebra Γ((SCH).obj V, ⊤) Γ((SCH).obj T, ⊤) := ((SCH).map t).appTop.hom.toAlgebra
  have e : ∀ x : gRing M V, specRing t h x = AddMonoidAlgebra.lift Γ((SCH).obj V, ⊤) Γ((SCH).obj T, ⊤) M h x := by
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single n r =>
      refine Eq.trans ?_ (AddMonoidAlgebra.lift_single _ _ _).symm
      rw [specRing_single, Algebra.smul_def]
      rfl
  rw [hI T t h]
  simp only [e]
  exact hZ _ hu h


/-- **Named hypothesis**, at `act`: over a nonempty affine integral noetherian open `W` of `V`, the
stabilizer of `p` is closed in `D(M)_W`. It implies the generic stabilizer statement. -/
def StabClosedGeneric (act : AAction (fppfO B S hS) M X) : Prop :=
  ∀ (V : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj V)) (_ : IsDomain Γ((SCH).obj V, ⊤))
    (_ : IsNoetherianRing Γ((SCH).obj V, ⊤)) (p : X.obj (op V))
    (_ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) (yonedaEquiv.symm p)),
    ∃ (W : BigFppfOver B S hS) (ι : W ⟶ V) (_ : AlgebraicGeometry.IsOpenImmersion ((SCH).map ι))
      (_ : IsAffine ((SCH).obj W)) (_ : IsDomain Γ((SCH).obj W, ⊤))
      (_ : IsNoetherianRing Γ((SCH).obj W, ⊤)) (I : Ideal (gRing M W)),
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ W) (h : APt (fppfO B S hS) M (op T)),
        act.smul h (X.map t.op (X.map ι.op p)) = X.map t.op (X.map ι.op p) ↔
          ∀ f ∈ I, specRing t h f = 0

/-- **The generic stabilizer, from generic closedness.** -/
theorem genericStabilizerAt_of_closedGeneric [AddMonoid.FG M] (act : AAction (fppfO B S hS) M X)
    (hc : StabClosedGeneric act) : GenericStabilizerAt act := by
  intro V hVa hVd hVn p hpe
  obtain ⟨W, ι, hι, hWa, hWd, hWn, I, hI⟩ := hc V hVa hVd hVn p hpe
  obtain ⟨s', hs', Z, hZ⟩ := exists_generic_of_ideal act (X.map ι.op p) I hI
  -- `D(s')` of `W`, as an open of `V`, contains a basic open
  have hVred : IsReduced ((SCH).obj V) := by
    haveI : IsReduced Γ((SCH).obj V, ⊤) := inferInstance
    exact isReduced_of_isAffine_isReduced _
  have hWred : IsReduced ((SCH).obj W) := by
    haveI : IsReduced Γ((SCH).obj W, ⊤) := inferInstance
    exact isReduced_of_isAffine_isReduced _
  have hne : ((SCH).obj W).basicOpen s' ≠ ⊥ := fun e =>
    hs' ((AlgebraicGeometry.basicOpen_eq_bot_iff s').1 e)
  obtain ⟨w, hw⟩ := TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.1 hne
  let i := (SCH).map ι
  let O : ((SCH).obj V).Opens := i ''ᵁ ((SCH).obj W).basicOpen s'
  have hv : i w ∈ O := ⟨w, hw, rfl⟩
  obtain ⟨s, hsO, hvs⟩ := (isAffineOpen_top ((SCH).obj V)).exists_basicOpen_le
    (V := O) ⟨i w, hv⟩ trivial
  refine ⟨s, ?_, Z, fun T t hu h => ?_⟩
  · rintro rfl
    have : i w ∈ ((SCH).obj V).basicOpen (0 : Γ((SCH).obj V, ⊤)) := hvs
    simp at this
  have hmem : ∀ y : (SCH).obj T, (SCH).map t y ∈ ((SCH).obj V).basicOpen s := by
    intro y
    have e := Scheme.preimage_basicOpen ((SCH).map t) s
    have hy : y ∈ ((SCH).obj T).basicOpen (((SCH).map t).appTop.hom s) :=
      (Scheme.mem_basicOpen_top _ _ y).2 (hu.map _)
    exact (SetLike.ext_iff.1 e y).2 hy
  -- `t` factors through `W`
  have hrange : Set.range ((SCH).map t) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨w', -, e⟩ := hsO (hmem y)
    exact ⟨w', e⟩
  let l : (SCH).obj T ⟶ (SCH).obj W := AlgebraicGeometry.IsOpenImmersion.lift i ((SCH).map t) hrange
  have hl : l ≫ i = (SCH).map t := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let t' : T ⟶ W := Over.homMk (ObjectProperty.homMk l) (by
    apply B.inclusion.map_injective
    have e1 : i ≫ structMap V = structMap W := congrArg (B.inclusion.map) (Over.w ι)
    have e2 : (SCH).map t ≫ structMap V = structMap T := congrArg (B.inclusion.map) (Over.w t)
    change l ≫ structMap W = structMap T
    rw [← e1, ← Category.assoc, hl, e2])
  have ht' : t' ≫ ι = t := (SCH).map_injective (by rw [Functor.map_comp]; exact hl)
  have hu' : IsUnit (((SCH).map t').appTop.hom s') := by
    refine ((SCH).obj T).toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    have e := Scheme.preimage_basicOpen ((SCH).map t') s'
    refine (SetLike.ext_iff.1 e y).1 ?_
    obtain ⟨w', hw', e'⟩ := hsO (hmem y)
    have hlt : i ((SCH).map t' y) = (SCH).map t y := by rw [← hl]; rfl
    have hww : w' = (SCH).map t' y := i.isOpenEmbedding.injective (e'.trans hlt.symm)
    rw [hww] at hw'
    exact hw'
  have := hZ T t' hu' h
  rw [← Functor.map_comp_apply, ← op_comp, ht'] at this
  exact this

/-- For separated `X`, `exists_generic_stabilizer` is `GenericStabilizerAt`. -/
theorem genericStabilizerAt_of_separated [AddMonoid.FG M] (act : AAction (fppfO B S hS) M X)
    (hsep : Space.IsSeparatedOver B S hS X) : GenericStabilizerAt act :=
  fun _ _ _ _ p _ => exists_generic_stabilizer act hsep p

end AlgMag.ChartQSStrat

#print axioms AlgMag.ChartQSStrat.genericStabilizerAt_of_closedGeneric
