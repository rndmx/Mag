/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumQS
import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms

/-!
# An affine open of the quotient (affine stratum lemma, step 6)

The quotient is quasi-separated if it maps to an affine scheme quasi-separatedly, so it is decent, and
it has a dense schematic open (Stacks 086U); take an affine open of that.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The diagonal of `Y → G` is a base change of the diagonal of `X → G'`, for a monomorphism
`Y → X` over `G → G'`. -/
theorem isPullback_diagonal_of_mono {C : Type*} [Category C] [HasPullbacks C]
    {Y X G G' : C} (ι : Y ⟶ X) [Mono ι] (r : Y ⟶ G) (e : X ⟶ G') (a : G ⟶ G') (h : r ≫ a = ι ≫ e) :
    IsPullback ι (pullback.diagonal r) (pullback.diagonal e)
      (pullback.lift (pullback.fst r r ≫ ι) (pullback.snd r r ≫ ι)
        (by simp only [Category.assoc, ← h]; rw [← Category.assoc, pullback.condition,
          Category.assoc]) : pullback r r ⟶ pullback e e) := by
  set k : pullback r r ⟶ pullback e e := pullback.lift (pullback.fst r r ≫ ι) (pullback.snd r r ≫ ι)
    (by simp only [Category.assoc, ← h]; rw [← Category.assoc, pullback.condition,
      Category.assoc]) with hk
  have k1 : k ≫ pullback.fst e e = pullback.fst r r ≫ ι := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd e e = pullback.snd r r ≫ ι := pullback.lift_snd _ _ _
  have w : ι ≫ pullback.diagonal e = pullback.diagonal r ≫ k := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1]
      rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2]
      rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]
  refine IsPullback.of_isLimit' ⟨w⟩ ?_
  have eqs : ∀ c : PullbackCone (pullback.diagonal e) k,
      c.fst = c.snd ≫ pullback.fst r r ≫ ι ∧ c.fst = c.snd ≫ pullback.snd r r ≫ ι := by
    intro c
    have q := c.condition
    constructor
    · have e1 := congrArg (· ≫ pullback.fst e e) q
      simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1] using e1
    · have e1 := congrArg (· ≫ pullback.snd e e) q
      simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2] using e1
  have same : ∀ c : PullbackCone (pullback.diagonal e) k,
      c.snd ≫ pullback.fst r r = c.snd ≫ pullback.snd r r := fun c => by
    rw [← cancel_mono ι, Category.assoc, Category.assoc, ← (eqs c).1, ← (eqs c).2]
  refine PullbackCone.IsLimit.mk _ (fun c => c.snd ≫ pullback.fst r r) ?_ ?_ ?_
  · intro c
    rw [Category.assoc, ← (eqs c).1]
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, same c]
  · intro c m h1 h2
    rw [← h2, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- A map from an open subspace of a quasi-separated `X`, to anything over the base, is
quasi-separated. -/
theorem isQuasiSeparated_of_mono {X Y G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : Y ⟶ X) [Mono ι]
    (r : Y ⟶ G) (hsep : Space.IsSeparatedOver B S hS X) :
    Space.IsQuasiSeparated B S hS r := by
  have he : Space.IsQuasiSeparated B S hS (terminal.from X) :=
    Space.isQuasiSeparated_of_isSeparated B S hS
      ((Space.isSeparatedOver_iff_isSeparated_of_isTerminal B S hS terminalIsTerminal
        (terminal.from X)).1 hsep)
  exact Space.isQuasiCompact_of_isPullback B S hS
    (isPullback_diagonal_of_mono ι r (terminal.from X) (terminal.from G) (terminal.hom_ext _ _)) he

attribute [local instance] Space.pointTopology in
/-- **Affine stratum lemma, step 6**: a nonempty absolutely quasi-separated algebraic space has a nonempty affine
open. -/
theorem exists_affine_open_of_absQS {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : IsAlgebraicSpace B S hS Q)
    (hqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Q)
    (hne : Nonempty (Space.points B S hS Q)) :
    ∃ (D : BigFppfOver B S hS) (ξ : yoneda.obj D ⟶ Q), IsAffine ((SCH).obj D) ∧
      Nonempty ((SCH).obj D) ∧ Space.IsOpenImmersion B S hS ξ := by
  obtain ⟨G, ⟨hGa, hGo⟩, hrep, hd⟩ :=
    Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS hQ
      (Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B S hS Q hQ hqs)
  have hpt := hd.nonempty
  let A₀ := G.toFunctor.reprX
  let e : yoneda.obj A₀ ≅ G.toFunctor := G.toFunctor.reprW
  have hA₀ : Nonempty ((SCH).obj A₀) := by
    obtain ⟨z⟩ := hpt
    induction z using Quot.ind with
    | mk p =>
      let y : yoneda.obj A₀ ⟶ G.toFunctor := e.hom
      let t : Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS) ⟶ A₀ :=
        yonedaEquiv.symm p.value ≫ e.inv |> yoneda.preimage
      have hk : Nonempty (Spec (.of p.carrier)) := inferInstance
      obtain ⟨w⟩ := hk
      exact ⟨(SCH).map t w⟩
  obtain ⟨z⟩ := hA₀
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := (SCH).obj A₀)
    (x := z) (U := ⊤) trivial
  let D := Space.opensObject B S hS A₀ V
  have hDaff : IsAffine ((SCH).obj D) := hV
  have hDne : Nonempty ((SCH).obj D) := ⟨⟨z, hz⟩⟩
  have hi : AlgebraicGeometry.IsOpenImmersion ((SCH).map (Space.opensObjectι B S hS A₀ V)) := by
    change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj A₀) V)
    infer_instance
  have h1 : Space.IsOpenImmersion B S hS (yoneda.map (Space.opensObjectι B S hS A₀ V)) := by
    have := Space.inverseImage_isStableUnderBaseChange B S hS
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
    exact MorphismProperty.relative_map (F := yoneda) hi
  have h2 : Space.IsOpenImmersion B S hS (e.hom ≫ G.ι) :=
    MorphismProperty.RespectsIso.precomp _ e.hom _ hGo
  exact ⟨D, yoneda.map (Space.opensObjectι B S hS A₀ V) ≫ e.hom ≫ G.ι, hDaff, hDne,
    Space.isOpenImmersion_comp B S hS _ _ h1 h2⟩

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.isQuasiSeparated_of_mono
#print axioms AlgMag.ChartStratum.exists_affine_open_of_absQS
