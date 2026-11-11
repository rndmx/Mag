/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumAffine
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact

/-!
# Quasi-separatedness of the quotient (affine stratum lemma, step 6)

The base change of the diagonal of `Q = U/R → G` along `U ×_G U → Q ×_G Q` is `R → U ×_G U`. It is
quasi-compact when the source of the relation is, and `U → G` is quasi-separated.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The square `R = U ×_Q U` gives the base change of a diagonal, in any category with pullbacks. -/
theorem isPullback_diagonal_of_kernel {C : Type*} [Category C] [HasPullbacks C]
    {R U Q G : C} {s t : R ⟶ U} {π : U ⟶ Q} {f : Q ⟶ G}
    (h : IsPullback s t π π) :
    IsPullback (s ≫ π)
      (pullback.lift s t (by rw [← Category.assoc, ← Category.assoc, h.w]) : R ⟶ pullback (π ≫ f) (π ≫ f))
      (pullback.diagonal f)
      (pullback.lift (pullback.fst (π ≫ f) (π ≫ f) ≫ π) (pullback.snd (π ≫ f) (π ≫ f) ≫ π)
        (by simp [pullback.condition]) : pullback (π ≫ f) (π ≫ f) ⟶ pullback f f) := by
  set g₀ : R ⟶ pullback (π ≫ f) (π ≫ f) := pullback.lift s t
    (by rw [← Category.assoc, ← Category.assoc, h.w]) with hg₀
  set k : pullback (π ≫ f) (π ≫ f) ⟶ pullback f f :=
    pullback.lift (pullback.fst (π ≫ f) (π ≫ f) ≫ π) (pullback.snd (π ≫ f) (π ≫ f) ≫ π)
      (by simp [pullback.condition]) with hk
  have g1 : g₀ ≫ pullback.fst _ _ = s := pullback.lift_fst _ _ _
  have g2 : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
  have k1 : k ≫ pullback.fst f f = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd f f = pullback.snd _ _ ≫ π := pullback.lift_snd _ _ _
  have w : (s ≫ π) ≫ pullback.diagonal f = g₀ ≫ k := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1]
      rw [← Category.assoc, g1]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2]
      rw [← Category.assoc, g2, h.w]
  refine IsPullback.of_isLimit' ⟨w⟩ ?_
  have eqs : ∀ c : PullbackCone (pullback.diagonal f) k,
      c.fst = c.snd ≫ pullback.fst _ _ ≫ π ∧ c.fst = c.snd ≫ pullback.snd _ _ ≫ π := by
    intro c
    have e := c.condition
    constructor
    · have e1 := congrArg (· ≫ pullback.fst f f) e
      simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, k1] using e1
    · have e1 := congrArg (· ≫ pullback.snd f f) e
      simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, k2] using e1
  have cond : ∀ c : PullbackCone (pullback.diagonal f) k,
      (c.snd ≫ pullback.fst _ _) ≫ π = (c.snd ≫ pullback.snd _ _) ≫ π := fun c => by
    rw [Category.assoc, Category.assoc, ← (eqs c).1, ← (eqs c).2]
  refine PullbackCone.IsLimit.mk _ (fun c => h.lift _ _ (cond c)) ?_ ?_ ?_
  · intro c
    rw [← Category.assoc, h.lift_fst, Category.assoc, ← (eqs c).1]
  · intro c
    apply pullback.hom_ext
    · rw [Category.assoc, g1, h.lift_fst]
    · rw [Category.assoc, g2, h.lift_snd]
  · intro c m h1 h2
    apply h.hom_ext
    · rw [h.lift_fst, ← h2, Category.assoc, g1]
    · rw [h.lift_snd, ← h2, Category.assoc, g2]

/-- **Affine stratum lemma, step 6**: the quotient `U/R → G` is quasi-separated if `U → G` is, and the source of
the relation is quasi-compact. -/
theorem isQuasiSeparated_quotient [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z₀} (j : Space.PreRelation R U)
    (hR : IsAlgebraicSpace B S hS R.left) (hU : IsAlgebraicSpace B S hS U.left)
    (hj : IsEquivalenceRelation j.target j.source)
    (hQ : IsAlgebraicSpace B S hS (Space.quotientSheaf j).obj)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (f : (Space.quotientSheaf j).obj ⟶ G)
    (hsep : Space.IsQuasiSeparated B S hS (Space.toQuotientSheaf j ≫ f))
    (hsrc : Space.IsQuasiCompact B S hS j.source.left) :
    Space.IsQuasiSeparated B S hS f := by
  let π := Space.toQuotientSheaf j
  have hpb : IsPullback j.source.left j.target.left π π :=
    Space.isPullback_toQuotientSheaf j hj hR.isSheaf hU.isSheaf
  have key := isPullback_diagonal_of_kernel (f := f) hpb
  set g₀ : R.left ⟶ pullback (π ≫ f) (π ≫ f) := pullback.lift j.source.left j.target.left
    (by rw [← Category.assoc, ← Category.assoc, hpb.w]) with hg₀
  set c : pullback (π ≫ f) (π ≫ f) ⟶ pullback f f :=
    pullback.lift (pullback.fst (π ≫ f) (π ≫ f) ≫ π) (pullback.snd (π ≫ f) (π ≫ f) ≫ π)
        (by simp [pullback.condition]) with hc
  have hU2 : IsAlgebraicSpace B S hS (pullback (π ≫ f) (π ≫ f)) :=
    isAlgebraicSpace_pullback B S hS _ _ hU hU hG
  have hP : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback B S hS _ _ hQ hQ hG
  -- `R → U ×_G U` is quasi-compact
  have hg₀qc : Space.IsQuasiCompact B S hS g₀ := by
    refine Space.isQuasiCompact_of_comp_of_isQuasiSeparated B S hS g₀
      (pullback.fst (π ≫ f) (π ≫ f)) hR hU ?_ ?_
    · rw [hg₀, pullback.lift_fst]; exact hsrc
    · let cU2 : AlgebraicSpaces B S hS := ⟨_, hU2⟩
      let cU : AlgebraicSpaces B S hS := ⟨_, hU⟩
      let cG : AlgebraicSpaces B S hS := ⟨_, hG⟩
      let a : cU2 ⟶ cU := ObjectProperty.homMk (pullback.fst (π ≫ f) (π ≫ f))
      let b : cU2 ⟶ cU := ObjectProperty.homMk (pullback.snd (π ≫ f) (π ≫ f))
      let v : cU ⟶ cG := ObjectProperty.homMk (π ≫ f)
      have sq : IsPullback b a v v :=
        IsPullback.of_map (ObjectProperty.ι _)
          (ObjectProperty.hom_ext _ (IsPullback.of_hasPullback (π ≫ f) (π ≫ f)).flip.w)
          (IsPullback.of_hasPullback (π ≫ f) (π ≫ f)).flip
      exact (Space.isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq hsep
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hQ hP _ ?_
  intro T hTaff g
  have hloc := Space.isLocallySurjective_toQuotientSheaf j
  have step : ∀ (T' : BigFppfOver B S hS) (ξ : yoneda.obj T' ⟶ (Space.quotientSheaf j).obj),
      ∃ (V : BigFppfOver B S hS) (f' : V ⟶ T') (a : yoneda.obj V ⟶ U.left),
        Flat ((BigFppfOver.toScheme B S hS).map f') ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f') ∧
        Surjective ((BigFppfOver.toScheme B S hS).map f') ∧ a ≫ π = yoneda.map f' ≫ ξ := by
    intro T' ξ
    obtain ⟨V, f', hF, hL, hS', a, ha⟩ := Space.exists_single_fppf_lift_of_isLocallySurjective
      B S hS hU.isSheaf hQ.isSheaf π hloc T' (yonedaEquiv ξ)
    refine ⟨V, f', yonedaEquiv.symm a, hF, hL, hS', ?_⟩
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, yonedaEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using ha
  obtain ⟨V₁, f₁, a₁, hF₁, hL₁, hS₁, ha₁⟩ := step T (g ≫ pullback.fst f f)
  obtain ⟨V₂, f₂, a₂, hF₂, hL₂, hS₂, ha₂⟩ := step V₁ (yoneda.map f₁ ≫ g ≫ pullback.snd f f)
  let A₁ : yoneda.obj V₂ ⟶ U.left := yoneda.map f₂ ≫ a₁
  have hA₁ : A₁ ≫ π = yoneda.map (f₂ ≫ f₁) ≫ g ≫ pullback.fst f f := by
    simp only [A₁, Category.assoc, ha₁, Functor.map_comp]
  have hA₂ : a₂ ≫ π = yoneda.map (f₂ ≫ f₁) ≫ g ≫ pullback.snd f f := by
    rw [ha₂]; simp only [Functor.map_comp, Category.assoc]
  have hcond : A₁ ≫ π ≫ f = a₂ ≫ π ≫ f := by
    rw [← Category.assoc, hA₁, ← Category.assoc a₂, hA₂]
    simp only [Category.assoc, pullback.condition]
  let aV : yoneda.obj V₂ ⟶ pullback (π ≫ f) (π ≫ f) := pullback.lift A₁ a₂ hcond
  have comm : aV ≫ c = yoneda.map (f₂ ≫ f₁) ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst, hA₁]
    · rw [Category.assoc, Category.assoc, hc, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd, hA₂]
  have hpaste : IsPullback (pullback.snd aV g₀ ≫ (j.source.left ≫ π)) (pullback.fst aV g₀)
      (pullback.diagonal f) (yoneda.map (f₂ ≫ f₁) ≫ g) := by
    rw [← comm]
    exact (IsPullback.of_hasPullback aV g₀).flip.paste_horiz key
  have hsq := IsPullback.of_right' hpaste (IsPullback.of_hasPullback g (pullback.diagonal f)).flip
  have hTa := isAlgebraicSpace_yoneda B S hS T
  have hPg : IsAlgebraicSpace B S hS (pullback g (pullback.diagonal f)) :=
    isAlgebraicSpace_pullback B S hS _ _ hTa hQ hP
  have hPV : IsAlgebraicSpace B S hS (pullback aV g₀) :=
    isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS V₂) hR hU2
  have hFf : Flat ((BigFppfOver.toScheme B S hS).map (f₂ ≫ f₁)) := by
    rw [Functor.map_comp]; infer_instance
  have hLf : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (f₂ ≫ f₁)) := by
    rw [Functor.map_comp]; infer_instance
  have hSf : Surjective ((BigFppfOver.toScheme B S hS).map (f₂ ≫ f₁)) := by
    rw [Functor.map_comp]; infer_instance
  have hq : Space.IsQuasiCompact B S hS (pullback.fst g (pullback.diagonal f)) :=
    Space.of_isPullback_yoneda_map_of_fppf B S hS (Space.quasiCompactProperty B S hS) hFf hLf hSf hPg
      (PV := ⟨_, hPV⟩) hsq
      (Space.isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback aV g₀).flip hg₀qc)
  have := hq _ hTa (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS T hTaff) (𝟙 _)
  exact Space.isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 _) _)) this

end AlgMag.ChartStratum

#print axioms AlgMag.ChartStratum.isQuasiSeparated_quotient
