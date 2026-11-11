/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSIndInst
import AlgMag.ChartMain

/-!
# Lemma 4.3 for `X` quasi-separated: the charts

`DeligneQS.HasCharts X` from quasi-compactness of `Z ×_X V` (`PullbacksQC`), `S` affine: an affine étale
surjective cover `E` of `Z ×_X V`. Since `Z ×_X V → Z ×_S V` is a monomorphism and `Z ×_S V` is affine,
`W ×_(Z ×_X V) E = W ×_(Z ×_S V) E` is affine for `W` affine.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `Z ×_X V` is quasi-compact for `Z`, `V` affine and `V → X` étale: what quasi-separatedness of `X` gives. -/
def PullbacksQC (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (φ : yoneda.obj V ⟶ X)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (Z : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] (t : yoneda.obj Z ⟶ X),
    Space.IsQuasiCompactSpace B S hS (yoneda.obj (he.rep.pullback t))

set_option maxHeartbeats 4000000 in
/-- **`PullbacksQC`** for `X` quasi-separated, `S` affine: `Z ×_X V` is the pullback of the diagonal of `X` along
the affine `Z ×_S V → X ×_S X`. -/
theorem pullbacksQC_of_isQuasiSeparated [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hqs : Space.IsQuasiSeparated B S hS (terminal.from X)) : PullbacksQC X := by
  intro V _ φ he Z _ t
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) := preservesPullbacks_bigFppfOverToScheme B S hS
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  let P := he.rep.pullback t
  let p₁ : P ⟶ Z := he.rep.snd t
  let p₂ : P ⟶ V := yoneda.preimage (he.rep.fst t)
  have hp₂ : yoneda.map p₂ = he.rep.fst t := Functor.map_preimage _ _
  have hsqP : IsPullback (yoneda.map p₂) (yoneda.map p₁) φ t := by
    rw [hp₂]
    exact he.rep.isPullback t
  let tZ : Z ⟶ siteTop := Over.mkIdTerminal.from Z
  let tV : V ⟶ siteTop := Over.mkIdTerminal.from V
  let Q := pullback tZ tV
  have hQ : IsPullback ((SCH).map (pullback.fst tZ tV)) ((SCH).map (pullback.snd tZ tV))
      ((SCH).map tZ) ((SCH).map tV) := (IsPullback.of_hasPullback tZ tV).map (SCH)
  have htV : IsAffineHom ((SCH).map tV) := by
    have e : (SCH).map tV = V.hom.hom := by simpa using site_w tV
    rw [e]
    exact @isAffineHom_of_isAffine _ _ V.hom.hom ‹_› ‹_›
  have hQa : IsAffine ((SCH).obj Q) := by
    have h₁ : IsAffineHom ((SCH).map (pullback.fst tZ tV)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hQ.flip htV
    exact isAffine_of_isAffineHom ((SCH).map (pullback.fst tZ tV))
  let pr₁ : Q ⟶ Z := pullback.fst tZ tV
  let pr₂ : Q ⟶ V := pullback.snd tZ tV
  let m : P ⟶ Q := pullback.lift p₁ p₂ (Over.mkIdTerminal.hom_ext _ _)
  have hm₁ : m ≫ pr₁ = p₁ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pr₂ = p₂ := pullback.lift_snd _ _ _
  let tX := terminal.from X
  let g : yoneda.obj Q ⟶ pullback tX tX :=
    pullback.lift (yoneda.map pr₁ ≫ t) (yoneda.map pr₂ ≫ φ) (terminal.hom_ext _ _)
  let c : yoneda.obj P ⟶ X := yoneda.map p₁ ≫ t
  have hw : c ≫ pullback.diagonal tX = yoneda.map m ≫ g := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, g, pullback.lift_fst, c]
      rw [← Category.assoc (yoneda.map m), ← Functor.map_comp, hm₁]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, g, pullback.lift_snd, c]
      rw [← Category.assoc (yoneda.map m), ← Functor.map_comp, hm₂]
      exact hsqP.w.symm
  have hQy : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) (yoneda.map tZ) (yoneda.map tV) :=
    (IsPullback.of_hasPullback tZ tV).map yoneda
  have hpb : IsPullback (yoneda.map m) c g (pullback.diagonal tX) := by
    have hk : ∀ s : PullbackCone g (pullback.diagonal tX),
        s.fst ≫ yoneda.map pr₁ ≫ t = s.snd ∧ s.fst ≫ yoneda.map pr₂ ≫ φ = s.snd := fun s => by
      have h₁ := congrArg (· ≫ pullback.fst tX tX) s.condition
      have h₂ := congrArg (· ≫ pullback.snd tX tX) s.condition
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
        pullback.lift_fst, pullback.lift_snd] at h₁ h₂
      exact ⟨h₁, h₂⟩
    have hcond : ∀ s : PullbackCone g (pullback.diagonal tX),
        (s.fst ≫ yoneda.map pr₂) ≫ φ = (s.fst ≫ yoneda.map pr₁) ≫ t := fun s => by
      simp only [Category.assoc]
      rw [(hk s).1, (hk s).2]
    refine IsPullback.of_isLimit' ⟨hw.symm⟩ (PullbackCone.IsLimit.mk _
      (fun s => hsqP.lift (s.fst ≫ yoneda.map pr₂) (s.fst ≫ yoneda.map pr₁) (hcond s)) ?_ ?_ ?_)
    · intro s
      apply hQy.hom_ext
      · rw [Category.assoc, ← Functor.map_comp, hm₁]
        exact hsqP.lift_snd _ _ _
      · rw [Category.assoc, ← Functor.map_comp, hm₂]
        exact hsqP.lift_fst _ _ _
    · intro s
      rw [← (hk s).1]
      change _ ≫ yoneda.map p₁ ≫ t = _
      rw [← Category.assoc, hsqP.lift_snd, Category.assoc]
    · intro s n h₁ _
      apply hsqP.hom_ext
      · rw [hsqP.lift_fst, ← h₁, Category.assoc, ← Functor.map_comp, hm₂]
      · rw [hsqP.lift_snd, ← h₁, Category.assoc, ← Functor.map_comp, hm₁]
  have hq := hqs (yoneda.obj Q) (isAlgebraicSpace_yoneda B S hS Q)
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS Q hQa) g
  exact Space.isQuasiCompactSpace_of_iso B S hS hpb.isoPullback.symm hq

set_option maxHeartbeats 4000000 in
/-- **`HasCharts`**, `S` affine. -/
theorem hasCharts_of_pullbacksQC [IsAffine S] (hX : IsAlgebraicSpace B S hS X) (h : PullbacksQC X) :
    HasCharts X := by
  intro V _ φ hs he Z _ τ
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have : PreservesLimitsOfShape WalkingCospan (SCH) := preservesPullbacks_bigFppfOverToScheme B S hS
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  let t : yoneda.obj Z ⟶ X := yonedaEquiv.symm τ
  let P := he.rep.pullback t
  have hPalg : IsAlgebraicSpace B S hS (yoneda.obj P) := isAlgebraicSpace_yoneda B S hS P
  obtain ⟨E, f, hEa, hfs, hfe⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj P) hPalg).1
      (h V φ he Z t)
  haveI : IsAffine ((SCH).obj E) := hEa
  have hfe' := Space.presheaf_etale_of_isEtale B S hS hfe
  let g : E ⟶ P := yoneda.preimage f
  have hg : yoneda.map g = f := Functor.map_preimage _ _
  let p₁ : P ⟶ Z := he.rep.snd t
  let p₂ : P ⟶ V := yoneda.preimage (he.rep.fst t)
  have hp₂ : yoneda.map p₂ = he.rep.fst t := Functor.map_preimage _ _
  have hsqP : IsPullback (yoneda.map p₂) (yoneda.map p₁) φ t := by
    rw [hp₂]
    exact (he.rep.isPullback t)
  have hetP : Etale ((SCH).map p₁) := he.2 _ _ p₁ hsqP
  have hsuP : Surjective ((SCH).map p₁) := hs.2 _ _ p₁ hsqP
  -- `g` is a cover in the sense of `IsCov`, along any base change
  have hcovbc : ∀ {W W' : BigFppfOver B S hS} (l₀ : W ⟶ P) (ρ : W' ⟶ W) (l : W' ⟶ E),
      IsPullback l ρ g l₀ → IsCov ρ := by
    intro W W' l₀ ρ l hpb
    have hy : IsPullback (yoneda.map l) (yoneda.map ρ) f (yoneda.map l₀) := by
      rw [← hg]
      exact hpb.map yoneda
    exact ⟨hfe'.2 _ _ ρ hy, hfs.2 _ _ ρ hy⟩
  have hgcov : IsCov g := hcovbc (𝟙 P) g (𝟙 E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hcov₁ : IsCov p₁ := ⟨hetP, hsuP⟩
  have hcomp : IsCov (g ≫ p₁) := hcov₁.comp hgcov
  haveI := hcomp.1
  haveI := hcomp.2
  -- `Z ×_S V`
  let tZ : Z ⟶ siteTop := Over.mkIdTerminal.from Z
  let tV : V ⟶ siteTop := Over.mkIdTerminal.from V
  let Q := pullback tZ tV
  have hQ : IsPullback ((SCH).map (pullback.fst tZ tV)) ((SCH).map (pullback.snd tZ tV))
      ((SCH).map tZ) ((SCH).map tV) := (IsPullback.of_hasPullback tZ tV).map (SCH)
  have htV : IsAffineHom ((SCH).map tV) := by
    have e : (SCH).map tV = V.hom.hom := by simpa using site_w tV
    rw [e]
    exact @isAffineHom_of_isAffine _ _ V.hom.hom ‹_› ‹_›
  have hQa : IsAffine ((SCH).obj Q) := by
    have h₁ : IsAffineHom ((SCH).map (pullback.fst tZ tV)) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) hQ.flip htV
    exact isAffine_of_isAffineHom ((SCH).map (pullback.fst tZ tV))
  haveI := hQa
  let pair : ∀ {A : BigFppfOver B S hS}, (A ⟶ Z) → (A ⟶ V) → (A ⟶ Q) := fun z v =>
    pullback.lift z v (Over.mkIdTerminal.hom_ext _ _)
  let m : P ⟶ Q := pair p₁ p₂
  have hP_ext : ∀ {A : BigFppfOver B S hS} (a b : A ⟶ P), a ≫ m = b ≫ m → a = b := by
    intro A a b hab
    have h₁ : a ≫ p₁ = b ≫ p₁ := by
      have e : m ≫ pullback.fst tZ tV = p₁ := pullback.lift_fst _ _ _
      have h := congrArg (· ≫ pullback.fst tZ tV) hab
      simp only [Category.assoc] at h
      rwa [e] at h
    have h₂ : a ≫ p₂ = b ≫ p₂ := by
      have e : m ≫ pullback.snd tZ tV = p₂ := pullback.lift_snd _ _ _
      have h := congrArg (· ≫ pullback.snd tZ tV) hab
      simp only [Category.assoc] at h
      rwa [e] at h
    refine he.rep.hom_ext ?_ h₁
    rw [← hp₂, ← Functor.map_comp, ← Functor.map_comp, h₂]
  have hw₀ : φ.app (op P) p₂ = X.map p₁.op τ := by
    have e := congrArg yonedaEquiv hsqP.w
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at e
    refine e.trans ?_
    simp [t]
  have hett : ((SCH).map (g ≫ p₁)).appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).1 hcomp.1
  refine ⟨⟨E, hEa, g ≫ p₁, g ≫ p₂, hett, hcomp.2, ?_, ?_⟩⟩
  · rw [map_yoneda_app, hw₀, ← Functor.map_comp_apply, ← op_comp]
  · intro W _ z v hzv
    have hc : yoneda.map v ≫ φ = yoneda.map z ≫ t := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map, hzv]
      simp [t]
    let l₀ : W ⟶ P := he.rep.lift (yoneda.map v) z hc
    have hl₁ : l₀ ≫ p₁ = z := he.rep.lift_snd _ _ _
    have hl₂ : l₀ ≫ p₂ = v := by
      apply yoneda.map_injective
      rw [Functor.map_comp, hp₂]
      exact he.rep.lift_fst _ _ _
    let a := l₀ ≫ m
    let b := g ≫ m
    have hb : IsAffineHom ((SCH).map b) := isAffineHom_of_isAffine _
    have hpb0 : IsPullback ((SCH).map (pullback.fst a b)) ((SCH).map (pullback.snd a b))
        ((SCH).map a) ((SCH).map b) := (IsPullback.of_hasPullback a b).map (SCH)
    have hWa : IsAffine ((SCH).obj (pullback a b)) := by
      have h₁ : IsAffineHom ((SCH).map (pullback.fst a b)) :=
        MorphismProperty.of_isPullback (P := @IsAffineHom) hpb0.flip hb
      exact isAffine_of_isAffineHom ((SCH).map (pullback.fst a b))
    have hcomm : pullback.snd a b ≫ g = pullback.fst a b ≫ l₀ := hP_ext _ _ (by
      simp only [Category.assoc]
      exact (pullback.condition (f := a) (g := b)).symm)
    have hPB : IsPullback (pullback.snd a b) (pullback.fst a b) g l₀ := by
      refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk _
        (fun s => pullback.lift s.snd s.fst (by
          simp only [a, b, ← Category.assoc, ← s.condition]))
        (fun s => pullback.lift_snd _ _ _) (fun s => pullback.lift_fst _ _ _) ?_)
      intro s c h₁ h₂
      exact pullback.hom_ext (by rw [pullback.lift_fst]; exact h₂) (by rw [pullback.lift_snd]; exact h₁)
    refine ⟨pullback a b, hWa, pullback.fst a b, pullback.snd a b, hcovbc l₀ _ _ hPB, ?_, ?_⟩
    · rw [← Category.assoc, hcomm, Category.assoc, hl₁]
    · rw [← Category.assoc, hcomm, Category.assoc, hl₂]

end AlgMag.ChartMain.DeligneQS

#print axioms AlgMag.ChartMain.DeligneQS.hasCharts_of_pullbacksQC
