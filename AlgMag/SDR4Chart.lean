/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3AsmFinal
import AlgMag.SDR3OrbitStep
import AlgMag.SDR3CoactMain

/-!
# Lemma D, final bridge: the affine chart, `W' → W` is étale and separated

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, remark on `W'`. `U` is replaced by
an affine open around the image of a point, and `W' = W ×_X U` is separated over `W`, since `W' → W × U` is a monomorphism
on objects of the site, by the closed subscheme `E` where the two projections to `U` agree.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- `W' → W` is separated when `W' → W × U₁` is injective on points of the site, for `U₁` affine. -/
theorem SDR4_sep {W' W U₁ : BigFppfOver B S hS} [IsAffine ((SCH).obj U₁)] (p : W' ⟶ W) (s : W' ⟶ U₁)
    (huniq : ∀ {T : BigFppfOver B S hS} (l₁ l₂ : T ⟶ W'), l₁ ≫ p = l₂ ≫ p → l₁ ≫ s = l₂ ≫ s → l₁ = l₂) :
    IsSeparated ((SCH).map p) := by
  let P : BigFppfOver B S hS := Limits.pullback p p
  have hpb := (IsPullback.of_hasPullback p p).map (SCH)
  let A := hpb.isoPullback
  let Y := (SCH).obj U₁
  let ξ : (SCH).obj P ⟶ Limits.pullback (terminal.from Y) (terminal.from Y) :=
    pullback.lift ((SCH).map (pullback.fst p p) ≫ (SCH).map s) ((SCH).map (pullback.snd p p) ≫ (SCH).map s)
      (terminal.hom_ext _ _)
  let Δ := pullback.diagonal (terminal.from Y)
  let E := Limits.pullback ξ Δ
  let e : E ⟶ (SCH).obj P := pullback.fst ξ Δ
  have : IsClosedImmersion Δ := inferInstance
  have hec : IsClosedImmersion e := inferInstance
  have hC : B.Contains E := B.contains_of_mono e P.left.2
  let Eo : BigFppfOver B S hS := siteObject B S hS hC (e ≫ P.hom.hom)
  let eo : Eo ⟶ P := overHom e rfl
  have h12 : eo ≫ pullback.fst p p = eo ≫ pullback.snd p p := by
    refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition]
    · refine toScheme_map_injective ?_
      simp only [Functor.map_comp]
      have hc : e ≫ ξ = pullback.snd ξ Δ ≫ Δ := pullback.condition
      have h1 := congrArg (· ≫ pullback.fst (terminal.from Y) (terminal.from Y)) hc
      have h2 := congrArg (· ≫ pullback.snd (terminal.from Y) (terminal.from Y)) hc
      simp only [Category.assoc, ξ, Δ, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd,
        Category.comp_id] at h1 h2
      exact h1.trans h2.symm
  have h12' : e ≫ (SCH).map (pullback.fst p p) = e ≫ (SCH).map (pullback.snd p p) := by
    have := congrArg (SCH).map h12
    rw [Functor.map_comp, Functor.map_comp] at this
    exact this
  have hrange : Set.range (pullback.diagonal ((SCH).map p)) = A.hom '' Set.range e := by
    apply Set.Subset.antisymm
    · rintro _ ⟨w, rfl⟩
      let η : (SCH).obj W' ⟶ (SCH).obj P := pullback.diagonal ((SCH).map p) ≫ A.inv
      have hη1 : η ≫ (SCH).map (pullback.fst p p) = 𝟙 _ := by
        simp [η, A, IsPullback.isoPullback_inv_fst]
      have hη2 : η ≫ (SCH).map (pullback.snd p p) = 𝟙 _ := by
        simp [η, A, IsPullback.isoPullback_inv_snd]
      have hηξ : η ≫ ξ = (SCH).map s ≫ Δ := by
        apply pullback.hom_ext
        · simp only [Category.assoc, ξ, Δ, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
          rw [← Category.assoc, hη1, Category.id_comp]
        · simp only [Category.assoc, ξ, Δ, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
          rw [← Category.assoc, hη2, Category.id_comp]
      let η' : (SCH).obj W' ⟶ E := pullback.lift η ((SCH).map s) hηξ
      have hη' : η' ≫ e = η := pullback.lift_fst _ _ _
      refine ⟨e (η' w), ⟨_, rfl⟩, ?_⟩
      have h3 : (η' ≫ e ≫ A.hom) w = pullback.diagonal ((SCH).map p) w := by
        rw [← Category.assoc, hη']
        simp [η]
      exact h3
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨(e ≫ (SCH).map (pullback.fst p p)) z, ?_⟩
      have h4 : (e ≫ (SCH).map (pullback.fst p p)) ≫ pullback.diagonal ((SCH).map p) = e ≫ A.hom := by
        apply pullback.hom_ext
        · simp [A]
        · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, A, IsPullback.isoPullback_hom_snd]
          exact h12'
      exact congrArg (fun m : E ⟶ _ => m z) h4
  have hcl : IsClosed (Set.range (pullback.diagonal ((SCH).map p))) := by
    rw [hrange]
    exact (Scheme.homeoOfIso A).isClosedMap _ e.isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

section OpenObj

/-- An open of an object of the site, as an object of the site. -/
noncomputable def SDR4_openObj (Z : BigFppfOver B S hS) (O : ((SCH).obj Z).Opens) : BigFppfOver B S hS :=
  siteObject B S hS (B.contains_of_mono O.ι Z.left.2) (O.ι ≫ Z.hom.hom)

/-- The inclusion of an open object. -/
noncomputable def SDR4_openι (Z : BigFppfOver B S hS) (O : ((SCH).obj Z).Opens) : SDR4_openObj Z O ⟶ Z :=
  overHom O.ι rfl

instance SDR4_openι_imm (Z : BigFppfOver B S hS) (O : ((SCH).obj Z).Opens) :
    IsOpenImmersion ((SCH).map (SDR4_openι Z O)) := inferInstanceAs (IsOpenImmersion O.ι)

lemma SDR4_openι_range (Z : BigFppfOver B S hS) (O : ((SCH).obj Z).Opens) :
    Set.range ((SCH).map (SDR4_openι Z O)) = O := O.range_ι

/-- Open immersions of the site cancel. -/
lemma SDR4_cancel {V Z T : BigFppfOver B S hS} (k : V ⟶ Z) [hk : IsOpenImmersion ((SCH).map k)] {a b : T ⟶ V}
    (h : a ≫ k = b ≫ k) : a = b := by
  refine toScheme_map_injective ?_
  have h' := congrArg (SCH).map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  exact (cancel_mono ((SCH).map k)).1 h'

/-- Lifting along an open immersion of the site. -/
lemma SDR4_lift {V Z T : BigFppfOver B S hS} (k : V ⟶ Z) [hk : IsOpenImmersion ((SCH).map k)] (q : T ⟶ Z)
    (hq : Set.range ((SCH).map q) ⊆ Set.range ((SCH).map k)) : ∃ l : T ⟶ V, l ≫ k = q := by
  have h1 : IsOpenImmersion.lift ((SCH).map k) ((SCH).map q) hq ≫ (SCH).map k = (SCH).map q :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨overHom (IsOpenImmersion.lift ((SCH).map k) ((SCH).map q) hq) ?_, toScheme_map_injective ?_⟩
  · have h2 : (SCH).map k ≫ Z.hom.hom = V.hom.hom := site_w k
    have h3 : (SCH).map q ≫ Z.hom.hom = T.hom.hom := site_w q
    rw [← h2, ← Category.assoc, h1, h3]
  · rw [Functor.map_comp, map_overHom]
    exact h1

end OpenObj

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `W' = W ×_X U₁`, for `U₁` an affine open of the atlas `U` around a given point `y`, is étale and separated over `W`. -/
theorem SDR4_chart {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    {W : BigFppfOver B S hS} (x : X.obj (op W)) (y : (SCH).obj U) :
    ∃ (U₁ : BigFppfOver B S hS) (_ : IsAffine ((SCH).obj U₁)) (i₁ : U₁ ⟶ U) (_ : IsOpenImmersion ((SCH).map i₁))
      (W' : BigFppfOver B S hS) (p : W' ⟶ W) (s : W' ⟶ U₁), y ∈ Set.range ((SCH).map i₁) ∧
      Etale ((SCH).map p) ∧ IsSeparated ((SCH).map p) ∧ f.app (op W') (s ≫ i₁) = X.map p.op x ∧
      ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U₁), X.map a.op x = f.app (op T) (b ≫ i₁) →
        ∃! l : T ⟶ W', l ≫ p = a ∧ l ≫ s = b := by
  obtain ⟨W₀, p₀, s₀, het, hps, hu⟩ := SDLocS_chart f hf x
  obtain ⟨O, hO, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := (SCH).obj U) (x := y) (U := ⊤) trivial
  let U₁ := SDR4_openObj U O
  let i₁ : U₁ ⟶ U := SDR4_openι U O
  have hU₁ : IsAffine ((SCH).obj U₁) := hO
  let Q : ((SCH).obj W₀).Opens := (SCH).map s₀ ⁻¹ᵁ O
  let W' := SDR4_openObj W₀ Q
  let k : W' ⟶ W₀ := SDR4_openι W₀ Q
  have hri : Set.range ((SCH).map i₁) = O := SDR4_openι_range U O
  have hrk : Set.range ((SCH).map k) = Q := SDR4_openι_range W₀ Q
  obtain ⟨s, hs⟩ := SDR4_lift i₁ (k ≫ s₀) (by
    rw [hri]
    rintro _ ⟨z, rfl⟩
    have : (SCH).map k z ∈ Set.range ((SCH).map k) := ⟨z, rfl⟩
    rw [hrk] at this
    rw [Functor.map_comp]
    exact this)
  have huW : ∀ {T : BigFppfOver B S hS} (a : T ⟶ W) (b : T ⟶ U₁), X.map a.op x = f.app (op T) (b ≫ i₁) →
      ∃! l : T ⟶ W', l ≫ (k ≫ p₀) = a ∧ l ≫ s = b := by
    intro T a b hab
    obtain ⟨l₀, ⟨h1, h2⟩, huq⟩ := hu a (b ≫ i₁) hab
    obtain ⟨l, hl⟩ := SDR4_lift k l₀ (by
      rw [hrk]
      rintro _ ⟨z, rfl⟩
      change (SCH).map s₀ ((SCH).map l₀ z) ∈ O
      have e : (SCH).map l₀ ≫ (SCH).map s₀ = (SCH).map b ≫ (SCH).map i₁ := by
        rw [← Functor.map_comp, ← Functor.map_comp, h2]
      have e2 : (SCH).map s₀ ((SCH).map l₀ z) = (SCH).map i₁ ((SCH).map b z) :=
        congrArg (fun m : (SCH).obj T ⟶ (SCH).obj U => m z) e
      rw [e2, ← SetLike.mem_coe, ← hri]
      exact ⟨_, rfl⟩)
    refine ⟨l, ⟨by rw [← Category.assoc, hl, h1], SDR4_cancel i₁ ?_⟩, ?_⟩
    · rw [Category.assoc, hs, ← Category.assoc, hl, h2]
    · rintro l' ⟨h1', h2'⟩
      refine SDR4_cancel k ?_
      rw [hl]
      refine huq _ ⟨by rw [Category.assoc, h1'], ?_⟩
      rw [Category.assoc, ← hs, ← Category.assoc, h2']
  have hfs : f.app (op W') (s ≫ i₁) = X.map (k ≫ p₀).op x := by
    rw [hs, op_comp, Functor.map_comp_apply, ← hps]
    exact NatTrans.naturality_apply f k.op s₀
  refine ⟨U₁, hU₁, i₁, inferInstance, W', k ≫ p₀, s, ?_, ?_, ?_, hfs, huW⟩
  · rw [hri]; exact hy
  · rw [Functor.map_comp]
    have : Etale ((SCH).map p₀) := het
    infer_instance
  · refine SDR4_sep _ s ?_
    intro T l₁ l₂ h1 h2
    obtain ⟨l, -, huq⟩ := huW (l₁ ≫ k ≫ p₀) (l₁ ≫ s) (by
      have h := NatTrans.naturality_apply f l₁.op (s ≫ i₁ : W' ⟶ U)
      rw [hfs] at h
      rw [Category.assoc]
      refine Eq.trans ?_ h.symm
      rw [← Functor.map_comp_apply, ← op_comp])
    rw [huq l₁ ⟨rfl, rfl⟩, huq l₂ ⟨h1.symm, h2.symm⟩]

end AlgMag.SD
