/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBase

/-!
# Algebraic Magnetism, Fact 2.6 (i), the bialgebra `𝒪_S[N]`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). For `U ⊆ S` affine open with `R = Γ(S, U)`:
`𝔸(N)_S ×_S Spec R = Spec R[N]`, the coordinate `X^n` being the pull-back of the universal function.
So `q_* 𝒪_{𝔸(N)_S}(U) = 𝒪_S(U)[N]` (Definition 2.3 (ii) on quasi-compact opens).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.GB

variable (N : Type u) [AddCommMonoid N] (R : CommRingCat.{u})

/-- `Spec R[N]`. -/
abbrev PR : Scheme.{u} := Spec (CommRingCat.of (AddMonoidAlgebra R N))

/-- `Spec R[N] → Spec R`. -/
def piR : PR N R ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom))

variable {S : Scheme.{u}} (s : Spec R ⟶ S)

/-- `Spec R[N]` as a scheme over `S`. -/
abbrev T0PR : Over S := Over.mk (piR N R ≫ s)

/-- The point `n ↦ X^n` of `𝔸(N)` over `Spec R[N]`. -/
def a0PR : Multiplicative N →* Γ(PR N R, ⊤) :=
  ((homSpecEquiv (PR N R) _ (𝟙 _)).hom : _ →+* _).toMonoidHom.comp
    (AddMonoidAlgebra.of R N)

/-- The morphism `Spec R[N] → 𝔸(N)_S`, `X^n ↦ X^n`. -/
def jS : T0PR N R s ⟶ A N S := (pts (T0PR N R s)).symm (a0PR N R)

lemma ptsZ_jS : ptsZ (PR N R) ((jS N R s).left ≫ toAZ N S) = a0PR N R :=
  (pts (T0PR N R s)).apply_symm_apply _

/-- The ring morphism `R[N] → Γ(T, ⊤)` of a morphism `T → Spec R` and a point of `𝔸(N)` over `T`. -/
def rhoPR {T : Scheme.{u}} (x : T ⟶ Spec R) (a : Multiplicative N →* Γ(T, ⊤)) :
    CommRingCat.of (AddMonoidAlgebra R N) ⟶ Γ(T, ⊤) :=
  CommRingCat.ofHom (AddMonoidAlgebra.liftNCRingHom (homSpecEquiv T _ x).hom a
    fun _ _ => Commute.all _ _)

variable {N R} in
lemma rhoPR_single {T : Scheme.{u}} (x : T ⟶ Spec R) (a : Multiplicative N →* Γ(T, ⊤)) (n : N) :
    (rhoPR N R x a).hom (AddMonoidAlgebra.single n 1) = a (Multiplicative.ofAdd n) := by
  simp [rhoPR]

variable {N R} in
lemma rhoPR_zero {T : Scheme.{u}} (x : T ⟶ Spec R) (a : Multiplicative N →* Γ(T, ⊤)) :
    CommRingCat.ofHom AddMonoidAlgebra.singleZeroRingHom ≫ rhoPR N R x a = homSpecEquiv T _ x := by
  ext r
  simp [rhoPR]

variable {N R} in
lemma lift_piR {T : Scheme.{u}} (x : T ⟶ Spec R) (a : Multiplicative N →* Γ(T, ⊤)) :
    (homSpecEquiv T _).symm (rhoPR N R x a) ≫ piR N R = x := by
  apply (homSpecEquiv T _).injective
  rw [piR, homSpecEquiv_map, Equiv.apply_symm_apply, rhoPR_zero]

variable {N R} in
lemma ptsZ_lift {T : Scheme.{u}} (x : T ⟶ Spec R) (a : Multiplicative N →* Γ(T, ⊤)) :
    ptsZ T ((homSpecEquiv T _).symm (rhoPR N R x a) ≫ (jS N R s).left ≫ toAZ N S) = a := by
  rw [ptsZ_comp, ptsZ_jS]
  refine MonoidHom.ext fun n => ?_
  set l := (homSpecEquiv T _).symm (rhoPR N R x a) with hl
  have h := homSpecEquiv_comp l (𝟙 (PR N R))
  rw [Category.comp_id, hl, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun k => k.hom (AddMonoidAlgebra.single (Multiplicative.toAdd n) (1 : R))) h
  rw [rhoPR_single] at h2
  exact h2.symm

/-- `Spec R[N] = 𝔸(N)_S ×_S Spec R`. This is `q_* 𝒪` on the affine `Spec R → S` (Fact 2.6 (i)). -/
theorem isPullback_jS : IsPullback (jS N R s).left (piR N R) (A N S).hom s := by
  refine IsPullback.of_isLimit' ⟨Over.w (jS N R s)⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun c => (homSpecEquiv _ _).symm (rhoPR N R c.snd (ptsZ _ (c.fst ≫ toAZ N S)))) ?_ ?_ ?_
  · intro c
    refine pullback.hom_ext ?_ ?_
    · have e : (homSpecEquiv _ _).symm (rhoPR N R c.snd (ptsZ _ (c.fst ≫ toAZ N S))) ≫ piR N R ≫ s =
          c.fst ≫ (A N S).hom := by
        rw [← Category.assoc, lift_piR]
        exact c.condition.symm
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w (jS N R s))).trans e)
    · refine (Category.assoc _ _ _).trans ?_
      apply (ptsZ _).injective
      exact ptsZ_lift s _ _
  · intro c
    exact lift_piR _ _
  · intro c m h1 h2
    apply (homSpecEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_)
    · have := congrArg (fun k => (homSpecEquiv _ _ k).hom r) h2
      simp only [piR, homSpecEquiv_map] at this
      refine this.trans ?_
      have h3 := congrArg (fun k => k.hom r) (rhoPR_zero (N := N) c.snd (ptsZ _ (c.fst ≫ toAZ N S)))
      exact h3.symm
    · have hp : ptsZ _ (c.fst ≫ toAZ N S) =
          (m.appTop.hom : Γ(PR N R, ⊤) →+* _).toMonoidHom.comp (a0PR N R) := by
        rw [← h1, Category.assoc, ptsZ_comp]
        exact congrArg _ (ptsZ_jS N R s)
      refine Eq.trans ?_ (rhoPR_single _ _ n).symm
      rw [hp]
      have h : homSpecEquiv _ _ m = _ :=
        (congrArg _ (Category.comp_id m).symm).trans (homSpecEquiv_comp m (𝟙 (PR N R)))
      exact congrArg (fun k => k.hom (AddMonoidAlgebra.single n (1 : R))) h

/-- `Spec R[N] → 𝔸(N)_S` is an open immersion when `Spec R → S` is one. -/
instance [IsOpenImmersion s] : IsOpenImmersion (jS N R s).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_jS N R s).flip inferInstance

variable {R} [IsOpenImmersion s]

lemma opensRange_jS : (jS N R s).left.opensRange = (A N S).hom ⁻¹ᵁ s.opensRange := by
  apply TopologicalSpace.Opens.ext
  have e : (jS N R s).left = (isPullback_jS N R s).isoPullback.hom ≫ pullback.fst (A N S).hom s :=
    (IsPullback.isoPullback_hom_fst _).symm
  change Set.range (jS N R s).left = _
  have hi : Set.range (isPullback_jS N R s).isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr fun y => Surjective.surj y
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi, Set.image_univ,
    Scheme.Pullback.range_fst]
  rfl

lemma appLE_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

lemma bijective_appLE {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (V : Y.Opens)
    (hV : j ''ᵁ ⊤ = V) (e : (⊤ : X.Opens) ≤ j ⁻¹ᵁ V) :
    Function.Bijective (j.appLE V ⊤ e).hom := by
  subst hV
  have h : j.appLE (j ''ᵁ ⊤) ⊤ e = (j.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom]
    rfl
  rw [h]
  exact (j.appIso ⊤).commRingCatIsoToRingEquiv.bijective

/-- **Fact 2.6 (i)** and **Definition 2.3 (ii)**, last assertion: for `U ⊆ S` affine open, `q : 𝔸(N)_S → S`:
`q_* 𝒪 (U) = 𝒪_S(U)[N]`, as `𝒪_S(U)`-algebras, the universal function `X^n` going to `X^n`. -/
theorem fact26_i_sections {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ e : Γ((A N S).left, (A N S).hom ⁻¹ᵁ U) ≃+* AddMonoidAlgebra Γ(S, U) N,
      (∀ n : N, e (((A N S).left.presheaf.map (homOfLE le_top).op).hom
          (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n))) = AddMonoidAlgebra.single n 1) ∧
      ∀ r : Γ(S, U), e (((A N S).hom.app U).hom r) = AddMonoidAlgebra.single 0 r := by
  let s := hU.fromSpec
  let j := (jS N Γ(S, U) s).left
  have hq : j ≫ (A N S).hom = piR N Γ(S, U) ≫ s := Over.w (jS N Γ(S, U) s)
  have hle : (⊤ : (PR N Γ(S, U)).Opens) ≤ j ⁻¹ᵁ ((A N S).hom ⁻¹ᵁ U) := by
    have h1 : j ''ᵁ ⊤ = (A N S).hom ⁻¹ᵁ U := by
      rw [Scheme.Hom.image_top_eq_opensRange, opensRange_jS, hU.opensRange_fromSpec]
    rw [← h1, Scheme.Hom.preimage_image_eq]
  have hb := bijective_appLE j _ (by
    rw [Scheme.Hom.image_top_eq_opensRange, opensRange_jS, hU.opensRange_fromSpec]) hle
  let e0 := RingEquiv.ofBijective (j.appLE _ ⊤ hle).hom hb
  let G := Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra Γ(S, U) N))
  refine ⟨e0.trans G.commRingCatIsoToRingEquiv, fun n => ?_, fun r => ?_⟩
  · have h0 : (j.appLE _ ⊤ hle).hom (((A N S).left.presheaf.map (homOfLE le_top).op).hom
        (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n))) =
        j.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)) := by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      rfl
    have h1 : j.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)) =
        a0PR N Γ(S, U) (Multiplicative.ofAdd n) := by
      have := ptsZ_jS N Γ(S, U) s
      rw [ptsZ_comp] at this
      exact DFunLike.congr_fun this _
    change G.hom.hom ((j.appLE _ ⊤ hle).hom _) = _
    rw [h0, h1]
    simp [a0PR, homSpecEquiv, G]
  · have h0 : (j.appLE _ ⊤ hle).hom (((A N S).hom.app U).hom r) =
        (piR N Γ(S, U)).appTop.hom ((Scheme.ΓSpecIso Γ(S, U)).inv.hom r) := by
      have hh : (⊤ : (PR N Γ(S, U)).Opens) ≤ (piR N Γ(S, U)) ⁻¹ᵁ (s ⁻¹ᵁ U) := by
        have : (piR N Γ(S, U) ≫ s) ⁻¹ᵁ U = (j ≫ (A N S).hom) ⁻¹ᵁ U := by rw [hq]
        exact this.symm ▸ hle
      have c1 : ((A N S).hom.app U ≫ j.appLE _ ⊤ hle) =
          s.app U ≫ (piR N Γ(S, U)).appLE (s ⁻¹ᵁ U) ⊤ hh :=
        (Scheme.Hom.comp_appLE j (A N S).hom U ⊤ _).symm.trans
          ((appLE_congr hq _ _ _ _).trans (Scheme.Hom.comp_appLE _ s U ⊤ _))
      rw [← CommRingCat.comp_apply, c1]
      change (hU.fromSpec.app U ≫ _).hom r = _
      rw [hU.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE]
      rfl
    change G.hom.hom ((j.appLE _ ⊤ hle).hom _) = _
    rw [h0]
    have e2 := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom : Γ(S, U) →+* AddMonoidAlgebra Γ(S, U) N))
    have e3 := congrArg (fun k => k.hom r) e2
    change (G.inv.hom _) = (piR N Γ(S, U)).appTop.hom _ at e3
    refine (congrArg G.hom.hom e3.symm).trans ?_
    change (G.inv ≫ G.hom).hom _ = _
    rw [G.inv_hom_id]
    rfl

end AlgMag.GB
