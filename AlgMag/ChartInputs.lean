/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Stability
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraizationLocallyFiniteType

/-!
# Big inputs of the specialized AHR chart: Bhatt's algebraization and gluing

Restricted forms of Bhatt, *Algebraization and Tannaka duality* (arXiv:1404.7483), used in
the chart-lemma proof §4.

* `AlgMag.ChartInputs.bhatt11`: Theorem 1.1 for `A` Noetherian `I`-adically complete and a target
  separated and locally of finite type over `Spec A`. As in Bhatt's own example, this is
  algebraization (Stacks 0GHK) applied to the proper source `Spec A`.
* `AlgMag.ChartInputs.bhatt14`: Theorem 1.4(1) for `C` Noetherian, `Y` flat affine over `Spec C`
  and a separated target. Proved from the fpqc sheaf property (Stacks 0APL) and the separating
  lemma `eq_zero_of_flat_of_annihilated_of_mem_pow`, as in the notes' §4 Remark.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space
open scoped TensorProduct

universe u

namespace AlgMag.ChartInputs

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **Separating lemma** (notes §4, Lemma 4.5). -/
theorem eq_zero_of_flat_of_annihilated_of_mem_pow {C Q : Type u} [CommRing C] [IsNoetherianRing C]
    [CommRing Q] [Algebra C Q] [Module.Flat C Q] (a : Ideal C) {r : Q} (s : ℕ)
    (hs : ∀ x ∈ a ^ s, algebraMap C Q x * r = 0)
    (hk : ∀ k, r ∈ (a ^ k).map (algebraMap C Q)) : r = 0 := by
  classical
  obtain ⟨gs, hgs⟩ : (a ^ s).FG := IsNoetherian.noetherian _
  -- `J = (0 : a ^ s)` is the kernel of `g : C → (gs → C)`.
  let g : C →ₗ[C] (gs → C) := LinearMap.pi fun i => LinearMap.mulLeft C (i : C)
  let J : Submodule C C := LinearMap.ker g
  have hJ : ∀ y ∈ J, ∀ x ∈ a ^ s, x * y = 0 := by
    intro y hy x hx
    rw [← hgs] at hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact congrFun (LinearMap.mem_ker.1 hy) ⟨z, hz⟩
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul, hu, hv, zero_add]
    | smul c u _ hu => rw [smul_eq_mul, mul_assoc, hu, mul_zero]
  -- Artin--Rees: `a ^ k ∩ J = 0` for large `k`.
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul a J
  have hinf : (a ^ (s + c) • ⊤ : Submodule C C) ⊓ J = ⊥ := by
    rw [hc (s + c) (Nat.le_add_left c s), add_tsub_cancel_right, eq_bot_iff]
    refine Submodule.smul_le.2 fun x hx y hy => ?_
    obtain ⟨-, hyJ⟩ := Submodule.mem_inf.1 hy
    simpa using hJ y hyJ x hx
  let k := s + c
  let h : C →ₗ[C] (C ⧸ a ^ k) := (Submodule.mkQ (a ^ k)).restrictScalars C
  have hinj : Function.Injective (h ∘ₗ J.subtype) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨y, hyJ⟩ hy
    have hy' : y ∈ a ^ k := by
      have : (Ideal.Quotient.mk (a ^ k)) y = 0 := hy
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    have : y ∈ (a ^ k • ⊤ : Submodule C C) ⊓ J :=
      ⟨by simpa [smul_eq_mul, Ideal.mul_top] using hy', hyJ⟩
    rw [hinf] at this
    simpa using (Submodule.mem_bot C).1 this
  have hexact : Function.Exact J.subtype g := fun y => by
    simp [J, LinearMap.mem_ker, eq_comm]
  have hexQ := Module.Flat.lTensor_exact Q hexact
  have hinjQ := Module.Flat.lTensor_preserves_injective_linearMap (M := Q) _ hinj
  have hg0 : (g.lTensor Q) (r ⊗ₜ[C] (1 : C)) = 0 := by
    apply (TensorProduct.piRight C C Q fun _ : gs => C).injective
    ext i
    simp only [LinearMap.lTensor_tmul, map_zero, Pi.zero_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]
    have hmem : (i : C) ∈ a ^ s := by
      rw [← hgs]
      exact Submodule.subset_span i.2
    have : (i : C) • r = 0 := by
      rw [Algebra.smul_def]
      exact hs _ hmem
    simp only [g, LinearMap.pi_apply, LinearMap.mulLeft_apply, mul_one]
    rw [← mul_one (i : C), ← smul_eq_mul, ← TensorProduct.smul_tmul, this, TensorProduct.zero_tmul]
  obtain ⟨z, hz⟩ := (hexQ _).1 hg0
  have hh0 : (h.lTensor Q) (r ⊗ₜ[C] (1 : C)) = 0 := by
    have key : ∀ q ∈ (a ^ k).map (algebraMap C Q), ∀ c : Q,
        (h.lTensor Q) ((c * q) ⊗ₜ[C] (1 : C)) = 0 := by
      intro q hq
      refine Submodule.span_induction (p := fun q _ => ∀ c : Q,
        (h.lTensor Q) ((c * q) ⊗ₜ[C] (1 : C)) = 0) ?_ ?_ ?_ ?_ hq
      · rintro _ ⟨x, hx, rfl⟩ c
        have hx0 : h x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hx
        have : (c * algebraMap C Q x) ⊗ₜ[C] (1 : C) = c ⊗ₜ[C] x := by
          have e : c * algebraMap C Q x = x • c := by
            rw [Algebra.smul_def, mul_comm]
          rw [e, TensorProduct.smul_tmul, smul_eq_mul, mul_one]
        rw [this, LinearMap.lTensor_tmul, hx0, TensorProduct.tmul_zero]
      · intro c; simp
      · intro u v _ _ hu hv c
        rw [mul_add, TensorProduct.add_tmul, map_add, hu, hv, zero_add]
      · intro c' u _ hu c
        rw [smul_eq_mul, ← mul_assoc]
        exact hu _
    simpa using key r (hk k) 1
  have hz0 : z = 0 := hinjQ (by
    rw [map_zero, LinearMap.lTensor_comp_apply, hz, hh0])
  rw [hz0, map_zero] at hz
  simpa using congrArg (TensorProduct.rid C Q) hz.symm

theorem map_eq_zero_of_factor {Q B : Type u} [CommRing Q] [CommRing B] {E : Scheme.{u}}
    (ι : E ⟶ Spec (.of Q)) (ψ : Q →+* B) (l : Spec (.of B) ⟶ E)
    (h : l ≫ ι = Spec.map (CommRingCat.ofHom ψ)) {r : Q}
    (hr : ι.appTop ((Scheme.ΓSpecIso (.of Q)).inv r) = 0) : ψ r = 0 := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have e2 := congrArg (fun t => t.hom r) e
  have e3 : (Spec.map (CommRingCat.ofHom ψ)).appTop ((Scheme.ΓSpecIso (.of Q)).inv r) =
      l.appTop (ι.appTop ((Scheme.ΓSpecIso (.of Q)).inv r)) := by
    rw [← h, Scheme.Hom.comp_appTop]
    rfl
  have e4 : (Scheme.ΓSpecIso (.of B)).inv (ψ r) = 0 := by
    refine Eq.trans e2 ?_
    refine Eq.trans e3 ?_
    rw [hr, map_zero]
  have : (Scheme.ΓSpecIso (.of B)).hom ((Scheme.ΓSpecIso (.of B)).inv (ψ r)) = ψ r := by simp
  rw [← this, e4, map_zero]

/-- **Closed subscheme containing the open part and the thickenings** (notes §4 Remark). -/
theorem isIso_of_isClosedImmersion_of_factors {C Q : Type u} [CommRing C] [IsNoetherianRing C]
    [CommRing Q] [Algebra C Q] [Module.Flat C Q] (a : Ideal C) {E : Scheme.{u}}
    (ι : E ⟶ Spec (.of Q)) [IsClosedImmersion ι]
    (hopen : ∀ x ∈ a, ∃ l : Spec (.of (Localization.Away (algebraMap C Q x))) ⟶ E,
      l ≫ ι = Spec.map (CommRingCat.ofHom
        (algebraMap Q (Localization.Away (algebraMap C Q x)))))
    (hthick : ∀ k : ℕ, ∃ l : Spec (.of (Q ⧸ (a ^ (k + 1)).map (algebraMap C Q))) ⟶ E,
      l ≫ ι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))) :
    IsIso ι := by
  have hE : IsAffine E := isAffine_of_isAffineHom ι
  have hsurj : Function.Surjective ι.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ι).2
  have hzero : ∀ r : Q, ι.appTop ((Scheme.ΓSpecIso (.of Q)).inv r) = 0 → r = 0 := by
    intro r hr
    let J : Ideal C := LinearMap.ker ((LinearMap.toSpanSingleton Q Q r).restrictScalars C ∘ₗ
      (Algebra.linearMap C Q))
    have hJ : ∀ x, x ∈ J ↔ algebraMap C Q x * r = 0 := fun x => by
      simp [J, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_comm]
    have hrad : a ≤ J.radical := by
      intro x hx
      obtain ⟨l, hl⟩ := hopen x hx
      have h0 := map_eq_zero_of_factor ι _ l hl hr
      obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
        (Submonoid.powers (algebraMap C Q x)) _ r).1 h0
      refine ⟨n, (hJ _).2 ?_⟩
      simpa [map_pow, mul_comm] using hn
    obtain ⟨s, hs⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian a)
    refine eq_zero_of_flat_of_annihilated_of_mem_pow a s (fun x hx => (hJ x).1 (hs hx)) fun k => ?_
    have hle : (a ^ (k + 1)).map (algebraMap C Q) ≤ (a ^ k).map (algebraMap C Q) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ k))
    obtain ⟨l, hl⟩ := hthick k
    exact hle (Ideal.Quotient.eq_zero_iff_mem.1 (map_eq_zero_of_factor ι _ l hl hr))
  have hinj : Function.Injective ι.appTop := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : y = (Scheme.ΓSpecIso (.of Q)).inv ((Scheme.ΓSpecIso (.of Q)).hom y) := by simp
    rw [this] at hy ⊢
    rw [hzero _ hy, map_zero]
  have hiso : IsIso ι.appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, hsurj⟩
  have hn : ι ≫ (Spec (.of Q)).toSpecΓ = E.toSpecΓ ≫ Spec.map ι.appTop :=
    Scheme.toSpecΓ_naturality ι
  have hc : IsIso (ι ≫ (Spec (.of Q)).toSpecΓ) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_right ι (Spec (.of Q)).toSpecΓ


section Equalizer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Equalizer of two sections of a separated morphism: a closed subscheme of the source. -/
theorem exists_closed_equalizer {fX : X ⟶ G} (hsep : IsSeparated B S hS fX)
    {P : BigFppfOver B S hS} (a b : yoneda.obj P ⟶ X) (hab : a ≫ fX = b ≫ fX) :
    ∃ (E : BigFppfOver B S hS) (ι : E ⟶ P),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι) ∧
      yoneda.map ι ≫ a = yoneda.map ι ≫ b ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ P), yoneda.map g ≫ a = yoneda.map g ≫ b →
        ∃ l : W ⟶ E, l ≫ ι = g := by
  have hrep := hsep.1
  let c : yoneda.obj P ⟶ pullback fX fX := pullback.lift a b hab
  have sq := hrep.isPullback c
  refine ⟨hrep.pullback c, hrep.snd c, hsep.2 c _ _ sq, ?_, ?_⟩
  · have h := sq.w
    have h1 := congrArg (· ≫ pullback.fst fX fX) h
    have h2 := congrArg (· ≫ pullback.snd fX fX) h
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, c,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    exact h1.symm.trans h2
  · intro W g hg
    refine ⟨hrep.lift (yoneda.map g ≫ a) g ?_, hrep.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id, c]
    · simp only [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id, c, hg]

end Equalizer


section Glue

variable {C : Type u} [CommRing C] [IsNoetherianRing C] {a : Ideal C} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of C))} {hSn : ∀ n, B.Contains (adicThickening C a n)}
  {X : (BigFppfOver B (Spec (.of C)) hS)ᵒᵖ ⥤ Type u}

/-- Two jointly surjective flat quasi-compact morphisms to an affine scheme are an fpqc family. -/
theorem ofArrows_two_mem_fpqcPrecoverage {T : Scheme.{u}} [IsAffine T] (Z : Fin 2 → Scheme.{u})
    (q : ∀ i, Z i ⟶ T) (hq : ∀ i, Flat (q i)) (hc : ∀ i, QuasiCompact (q i))
    (hcov : ∀ x : T, ∃ i, x ∈ Set.range (q i)) :
    Presieve.ofArrows Z q ∈ Scheme.fpqcPrecoverage T := by
  let 𝒰 : T.Cover (Scheme.precoverage @Flat) := Scheme.Cover.mkOfCovers (Fin 2) Z q hcov hq
  have hcompact : ∀ i, QuasiCompact (𝒰.f i) := hc
  have := Scheme.jointlySurjective_precoverage_flat
  have hfin : Finite 𝒰.I₀ := inferInstanceAs (Finite (Fin 2))
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
    (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, hq⟩⟩

/-- Sheaf gluing along a two-member fpqc family, for morphisms out of representables. -/
theorem existsUnique_glue_of_fpqc (hX : IsAlgebraicSpace B _ hS X)
    {T : BigFppfOver B (Spec (.of C)) hS} (Z : Fin 2 → BigFppfOver B (Spec (.of C)) hS)
    (q : ∀ i, Z i ⟶ T)
    (hcov : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B (Spec (.of C)) hS).obj (Z i)) (fun i => (BigFppfOver.toScheme B (Spec (.of C)) hS).map (q i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj T))
    (x : ∀ i, yoneda.obj (Z i) ⟶ X)
    (hx : ∀ i j ⦃W : BigFppfOver B (Spec (.of C)) hS⦄ (g₁ : W ⟶ Z i) (g₂ : W ⟶ Z j),
      g₁ ≫ q i = g₂ ≫ q j → yoneda.map g₁ ≫ x i = yoneda.map g₂ ≫ x j) :
    ∃! φ : yoneda.obj T ⟶ X, ∀ i, yoneda.map (q i) ≫ φ = x i := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have hR : Presieve.ofArrows Z q ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B (Spec (.of C)) hS) T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hcov
  have hF := (Presieve.isSheafFor_arrows_iff X q).1 (hsh _ hR)
  obtain ⟨t, ht, hu⟩ := hF (fun i => yonedaEquiv (x i)) (by
    intro i j W g₁ g₂ h
    have e := congrArg yonedaEquiv (hx i j g₁ g₂ h)
    have e1 := yonedaEquiv_naturality (x i) g₁
    have e2 := yonedaEquiv_naturality (x j) g₂
    exact e1.trans (e.trans e2.symm))
  refine ⟨yonedaEquiv.symm t, fun i => ?_, fun φ hφ => ?_⟩
  · apply yonedaEquiv.injective
    have e := yonedaEquiv_naturality (yonedaEquiv.symm t) (q i)
    rw [Equiv.apply_symm_apply] at e
    exact e.symm.trans (ht i)
  · apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    refine hu _ fun i => ?_
    have e := yonedaEquiv_naturality φ (q i)
    exact e.trans (congrArg yonedaEquiv (hφ i))

/-- A scheme-level cone over a site-level cospan lifts through the site-level pullback. -/
theorem exists_lift_sch_pullback {A₁ A₂ A₃ : BigFppfOver B (Spec (.of C)) hS} (f : A₁ ⟶ A₃)
    (f' : A₂ ⟶ A₃) {W : Scheme.{u}} (g : W ⟶ (BigFppfOver.toScheme B (Spec (.of C)) hS).obj A₁) (h : W ⟶ (BigFppfOver.toScheme B (Spec (.of C)) hS).obj A₂)
    (w : g ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map f = h ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map f') :
    ∃ l : W ⟶ (BigFppfOver.toScheme B (Spec (.of C)) hS).obj (pullback f f'), l ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map (pullback.fst f f') = g := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B (Spec (.of C)) hS) := inferInstance
  refine ⟨pullback.lift g h w ≫ inv (pullbackComparison (BigFppfOver.toScheme B (Spec (.of C)) hS) f f'), ?_⟩
  have e : inv (pullbackComparison (BigFppfOver.toScheme B (Spec (.of C)) hS) f f') ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map (pullback.fst f f') =
      pullback.fst _ _ := by
    rw [IsIso.inv_comp_eq, pullbackComparison_comp_fst]
  rw [Category.assoc, e, pullback.lift_fst]

/-- **The overlap `Y ×_T Y`**: in the situation of `bhatt14`, the two pullbacks of a section `t`
of a separated `X` to `Y ×_T Y` agree. This is the only non-formal step (notes §4 Remark). -/
theorem eq_on_overlap {U Y : BigFppfOver B (Spec (.of C)) hS}
    (j : U ⟶ baseObject C B hS) (p : Y ⟶ baseObject C B hS)
    (hYaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj Y)) (hj : IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j))
    (hjr : Set.range ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) = (PrimeSpectrum.zeroLocus (a : Set C))ᶜ)
    (hp : Flat ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p))
    (hiso : ∀ k, IsIso (pullback.snd p (adicThickeningMap C a B hS hSn k)))
    {fX : X ⟶ yoneda.obj (baseObject C B hS)} (hsep : IsSeparated B _ hS fX)
    (u : yoneda.obj U ⟶ X) (t : yoneda.obj Y ⟶ X) (ht : t ≫ fX = yoneda.map p)
    (huv : ∀ ⦃W : BigFppfOver B (Spec (.of C)) hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y),
      g₁ ≫ j = g₂ ≫ p → yoneda.map g₁ ≫ u = yoneda.map g₂ ≫ t)
    ⦃W : BigFppfOver B (Spec (.of C)) hS⦄ (g₁ g₂ : W ⟶ Y) (hg : g₁ ≫ p = g₂ ≫ p) :
    yoneda.map g₁ ≫ t = yoneda.map g₂ ≫ t := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B (Spec (.of C)) hS) := inferInstance
  let P := pullback p p
  let pr₁ : P ⟶ Y := pullback.fst p p
  let pr₂ : P ⟶ Y := pullback.snd p p
  have hpr : pr₁ ≫ p = pr₂ ≫ p := pullback.condition
  let ta := yoneda.map pr₁ ≫ t
  let tb := yoneda.map pr₂ ≫ t
  have hab : ta ≫ fX = tb ≫ fX := by
    simp only [ta, tb, Category.assoc, ht, ← yoneda.map_comp, hpr]
  obtain ⟨E, ι, hιc, hιeq, hfac⟩ := exists_closed_equalizer hsep ta tb hab
  have hT : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj (baseObject C B hS)) := inferInstanceAs (IsAffine (Spec (.of C)))
  have hPaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P) := by
    have : IsAffine (pullback ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p) ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p)) := by
      letI : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj Y) := hYaff
      letI : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj (baseObject C B hS)) := hT
      infer_instance
    exact .of_isIso (pullbackComparison (BigFppfOver.toScheme B (Spec (.of C)) hS) p p)
  let π : (BigFppfOver.toScheme B (Spec (.of C)) hS).obj P ⟶ Spec (.of C) := (BigFppfOver.toScheme B (Spec (.of C)) hS).map (pr₁ ≫ p)
  have hπflat : Flat π := by
    have e : π = pullbackComparison (BigFppfOver.toScheme B (Spec (.of C)) hS) p p ≫ pullback.fst _ _ ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map p := by
      simp only [π, pr₁, Functor.map_comp]
      rw [← Category.assoc, pullbackComparison_comp_fst]
    rw [e]
    infer_instance
  let Q := Γ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P, ⊤)
  let φ : C →+* Q := (π.appTop.hom).comp (Scheme.ΓSpecIso (.of C)).inv.hom
  letI : Algebra C Q := φ.toAlgebra
  have hπ : π = ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    have hφ : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of C)).inv ≫ π.appTop := rfl
    have hn := Scheme.toSpecΓ_naturality π
    rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← hn, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hQflat : Module.Flat C Q := by
    have hf : Flat (Spec.map (CommRingCat.ofHom φ)) := by
      have e : Spec.map (CommRingCat.ofHom φ) = ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.inv ≫ π := by
        rw [hπ, Iso.inv_hom_id_assoc]
      rw [e]; infer_instance
    exact Flat.SpecMap_iff.1 hf
  let ι' : (BigFppfOver.toScheme B (Spec (.of C)) hS).obj E ⟶ Spec (.of Q) := (BigFppfOver.toScheme B (Spec (.of C)) hS).map ι ≫ ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.hom
  have hιc' : AlgebraicGeometry.IsClosedImmersion ι' := by
    have := hιc
    infer_instance
  have hιiso : IsIso ι' := by
    refine isIso_of_isClosedImmersion_of_factors a ι' ?_ ?_
    · intro x hx
      let L := Localization.Away (algebraMap C Q x)
      let g : Spec (.of L) ⟶ (BigFppfOver.toScheme B (Spec (.of C)) hS).obj P :=
        Spec.map (CommRingCat.ofHom (algebraMap Q L)) ≫ ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.inv
      have hgπ : g ≫ π = Spec.map (CommRingCat.ofHom ((algebraMap Q L).comp φ)) := by
        simp only [g, Category.assoc]
        rw [hπ, Iso.inv_hom_id_assoc, ← Spec.map_comp]
        rfl
      have hr : Set.range (g ≫ π) ⊆ Set.range ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) := by
        rw [hjr]
        rintro _ ⟨y, rfl⟩ hz
        rw [hgπ] at hz
        have hmem : x ∈ (PrimeSpectrum.comap ((algebraMap Q L).comp φ) y).asIdeal := hz hx
        have hu : IsUnit (algebraMap Q L (algebraMap C Q x)) :=
          IsLocalization.Away.algebraMap_isUnit (algebraMap C Q x)
        exact (Ideal.IsPrime.ne_top y.2).elim ((Ideal.eq_top_of_isUnit_mem _ hmem hu))
      let h' := IsOpenImmersion.lift ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) (g ≫ π) hr
      obtain ⟨l₁, hl₁⟩ := exists_lift_sch_pullback (pr₁ ≫ p) j g h'
        (IsOpenImmersion.lift_fac ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) (g ≫ π) hr).symm
      obtain ⟨l₀, hl₀⟩ := hfac (pullback.fst (pr₁ ≫ p) j) (by
        have hc₁ : pullback.snd (pr₁ ≫ p) j ≫ j = (pullback.fst (pr₁ ≫ p) j ≫ pr₁) ≫ p := by
          rw [Category.assoc]; exact pullback.condition.symm
        have hc₂ : pullback.snd (pr₁ ≫ p) j ≫ j = (pullback.fst (pr₁ ≫ p) j ≫ pr₂) ≫ p := by
          rw [Category.assoc, ← hpr]; exact pullback.condition.symm
        have e₁ := huv _ _ hc₁
        have e₂ := huv _ _ hc₂
        simp only [ta, tb, ← Category.assoc, ← yoneda.map_comp]
        exact e₁.symm.trans e₂)
      refine ⟨l₁ ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀, ?_⟩
      have : (BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀ ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map ι = (BigFppfOver.toScheme B (Spec (.of C)) hS).map (pullback.fst (pr₁ ≫ p) j) := by
        rw [← Functor.map_comp, hl₀]
      simp only [ι', Category.assoc]
      rw [← Category.assoc ((BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀), this, ← Category.assoc l₁, hl₁]
      simp [g]
    · intro k
      let J := (a ^ (k + 1)).map (algebraMap C Q)
      let g : Spec (.of (Q ⧸ J)) ⟶ (BigFppfOver.toScheme B (Spec (.of C)) hS).obj P :=
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.inv
      let τ : C ⧸ a ^ (k + 1) →+* Q ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      let m := adicThickeningMap C a B hS hSn k
      have hw : g ≫ π = Spec.map (CommRingCat.ofHom τ) ≫ adicThickeningι C a k := by
        simp only [g, Category.assoc]
        rw [hπ, Iso.inv_hom_id_assoc, adicThickeningι, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨l₁, hl₁⟩ := exists_lift_sch_pullback (pr₁ ≫ p) m g (Spec.map (CommRingCat.ofHom τ)) hw
      let Pk := pullback (pr₁ ≫ p) m
      let f₀ : Pk ⟶ P := pullback.fst _ _
      let s₀ : Pk ⟶ _ := pullback.snd (pr₁ ≫ p) m
      have hc₁ : (f₀ ≫ pr₁) ≫ p = s₀ ≫ m := by
        rw [Category.assoc]; exact pullback.condition
      have hc₂ : (f₀ ≫ pr₂) ≫ p = s₀ ≫ m := by
        rw [Category.assoc, ← hpr]; exact pullback.condition
      have hii := hiso k
      have hl : pullback.lift _ _ hc₁ = pullback.lift _ _ hc₂ :=
        (cancel_mono (pullback.snd p m)).1 (by rw [pullback.lift_snd, pullback.lift_snd])
      have heq : f₀ ≫ pr₁ = f₀ ≫ pr₂ := by
        have e₁ := pullback.lift_fst (f₀ ≫ pr₁) s₀ hc₁
        have e₂ := pullback.lift_fst (f₀ ≫ pr₂) s₀ hc₂
        rw [← e₁, ← e₂, hl]
      obtain ⟨l₀, hl₀⟩ := hfac f₀ (by
        simp only [ta, tb, ← Category.assoc, ← yoneda.map_comp, heq])
      refine ⟨l₁ ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀, ?_⟩
      have : (BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀ ≫ (BigFppfOver.toScheme B (Spec (.of C)) hS).map ι = (BigFppfOver.toScheme B (Spec (.of C)) hS).map f₀ := by
        rw [← Functor.map_comp, hl₀]
      simp only [ι', Category.assoc]
      rw [← Category.assoc ((BigFppfOver.toScheme B (Spec (.of C)) hS).map l₀), this, ← Category.assoc l₁, hl₁]
      simp [g]
  have hs : IsIso ((BigFppfOver.toScheme B (Spec (.of C)) hS).map ι) := by
    have : (BigFppfOver.toScheme B (Spec (.of C)) hS).map ι = ι' ≫ ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj P).isoSpec.inv := by simp [ι']
    rw [this]; infer_instance
  have : IsIso (B.inclusion.map ((BigFppfOver.forget B _ hS).map ι)) := hs
  have : IsIso ((BigFppfOver.forget B _ hS).map ι) := isIso_of_reflects_iso _ B.inclusion
  have : IsIso ι := isIso_of_reflects_iso _ (Over.forget (B.obj hS))
  have htab : ta = tb := by
    have hy : IsIso (yoneda.map ι) := inferInstance
    exact (cancel_epi (yoneda.map ι)).1 hιeq
  let m : W ⟶ P := pullback.lift g₁ g₂ hg
  have e₁ : yoneda.map m ≫ ta = yoneda.map g₁ ≫ t := by
    simp only [ta]
    rw [← Category.assoc, ← yoneda.map_comp, show m ≫ pr₁ = g₁ from pullback.lift_fst _ _ _]
  have e₂ : yoneda.map m ≫ tb = yoneda.map g₂ ≫ t := by
    simp only [tb]
    rw [← Category.assoc, ← yoneda.map_comp, show m ≫ pr₂ = g₂ from pullback.lift_snd _ _ _]
  rw [← e₁, ← e₂, htab]

/-- **Bhatt, Theorem 1.4(1), restricted form** (arXiv:1404.7483): `C` Noetherian, `U = Spec C \ V(a)`,
`Y → Spec C` flat with `Y` affine and an isomorphism over every thickening of `V(a)`, target
separated over `Spec C`. Then `Spec C` is the pushout of `U` and `Y` over `U ×_C Y`, for morphisms
to `X` over `Spec C`. The hypothesis `hZ` (`V(a)` lies in the image of `Y`) follows from `hiso`
in the case of interest; it is kept as stated data. -/
theorem bhatt14 {U Y : BigFppfOver B (Spec (.of C)) hS}
    (j : U ⟶ baseObject C B hS) (p : Y ⟶ baseObject C B hS)
    (hYaff : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj Y)) (hj : IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j))
    (hjr : Set.range ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) = (PrimeSpectrum.zeroLocus (a : Set C))ᶜ)
    (hp : Flat ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p))
    (hZ : PrimeSpectrum.zeroLocus (a : Set C) ⊆ Set.range ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p))
    (hiso : ∀ k, IsIso (pullback.snd p (adicThickeningMap C a B hS hSn k)))
    (hX : IsAlgebraicSpace B _ hS X)
    {fX : X ⟶ yoneda.obj (baseObject C B hS)} (hsep : IsSeparated B _ hS fX)
    (u : yoneda.obj U ⟶ X) (t : yoneda.obj Y ⟶ X)
    (hu : u ≫ fX = yoneda.map j) (ht : t ≫ fX = yoneda.map p)
    (huv : ∀ ⦃W : BigFppfOver B (Spec (.of C)) hS⦄ (g₁ : W ⟶ U) (g₂ : W ⟶ Y),
      g₁ ≫ j = g₂ ≫ p → yoneda.map g₁ ≫ u = yoneda.map g₂ ≫ t) :
    ∃! φ : yoneda.obj (baseObject C B hS) ⟶ X,
      φ ≫ fX = 𝟙 _ ∧ yoneda.map j ≫ φ = u ∧ yoneda.map p ≫ φ = t := by
  let Z : Fin 2 → BigFppfOver B (Spec (.of C)) hS := Fin.cons U (fun _ => Y)
  let q : ∀ i, Z i ⟶ baseObject C B hS := fun i =>
    Fin.cases (motive := fun i => Z i ⟶ baseObject C B hS) j (fun _ => p) i
  have hT : IsAffine ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj (baseObject C B hS)) := inferInstanceAs (IsAffine (Spec (.of C)))
  have hcov : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B (Spec (.of C)) hS).obj (Z i)) (fun i => (BigFppfOver.toScheme B (Spec (.of C)) hS).map (q i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj (baseObject C B hS)) := by
    refine ofArrows_two_mem_fpqcPrecoverage _ _ ?_ ?_ ?_
    · rw [Fin.forall_fin_two]
      exact ⟨inferInstanceAs (Flat ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j)), hp⟩
    · rw [Fin.forall_fin_two]
      refine ⟨?_, ?_⟩
      · have hN₀ : TopologicalSpace.NoetherianSpace ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj (baseObject C B hS)) :=
          inferInstanceAs (TopologicalSpace.NoetherianSpace (PrimeSpectrum C))
        have hN : TopologicalSpace.NoetherianSpace ((BigFppfOver.toScheme B (Spec (.of C)) hS).obj U) :=
          hj.base_open.isInducing.noetherianSpace
        exact quasiCompact_of_noetherianSpace_source ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j)
      · letI := hYaff
        letI := hT
        exact inferInstanceAs (QuasiCompact ((BigFppfOver.toScheme B (Spec (.of C)) hS).map p))
    · intro x
      by_cases hx : x ∈ PrimeSpectrum.zeroLocus (a : Set C)
      · exact ⟨1, hZ hx⟩
      · have : x ∈ Set.range ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) := by rw [hjr]; exact hx
        exact ⟨0, this⟩
  have hjm : Mono j := by
    have : Mono ((BigFppfOver.toScheme B (Spec (.of C)) hS).map j) := inferInstance
    exact Functor.mono_of_mono_map (BigFppfOver.toScheme B (Spec (.of C)) hS) this
  let x : ∀ i, yoneda.obj (Z i) ⟶ X := fun i =>
    Fin.cases (motive := fun i => yoneda.obj (Z i) ⟶ X) u (fun _ => t) i
  have hcompat : ∀ i k ⦃W : BigFppfOver B (Spec (.of C)) hS⦄ (g₁ : W ⟶ Z i) (g₂ : W ⟶ Z k),
      g₁ ≫ q i = g₂ ≫ q k → yoneda.map g₁ ≫ x i = yoneda.map g₂ ≫ x k := by
    rw [Fin.forall_fin_two]
    constructor <;> rw [Fin.forall_fin_two] <;> constructor
    · intro W g₁ g₂ h
      rw [(cancel_mono j).1 h]
    · intro W g₁ g₂ h
      exact huv g₁ g₂ h
    · intro W g₁ g₂ h
      exact (huv g₂ g₁ h.symm).symm
    · intro W g₁ g₂ h
      exact eq_on_overlap (hSn := hSn) j p hYaff hj hjr hp hiso hsep u t ht huv g₁ g₂ h
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_glue_of_fpqc hX Z q hcov x hcompat
  have hbase := existsUnique_glue_of_fpqc (isAlgebraicSpace_yoneda B _ hS (baseObject C B hS))
    Z q hcov (fun i => yoneda.map (q i)) (by
      intro i k W g₁ g₂ h
      rw [← yoneda.map_comp, ← yoneda.map_comp, h])
  have hover : φ ≫ fX = 𝟙 _ := by
    refine hbase.unique (fun i => ?_) (fun i => Category.comp_id _)
    rw [← Category.assoc, hφ i]
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨hu, ht⟩
  refine ⟨φ, ⟨hover, hφ 0, hφ 1⟩, ?_⟩
  rintro φ' ⟨-, h₁, h₂⟩
  refine huniq φ' fun i => ?_
  revert i
  rw [Fin.forall_fin_two]
  exact ⟨h₁, h₂⟩

end Glue

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}
  {Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- The base-as-source form of a compatible system of sections: the system of adic-fibre maps out
of the identity of `Spec A`. -/
noncomputable def sectionFibreMap {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n)) (n : ℕ) :
    adicFibre A I B hS hSn (𝟙 (yoneda.obj (baseObject A B hS))) n ⟶
      adicFibre A I B hS hSn fY n :=
  pullback.lift (pullback.snd _ _ ≫ y n) (pullback.snd _ _) (by
    rw [Category.assoc, hy])

theorem sectionFibreMap_fst {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n)) (n : ℕ) :
    sectionFibreMap y hy n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd _ _ ≫ y n := pullback.lift_fst _ _ _

theorem sectionFibreMap_snd {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n)) (n : ℕ) :
    sectionFibreMap y hy n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd _ _ := pullback.lift_snd _ _ _

theorem sectionFibreMap_succ {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n))
    (hyc : ∀ n, yoneda.map (adicThickeningSuccMap A I B hS hSn n) ≫ y (n + 1) = y n) (n : ℕ) :
    adicFibreSucc A I B hS hSn (𝟙 _) n ≫ sectionFibreMap y hy (n + 1) =
      sectionFibreMap y hy n ≫ adicFibreSucc A I B hS hSn fY n := by
  apply pullback.hom_ext
  · rw [Category.assoc, sectionFibreMap_fst, adicFibreSucc_snd_assoc, Category.assoc,
      adicFibreSucc_fst, sectionFibreMap_fst, hyc]
  · rw [Category.assoc, sectionFibreMap_snd, adicFibreSucc_snd, Category.assoc, adicFibreSucc_snd,
      ← Category.assoc, sectionFibreMap_snd]

/-- A morphism over the base with the adic fibres of the system `y` restricts to `y`, and
conversely. -/
theorem adicFibreMap_eq_sectionFibreMap_iff {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n))
    (s : yoneda.obj (baseObject A B hS) ⟶ Y) (hs : s ≫ fY = 𝟙 _) (n : ℕ) :
    adicFibreMap A I B hS hSn s hs n = sectionFibreMap y hy n ↔
      yoneda.map (adicThickeningMap A I B hS hSn n) ≫ s = y n := by
  have hcond : pullback.fst (𝟙 (yoneda.obj (baseObject A B hS)))
      (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd _ _ ≫ yoneda.map (adicThickeningMap A I B hS hSn n) := by
    simpa using pullback.condition (f := 𝟙 (yoneda.obj (baseObject A B hS)))
      (g := yoneda.map (adicThickeningMap A I B hS hSn n))
  constructor
  · intro h
    let σ : yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ adicFibre A I B hS hSn (𝟙 _) n :=
      pullback.lift (yoneda.map (adicThickeningMap A I B hS hSn n)) (𝟙 _) (by simp)
    have h1 := congrArg (fun t => σ ≫ t ≫ pullback.fst fY _) h
    have hσf : σ ≫ pullback.fst _ _ = yoneda.map (adicThickeningMap A I B hS hSn n) :=
      pullback.lift_fst _ _ _
    have hσs : σ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    rw [adicFibreMap_fst, sectionFibreMap_fst, ← Category.assoc, hσf, ← Category.assoc, hσs,
      Category.id_comp] at h1
    exact h1
  · intro h
    apply pullback.hom_ext
    · rw [adicFibreMap_fst, sectionFibreMap_fst, hcond, Category.assoc, h]
    · rw [adicFibreMap_snd, sectionFibreMap_snd]

/-- Reduction of `bhatt11` to Grothendieck's algebraization of morphisms with source `Spec A`. -/
theorem existsUnique_section_of_algebraization {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (halg : ∀ (g : ∀ n, adicFibre A I B hS hSn (𝟙 (yoneda.obj (baseObject A B hS))) n ⟶
          adicFibre A I B hS hSn fY n),
        (∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
          pullback.snd _ _) →
        (∀ n, adicFibreSucc A I B hS hSn (𝟙 _) n ≫ g (n + 1) =
          g n ≫ adicFibreSucc A I B hS hSn fY n) →
        ∃! φ : yoneda.obj (baseObject A B hS) ⟶ Y,
          ∃ hφ : φ ≫ fY = 𝟙 _, ∀ n, adicFibreMap A I B hS hSn φ hφ n = g n)
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n))
    (hyc : ∀ n, yoneda.map (adicThickeningSuccMap A I B hS hSn n) ≫ y (n + 1) = y n) :
    ∃! s : yoneda.obj (baseObject A B hS) ⟶ Y,
      s ≫ fY = 𝟙 _ ∧ ∀ n, yoneda.map (adicThickeningMap A I B hS hSn n) ≫ s = y n := by
  obtain ⟨φ, ⟨hφ, hφn⟩, huniq⟩ := halg (sectionFibreMap y hy) (sectionFibreMap_snd y hy)
    (sectionFibreMap_succ y hy hyc)
  refine ⟨φ, ⟨hφ, fun n => (adicFibreMap_eq_sectionFibreMap_iff y hy φ hφ n).1 (hφn n)⟩, ?_⟩
  rintro s ⟨hs, hsn⟩
  exact huniq s ⟨hs, fun n => (adicFibreMap_eq_sectionFibreMap_iff y hy s hs n).2 (hsn n)⟩

section Bhatt11

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}
  {Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}

/-- **Bhatt, Theorem 1.1, restricted form** (arXiv:1404.7483): for `A` Noetherian and `I`-adically
complete and `Y` separated and locally of finite type over `Spec A`, a compatible system of
sections over the thickenings `Spec A/I^(n+1)` comes from a unique section over `Spec A`. -/
theorem bhatt11 [IsNoetherianRing A] [IsAdicComplete I A]
    (hY : IsAlgebraicSpace B _ hS Y) {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hsY : IsSeparated B _ hS fY) (hlY : IsLocallyOfFiniteType B _ hS fY)
    (y : ∀ n, yoneda.obj (adicThickeningObject A I B hS hSn n) ⟶ Y)
    (hy : ∀ n, y n ≫ fY = yoneda.map (adicThickeningMap A I B hS hSn n))
    (hyc : ∀ n, yoneda.map (adicThickeningSuccMap A I B hS hSn n) ≫ y (n + 1) = y n) :
    ∃! s : yoneda.obj (baseObject A B hS) ⟶ Y,
      s ≫ fY = 𝟙 _ ∧ ∀ n, yoneda.map (adicThickeningMap A I B hS hSn n) ≫ s = y n :=
  existsUnique_section_of_algebraization
    (fun g hg hgc => existsUnique_adicFibreMap_eq_of_isLocallyOfFiniteType
      (isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)) hY (𝟙 _) fY
      (isProper_of_isIso B _ hS (𝟙 _)) hsY hlY g hg hgc) y hy hyc

end Bhatt11

end AlgMag.ChartInputs
