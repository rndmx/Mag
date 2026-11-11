/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# Equivariant effectivity: §4 of the chart-lemma proof

Proved here without inputs:

* `AlgMag.Chart.separating`: Lemma 4.5.
* `AlgMag.Chart.smul_eq_zero_of_mul_eq_zero`, `AlgMag.Chart.deligne_wellDefined`: the Tor-kernel step
  of Lemma 4.3 and the resulting well-definedness of `Ψ ν_g⁻¹(1)`.
* `AlgMag.Chart.exists_eqLocus`: the equalizer of two points of a separated space is closed.
* `AlgMag.Chart.eq_of_agree_basicOpen_of_agree_thickening`: equalizer killing.
* `AlgMag.Chart.eq_of_agree_of_iInf`, `AlgMag.Chart.iInf_pow_eq_bot`: the uniqueness in Theorem 4.1.

Bhatt's theorems are named propositions with their statements (`AlgMag.Chart.BhattAlgebraization`,
`AlgMag.Chart.BhattPushoutFlat`), to be discharged by `AlgMag/ChartInputs.lean`.

Not proved: Lemmas 4.2 and 4.3 on algebraic spaces, hence existence in Theorem 4.1.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.Chart

/-! ### Commutative algebra -/

section Algebra

variable {C R : Type*} [CommRing C] [CommRing R] [Algebra C R]

/-- **Lemma 4.5 (separating).** Let `C` be noetherian, `a` an ideal, `R` a flat `C`-algebra and
`r ∈ R` with `a^s r = 0` and `r ∈ a^k R` for all `k`. Then `r = 0`. -/
theorem separating [IsNoetherianRing C] [Module.Flat C R] (a : Ideal C) (s : ℕ) (r : R)
    (hs : ∀ x ∈ a ^ s, algebraMap C R x * r = 0)
    (hk : ∀ k : ℕ, r ∈ (a ^ k).map (algebraMap C R)) : r = 0 := by
  classical
  let K : Ideal C :=
    { carrier := {c | ∀ x ∈ a ^ s, x * c = 0}
      add_mem' := fun {u v} hu hv x hx => by rw [mul_add, hu x hx, hv x hx, add_zero]
      zero_mem' := fun x _ => mul_zero x
      smul_mem' := fun c u hu x hx => by
        rw [smul_eq_mul, mul_left_comm, hu x hx, mul_zero] }
  obtain ⟨k, hkAR⟩ := Ideal.exists_pow_inf_eq_pow_smul a (M := C) K
  have hK : a ^ s • K = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro x hx c hc
    exact hc x hx
  have hinf : a ^ (k + s) ⊓ K = ⊥ := by
    have h := hkAR (k + s) (Nat.le_add_right k s)
    rw [Nat.add_sub_cancel_left] at h
    have h' : (a ^ (k + s) • (⊤ : Ideal C)) ⊓ K = ⊥ := by
      rw [h, eq_bot_iff, ← hK]
      exact Submodule.smul_mono le_rfl inf_le_right
    simpa using h'
  obtain ⟨t, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((IsNoetherian.noetherian (a ^ s) : (a ^ s).FG))
  let Θ : C →ₗ[C] (C ⧸ a ^ (k + s)) × (Fin t → C) :=
    LinearMap.prod (Submodule.mkQ _) (LinearMap.pi fun i => LinearMap.mulLeft C (g i))
  have hΘ : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : c ∈ a ^ (k + s) := by
      have := congrArg Prod.fst hc
      simpa [Θ, Ideal.Quotient.eq_zero_iff_mem] using this
    have h2 : ∀ i, g i * c = 0 := fun i => by
      have := congrFun (congrArg Prod.snd hc) i
      simpa [Θ] using this
    have h3 : c ∈ K := by
      intro x hx
      rw [← hg] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact h2 i
      | zero => exact zero_mul c
      | add u v _ _ hu hv => rw [add_mul, hu, hv, zero_add]
      | smul b u _ hu => rw [smul_eq_mul, mul_assoc, hu, mul_zero]
    have : c ∈ a ^ (k + s) ⊓ K := ⟨h1, h3⟩
    rw [hinf] at this
    exact this
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := R) Θ hΘ
  have hfst : ∀ r' ∈ (a ^ (k + s)).map (algebraMap C R),
      r' ⊗ₜ[C] (((Submodule.mkQ (a ^ (k + s))) 1, 0) : (C ⧸ a ^ (k + s)) × (Fin t → C)) = 0 := by
    intro r' hr'
    induction hr' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← mul_one (algebraMap C R x), ← Algebra.smul_def, TensorProduct.smul_tmul]
      have : x • (((Submodule.mkQ (a ^ (k + s))) 1, 0) : (C ⧸ a ^ (k + s)) × (Fin t → C)) = 0 := by
        ext
        · change Submodule.Quotient.mk (x • (1 : C)) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          simpa using hx
        · simp
      rw [this, TensorProduct.tmul_zero]
    | zero => rw [TensorProduct.zero_tmul]
    | add u v _ _ hu hv => rw [TensorProduct.add_tmul, hu, hv, add_zero]
    | smul b u _ hu =>
      rw [smul_eq_mul, ← smul_eq_mul, ← TensorProduct.smul_tmul', hu, smul_zero]
  have hsnd : r ⊗ₜ[C] (((0 : C ⧸ a ^ (k + s)), fun i => g i) : (C ⧸ a ^ (k + s)) × (Fin t → C)) = 0 := by
    have hdec : (((0 : C ⧸ a ^ (k + s)), fun i => g i) : (C ⧸ a ^ (k + s)) × (Fin t → C)) =
        ∑ i, g i • (((0 : C ⧸ a ^ (k + s)), Pi.single i 1) : (C ⧸ a ^ (k + s)) × (Fin t → C)) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hdec, TensorProduct.tmul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← TensorProduct.smul_tmul]
    have hgi : g i ∈ a ^ s := by rw [← hg]; exact Submodule.subset_span ⟨i, rfl⟩
    rw [Algebra.smul_def, hs _ hgi, TensorProduct.zero_tmul]
  have hzero : LinearMap.lTensor R Θ (r ⊗ₜ[C] (1 : C)) = 0 := by
    have hΘ1 : Θ 1 = ((Submodule.mkQ (a ^ (k + s))) 1, 0) + ((0 : C ⧸ a ^ (k + s)), fun i => g i) := by
      ext j
      · simp [Θ]
      · simp [Θ]
    rw [LinearMap.lTensor_tmul, hΘ1, TensorProduct.tmul_add, hfst r (hk _), hsnd, add_zero]
  have h1 : r ⊗ₜ[C] (1 : C) = 0 := hinj (by rw [hzero, map_zero])
  have := congrArg (TensorProduct.rid C R) h1
  simpa using this

/-- The multiplication map `B ⊗_A J → B`, `b ⊗ i ↦ b i`, for an ideal `J` of `A`. -/
noncomputable def idealMul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) :
    B ⊗[A] J →ₗ[A] B :=
  TensorProduct.lift
    ((LinearMap.mul A B).compl₂ ((Algebra.linearMap A B).comp J.subtype))

@[simp] lemma idealMul_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
    (b : B) (i : J) : idealMul J (b ⊗ₜ[A] i) = b * algebraMap A B i := by
  simp [idealMul]

/-- For `j ∈ J` the action of `j` on `B ⊗_A J` factors through the multiplication map:
`j • x = 1 ⊗ j`-multiplied by `μ x`. -/
lemma algebraMap_smul_eq {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)
    (j : J) (x : B ⊗[A] J) :
    (algebraMap A B j : B) • x = (idealMul J x) ⊗ₜ[A] j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [smul_add, hu, hv, map_add, TensorProduct.add_tmul]
  | tmul b i =>
    rw [TensorProduct.smul_tmul', idealMul_tmul, smul_eq_mul, mul_comm (algebraMap A B _) b]
    have e1 : b * algebraMap A B (j : A) = (j : A) • b := by rw [Algebra.smul_def, mul_comm]
    have e2 : b * algebraMap A B (i : A) = (i : A) • b := by rw [Algebra.smul_def, mul_comm]
    rw [e1, e2, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    congr 1
    ext
    simp [mul_comm]

/-- **Lemma 4.3, Tor-kernel step.** The kernel of `B ⊗_A J → B` (a `Tor₁(A/J, B)`) is killed by
`J B`. Applied to the ideal `J^N` this is "killed by `a_n^N`". -/
theorem smul_eq_zero_of_mul_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (x : B ⊗[A] J) (hx : idealMul J x = 0) (y : B)
    (hy : y ∈ J.map (algebraMap A B)) : y • x = 0 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    have := algebraMap_smul_eq (B := B) J ⟨j, hj⟩ x
    rw [hx, TensorProduct.zero_tmul] at this
    exact this
  | zero => exact zero_smul _ x
  | add u v _ _ hu hv => rw [add_smul, hu, hv, zero_add]
  | smul b u _ hu => rw [smul_eq_mul, mul_smul, hu, smul_zero]

/-- **Lemma 4.3, well-definedness of `s_f = Ψ ν_g⁻¹(1)`.** If `g` kills `ker ν` and `ν n = ν n'` then
`g Ψ n = g Ψ n'`. -/
theorem deligne_wellDefined {C N D : Type*} [CommRing C] [AddCommGroup N] [Module C N]
    [AddCommGroup D] [Module C D] (ν : N →ₗ[C] C) (Ψ : N →ₗ[C] D) (g : C)
    (hg : ∀ x, ν x = 0 → g • x = 0) (n n' : N) (h : ν n = ν n') : g • Ψ n = g • Ψ n' := by
  have : g • (n - n') = 0 := hg _ (by rw [map_sub, h, sub_self])
  rw [← map_smul, ← map_smul, ← sub_eq_zero, ← map_sub, ← smul_sub, this, map_zero]

/-- The Krull part of **Lemma 3.3** at `N = C`: if a homogeneous ideal `m` separates homogeneous
elements, then `⋂ mⁿ = 0`. -/
theorem iInf_pow_eq_bot {ι σ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ C]
    [AddSubmonoidClass σ C] (𝒞 : ι → σ) [GradedRing 𝒞] (m : Ideal C) (hm : m.IsHomogeneous 𝒞)
    (hsep : ∀ d, ∀ c ∈ 𝒞 d, (∀ n : ℕ, c ∈ m ^ n) → c = 0) : (⨅ n : ℕ, m ^ n) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro c hc
  have hc' : ∀ n : ℕ, c ∈ m ^ n := fun n => (Ideal.mem_iInf.mp hc) n
  have hpow : ∀ n : ℕ, (m ^ n).IsHomogeneous 𝒞 := fun n => by
    induction n with
    | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact (⊤ : HomogeneousIdeal 𝒞).isHomogeneous
    | succ n ih =>
      rw [pow_succ]
      exact Ideal.IsHomogeneous.mul ih hm
  have hz : ∀ d, (DirectSum.decompose 𝒞 c d : C) = 0 := fun d =>
    hsep d _ (SetLike.coe_mem _) fun n => (hpow n) d (hc' n)
  have : DirectSum.decompose 𝒞 c = 0 := by
    ext d
    simpa using hz d
  simpa using (DirectSum.decompose 𝒞).injective (this.trans (DirectSum.decompose_zero 𝒞).symm)

end Algebra

/-- **Fill (a), ring form.** On `φₙ⁻¹(U)` the extension `ψ` of `f` restricts to multiplication by
`f̄ = φₙ^* f`, so if `ν x = g` with `g` invertible in `L`, then `s_f = Ψ(x)/g` maps to `f̄` in `L`. -/
theorem deligne_compat {C N L : Type*} [CommRing C] [CommRing L] [AddCommGroup N] [Module C N]
    (π : C →+* L) (ν Ψ : N →ₗ[C] C) (fbar : L) (h : ∀ x, π (Ψ x) = fbar * π (ν x)) (x : N) (g : C)
    (hx : ν x = g) (u : Lˣ) (hu : (u : L) = π g) : π (Ψ x) * (↑u⁻¹ : L) = fbar := by
  rw [h, hx, ← hu, mul_assoc, Units.mul_inv, mul_one]

/-! ### Equalizers in separated spaces -/

section Geometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The equalizer of two points of a separated space is closed. -/
theorem exists_eqLocus {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : Space.IsSeparatedOver B S hS X)
    (W : BigFppfOver B S hS) (p q : X.obj (op W)) :
    ∃ (E : BigFppfOver B S hS) (i : E ⟶ W), AlgebraicGeometry.IsClosedImmersion ((SCH).map i) ∧
      ∀ (W' : BigFppfOver B S hS) (t : W' ⟶ W),
        X.map t.op p = X.map t.op q ↔ ∃ u : W' ⟶ E, u ≫ i = t := by
  let g : yoneda.obj W ⟶ X ⨯ X := prod.lift (yonedaEquiv.symm p) (yonedaEquiv.symm q)
  have hrep := hX.rep
  have hpb := hrep.isPullback g
  refine ⟨hrep.pullback g, hrep.snd g, hX.property_snd g, fun W' t => ?_⟩
  have hnat : ∀ {V : BigFppfOver B S hS} (t : V ⟶ W) (x : X.obj (op W)),
      yoneda.map t ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.map t.op x) := fun t x => by
    apply yonedaEquiv.injective
    simp [yonedaEquiv_apply]
  constructor
  · intro h
    have hc : yoneda.map t ≫ g = yonedaEquiv.symm (X.map t.op p) ≫ diag X := by
      ext1
      · simp [g, hnat, diag]
      · simp [g, hnat, diag, h]
    let l := hpb.lift (yonedaEquiv.symm (X.map t.op p)) (yoneda.map t) hc.symm
    refine ⟨yoneda.preimage l, yoneda.map_injective ?_⟩
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]
    exact hpb.lift_snd _ _ _
  · rintro ⟨u, rfl⟩
    have hw := hpb.w
    have h1 := congrArg (· ≫ prod.fst) hw
    have h2 := congrArg (· ≫ prod.snd) hw
    simp only [Category.assoc, g, prod.lift_fst, prod.lift_snd, diag] at h1 h2
    have h12 : yoneda.map (hrep.snd g) ≫ yonedaEquiv.symm p =
        yoneda.map (hrep.snd g) ≫ yonedaEquiv.symm q := by
      simpa using h1.symm.trans h2
    apply yonedaEquiv.symm.injective
    rw [← hnat, ← hnat, CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, h12]

/-- An immersed scheme over an object `W` of the site, as an object of the site. -/
noncomputable def immObj (W : BigFppfOver B S hS) {Z : Scheme.{u}} (f : Z ⟶ (SCH).obj W)
    [AlgebraicGeometry.IsImmersion f] : BigFppfOver B S hS :=
  Over.mk (⟨f ≫ W.hom.hom⟩ :
    B.obj (Space.contains_of_isImmersion B W.left.2 f) ⟶ B.obj hS)

/-- The inclusion of `AlgMag.Chart.immObj`. -/
noncomputable def immι (W : BigFppfOver B S hS) {Z : Scheme.{u}} (f : Z ⟶ (SCH).obj W)
    [AlgebraicGeometry.IsImmersion f] : immObj W f ⟶ W :=
  Over.homMk ⟨f⟩ rfl

/-- `Spec R/I → Y` for `Y` affine with `R = Γ(Y, ⊤)`. -/
noncomputable def closedι (Y : Scheme.{u}) [IsAffine Y] (I : Ideal Γ(Y, ⊤)) :
    Spec (.of (Γ(Y, ⊤) ⧸ I)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.isoSpec.inv

instance (Y : Scheme.{u}) [IsAffine Y] (I : Ideal Γ(Y, ⊤)) :
    AlgebraicGeometry.IsClosedImmersion (closedι Y I) := by
  have : AlgebraicGeometry.IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  unfold closedι; infer_instance

lemma closedι_appTop_eq_zero {Y : Scheme.{u}} [IsAffine Y] (I : Ideal Γ(Y, ⊤)) (r : Γ(Y, ⊤))
    (h : (closedι Y I).appTop r = 0) : r ∈ I := by
  have e : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ Y.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    simp
  have hinv : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := (Iso.hom_comp_eq_id _).mp e
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have this : (closedι Y I).appTop r = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    rw [closedι, Scheme.Hom.comp_appTop, hinv]; rfl
  have h1 := ConcreteCategory.congr_hom hnat ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← this, h, map_zero] at h1
  have h2 : (Ideal.Quotient.mk I) r = 0 := by
    have h3 : (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) = r := by simp
    erw [h3] at h1
    exact h1.symm
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

lemma basicOpen_ι_appTop_eq_zero {Y : Scheme.{u}} [IsAffine Y] (g r : Γ(Y, ⊤))
    (h : (Y.basicOpen g).ι.appTop r = 0) : ∃ n : ℕ, g ^ n * r = 0 := by
  have hloc := (isAffineOpen_top Y).isLocalization_basicOpen g
  have key := Scheme.Opens.ι_app (Y.basicOpen g) ⊤
  have hle : Y.basicOpen g ≤ (Y.basicOpen g).ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).ge
  have hV : Y.presheaf.map (homOfLE (le_top : (Y.basicOpen g).ι ''ᵁ ⊤ ≤ ⊤)).op r = 0 := by
    have h' := h
    change ((Y.basicOpen g).ι.app ⊤) r = 0 at h'
    rw [key] at h'
    exact h'
  have h0 : algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g) r = 0 := by
    have : algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g) r =
        Y.presheaf.map (homOfLE hle).op
          (Y.presheaf.map (homOfLE (le_top : (Y.basicOpen g).ι ''ᵁ ⊤ ≤ ⊤)).op r) := by
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]; rfl
    rw [this, hV, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ r).mp h0
  exact ⟨n, hm⟩

lemma appTop_eq_zero_of_comp {A D E : Scheme.{u}} (u : A ⟶ E) (i : E ⟶ D) (f : A ⟶ D)
    (hc : u ≫ i = f) (r : Γ(D, ⊤)) (hr : i.appTop r = 0) : f.appTop r = 0 := by
  subst hc
  rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hr, map_zero]

/-- If a closed immersion `E → W` onto the equalizer of `p, q` has injective map on global sections,
then `p = q`. -/
lemma eq_of_ker_eq_bot {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W E : BigFppfOver B S hS}
    [IsAffine ((SCH).obj W)] {p q : X.obj (op W)} (i : E ⟶ W)
    (hi : AlgebraicGeometry.IsClosedImmersion ((SCH).map i))
    (hE : ∀ (W' : BigFppfOver B S hS) (t : W' ⟶ W),
      X.map t.op p = X.map t.op q ↔ ∃ u : W' ⟶ E, u ≫ i = t)
    (hinj : ∀ r, ((SCH).map i).appTop r = 0 → r = 0) : p = q := by
  have hiso : IsIso ((SCH).map i) := by
    apply IsClosedImmersion.isIso_of_injective_of_isAffine
    exact (injective_iff_map_eq_zero _).mpr hinj
  have hw : (inv ((SCH).map i)) ≫ E.hom.hom = W.hom.hom := by
    have : (SCH).map i ≫ W.hom.hom = E.hom.hom := congrArg (fun f => f.hom) (Over.w i)
    rw [← this, IsIso.inv_hom_id_assoc]
  let u : W ⟶ E := Over.homMk ⟨inv ((SCH).map i)⟩ (by
    apply InducedCategory.hom_ext; exact hw)
  have hu : u ≫ i = 𝟙 W := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _
  have := (hE W (𝟙 W)).mpr ⟨u, hu⟩
  simpa using this

/-- **Equalizer killing** (§4, the checks after Lemma 4.5). Let `X` be separated, `W = Spec R` affine,
`R` a flat algebra over a noetherian ring `C`, and `a` an ideal generated by the set `gens`.
Two points of `X` over `W` that agree on each `D(g)`, `g ∈ gens`, and on each `V(a^k R)` are equal. -/
theorem eq_of_agree_basicOpen_of_agree_thickening
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : Space.IsSeparatedOver B S hS X)
    (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)]
    {C : Type*} [CommRing C] [IsNoetherianRing C] [Algebra C Γ((SCH).obj W, ⊤)]
    [Module.Flat C Γ((SCH).obj W, ⊤)] (a : Ideal C) (gens : Set C) (hgens : a = Ideal.span gens)
    (p q : X.obj (op W))
    (hD : ∀ g ∈ gens, X.map (immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op p =
      X.map (immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op q)
    (hV : ∀ k : ℕ, X.map (immι W (closedι ((SCH).obj W)
        ((a ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op p =
      X.map (immι W (closedι ((SCH).obj W)
        ((a ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op q) : p = q := by
  obtain ⟨E, i, hi, hE⟩ := exists_eqLocus hX W p q
  refine eq_of_ker_eq_bot i hi hE fun r hr => ?_
  let Ann : Ideal C :=
    { carrier := {c | algebraMap C Γ((SCH).obj W, ⊤) c * r = 0}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq] at hu hv ⊢
        rw [map_add, add_mul, hu, hv, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c u hu => by
        simp only [Set.mem_ofPred_eq] at hu ⊢
        rw [smul_eq_mul, map_mul, mul_assoc, hu, mul_zero] }
  have hle : a ≤ Ann.radical := by
    rw [hgens, Ideal.span_le]
    intro g hg
    obtain ⟨u, hu⟩ := (hE _ _).mp (hD g hg)
    have hc : (SCH).map u ≫ (SCH).map i =
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι := by
      rw [← CategoryTheory.Functor.map_comp, hu]; rfl
    obtain ⟨n, hn⟩ := basicOpen_ι_appTop_eq_zero (Y := (SCH).obj W)
      (algebraMap C Γ((SCH).obj W, ⊤) g) r (appTop_eq_zero_of_comp _ _ _ hc r hr)
    exact ⟨n, by change algebraMap C _ (g ^ n) * r = 0; rw [map_pow]; exact hn⟩
  obtain ⟨s, hs⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian a)
  refine separating a s r (fun x hx => hs hx) fun k => closedι_appTop_eq_zero _ r ?_
  obtain ⟨u, hu⟩ := (hE _ _).mp (hV k)
  have hc : (SCH).map u ≫ (SCH).map i = closedι ((SCH).obj W)
      ((a ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))) := by
    rw [← CategoryTheory.Functor.map_comp, hu]; rfl
  exact appTop_eq_zero_of_comp _ _ _ hc r hr

/-- **Theorem 4.1, uniqueness**, in the form: two points of a separated space over `Spec R` that agree
on `V(J n)` for a family of ideals with zero intersection are equal. With `J n = mⁿ` and
`AlgMag.Chart.iInf_pow_eq_bot` this is the uniqueness for a complete pair. -/
theorem eq_of_agree_of_iInf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Space.IsSeparatedOver B S hS X) (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)]
    (J : ℕ → Ideal Γ((SCH).obj W, ⊤)) (hJ : (⨅ n, J n) = ⊥) (p q : X.obj (op W))
    (h : ∀ n, X.map (immι W (closedι ((SCH).obj W) (J n))).op p =
      X.map (immι W (closedι ((SCH).obj W) (J n))).op q) : p = q := by
  obtain ⟨E, i, hi, hE⟩ := exists_eqLocus hX W p q
  refine eq_of_ker_eq_bot i hi hE fun r hr => ?_
  have hmem : r ∈ ⨅ n, J n := by
    refine Ideal.mem_iInf.mpr fun n => closedι_appTop_eq_zero _ r ?_
    obtain ⟨u, hu⟩ := (hE _ _).mp (h n)
    have hc : (SCH).map u ≫ (SCH).map i = closedι ((SCH).obj W) (J n) := by
      rw [← CategoryTheory.Functor.map_comp, hu]; rfl
    exact appTop_eq_zero_of_comp _ _ _ hc r hr
  rw [hJ] at hmem
  simpa using hmem

/-! ### Bhatt's theorems as named propositions -/

/-- **Bhatt, arXiv:1404.7483, Theorem 1.1** for `X`: "If `A` is a ring which is `I`-adically complete
for some ideal `I`, and `X` is a qcqs algebraic space, then `X(A) ≃ lim X(A/Iⁿ)`." -/
def BhattAlgebraization (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)] (I : Ideal Γ((SCH).obj W, ⊤))
    [IsAdicComplete I Γ((SCH).obj W, ⊤)]
    (x : ∀ n : ℕ, X.obj (op (immObj W (closedι ((SCH).obj W) (I ^ n))))),
    (∀ (n m : ℕ) (t : immObj W (closedι ((SCH).obj W) (I ^ n)) ⟶
        immObj W (closedι ((SCH).obj W) (I ^ m))),
        t ≫ immι W _ = immι W _ → X.map t.op (x m) = x n) →
    ∃! y : X.obj (op W), ∀ n, X.map (immι W (closedι ((SCH).obj W) (I ^ n))).op y = x n

/-- The open complement of `V(I)` in an affine scheme. -/
noncomputable def complOpen (Y : Scheme.{u}) (I : Ideal Γ(Y, ⊤)) : Y.Opens :=
  ⨆ g : I, Y.basicOpen (g : Γ(Y, ⊤))

/-- **Bhatt, arXiv:1404.7483, Theorem 1.4(1)** for `X`, in the case of a flat map of affine schemes
`π : Y → T` (flatness gives the Tor-independence) and `Z = V(I)`, `I` finitely generated, with
`π⁻¹(Z) ≅ Z`: the fibre square of `Y \ π⁻¹(Z) → Y`, `T \ Z → T` is a pushout. -/
def BhattPushoutFlat (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (T Y : BigFppfOver B S hS) [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj Y)] (π : Y ⟶ T)
    (I : Ideal Γ((SCH).obj T, ⊤)), I.FG → ((SCH).map π).appTop.hom.Flat →
    Function.Bijective (Ideal.quotientMap (I.map ((SCH).map π).appTop.hom)
      ((SCH).map π).appTop.hom Ideal.le_comap_map) →
    ∀ (τ : X.obj (op (immObj T (complOpen ((SCH).obj T) I).ι))) (θ : X.obj (op Y)),
      (∀ (W' : BigFppfOver B S hS) (s : W' ⟶ immObj T (complOpen ((SCH).obj T) I).ι) (s' : W' ⟶ Y),
        s ≫ immι T _ = s' ≫ π → X.map s.op τ = X.map s'.op θ) →
      ∃! φ : X.obj (op T), X.map (immι T _).op φ = τ ∧ X.map π.op φ = θ

end Geometry

end AlgMag.Chart
