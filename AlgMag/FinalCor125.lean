/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedCor

/-!
# Corollary 12.5 of *Algebraic Magnetism*: the global form

`cor125` of `Sec12PrintedCor` works over each affine `T`, by the printed proof of Theorem 12.4
(`printed_ring`), with the section `s` of `I/I² → I` chosen. Here `π` is the explicit augmentation, and the
section is the one given by the irreducible elements of `N`: `tMap (X^n) = 0` for `n` reducible, and the
`tMap (X^i)`, `i` irreducible, are a basis. Then `phi_injective` of the printed proof shows that
`ℕ^{(Irr N)} → N` is bijective as soon as `S` is nonempty, so `𝔸(N)_S ≅ 𝔸(ℕ^{(Irr N)})_S` over `S`, globally.
So the vector bundle is trivial: this is stronger than the print, and it is what makes the local
statements global.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.Final

open AlgMag.GB AlgMag.Sec12Printed

variable {M : Type u} [AddCommGroup M] (N : AddSubmonoid M)

/-- The irreducible elements of `N`. -/
abbrev Irr : Type u := {n : N // n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0}

/-- `ℕ^{(Irr N)} → N`. -/
def gen : (Irr N →₀ ℕ) →+ N := Finsupp.liftAddHom fun i => multiplesHom N i.1

@[simp] lemma gen_single (i : Irr N) (k : ℕ) : gen N (Finsupp.single i k) = k • i.1 := by
  simp [gen]

variable (R : Type u) [CommRing R]

/-- The augmentation `R[N] → R`, `X^n ↦ 0` for `n ≠ 0`. `N` is sharp, as in Corollary 12.5. -/
def augN (hzero : ∀ n n' : N, n + n' = 0 → n = 0) : AddMonoidAlgebra R N →ₐ[R] R :=
  AddMonoidAlgebra.lift R R N
    { toFun := fun n => if Multiplicative.toAdd n = 0 then 1 else 0
      map_one' := if_pos rfl
      map_mul' := fun a b => by
        by_cases ha : Multiplicative.toAdd a = 0
        · by_cases hb : Multiplicative.toAdd b = 0
          · simp [ha, hb]
          · have : Multiplicative.toAdd (a * b) ≠ 0 := fun e => hb
              (hzero (Multiplicative.toAdd b) (Multiplicative.toAdd a) (by rw [add_comm]; exact e))
            simp [ha, hb]
        · have : Multiplicative.toAdd (a * b) ≠ 0 := fun e =>
            ha (hzero (Multiplicative.toAdd a) (Multiplicative.toAdd b) e)
          simp [ha]
          intro e
          exact absurd (hzero _ _ e) ha }

variable {N R} (hzero : ∀ n n' : N, n + n' = 0 → n = 0)

lemma augN_single (n : N) (c : R) :
    augN N R hzero (AddMonoidAlgebra.single n c) = c * (if n = 0 then 1 else 0) := by
  simp [augN, AddMonoidAlgebra.lift_single]

variable (N R)

/-- The coefficients at the irreducible elements. -/
def coefIrr : AddMonoidAlgebra R N →ₗ[R] (Irr N →₀ R) :=
  (Finsupp.lsum R fun n : N =>
    if h : n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0 then
      LinearMap.toSpanSingleton R (Irr N →₀ R) (Finsupp.single (⟨n, h⟩ : Irr N) (1 : R))
    else 0) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- `e_i ↦ X^i`. -/
def monIrr : (Irr N →₀ R) →ₗ[R] AddMonoidAlgebra R N :=
  Finsupp.linearCombination R fun i : Irr N => AddMonoidAlgebra.single i.1 1

variable {N R}

lemma coefIrr_single_irr (i : Irr N) (c : R) :
    coefIrr N R (AddMonoidAlgebra.single i.1 c) = Finsupp.single i c := by
  have h := i.2
  have : (AddMonoidAlgebra.coeffLinearEquiv R) (AddMonoidAlgebra.single i.1 c) =
      Finsupp.single i.1 c := rfl
  simp only [coefIrr, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Finsupp.lsum_single]
  rw [dif_pos h, LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma coefIrr_single_not {n : N} (h : ¬ (n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0)) (c : R) :
    coefIrr N R (AddMonoidAlgebra.single n c) = 0 := by
  have : (AddMonoidAlgebra.coeffLinearEquiv R) (AddMonoidAlgebra.single n c) =
      Finsupp.single n c := rfl
  simp only [coefIrr, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Finsupp.lsum_single]
  rw [dif_neg h]
  rfl

lemma single_mem_augI {n : N} (hn : n ≠ 0) (c : R) :
    AddMonoidAlgebra.single n c ∈ augI (augN N R hzero) := by
  change augN N R hzero _ = 0
  rw [augN_single, if_neg hn, mul_zero]

lemma augI_le_span : augI (augN N R hzero) ≤
    Ideal.span {b | ∃ n : N, n ≠ 0 ∧ b = AddMonoidAlgebra.single n (1 : R)} := by
  intro x hx
  have key : ∀ y : AddMonoidAlgebra R N, y - algebraMap R _ (augN N R hzero y) ∈
      Ideal.span {b | ∃ n : N, n ≠ 0 ∧ b = AddMonoidAlgebra.single n (1 : R)} := by
    intro y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      have := Ideal.add_mem _ ha hb
      convert this using 1
      simp only [map_add]
      ring
    | single n c =>
      by_cases hn : n = 0
      · subst hn
        rw [augN_single, if_pos rfl, mul_one]
        have : algebraMap R (AddMonoidAlgebra R N) c = AddMonoidAlgebra.single 0 c := rfl
        rw [this, sub_self]
        exact Ideal.zero_mem _
      · rw [augN_single, if_neg hn, mul_zero, map_zero, sub_zero]
        have e : AddMonoidAlgebra.single n c =
            AddMonoidAlgebra.single (0 : N) c * AddMonoidAlgebra.single n (1 : R) := by
          simp [AddMonoidAlgebra.single_mul_single]
        rw [e]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, hn, rfl⟩)
  have := key x
  have h0 : augN N R hzero x = 0 := hx
  simpa [h0] using this

include hzero in
lemma coefIrr_of_mem_sq {a : AddMonoidAlgebra R N} (ha : a ∈ (augI (augN N R hzero)) ^ 2) :
    coefIrr N R a = 0 := by
  have hle : (augI (augN N R hzero)) ^ 2 ≤ Ideal.span
      {b | ∃ n m : N, n ≠ 0 ∧ m ≠ 0 ∧ b = AddMonoidAlgebra.single (n + m) (1 : R)} := by
    rw [pow_two]
    refine (Ideal.mul_mono (augI_le_span hzero) (augI_le_span hzero)).trans ?_
    rw [Ideal.span_mul_span']
    refine Ideal.span_mono ?_
    rintro _ ⟨_, ⟨n, hn, rfl⟩, _, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨n, m, hn, hm, by simp [AddMonoidAlgebra.single_mul_single]⟩
  have main : ∀ x ∈ Ideal.span
      {b | ∃ n m : N, n ≠ 0 ∧ m ≠ 0 ∧ b = AddMonoidAlgebra.single (n + m) (1 : R)},
      ∀ c : AddMonoidAlgebra R N, coefIrr N R (c * x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add, hx, hy, add_zero]
    | smul c' x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    | mem x hx =>
      obtain ⟨n, m, hn, hm, rfl⟩ := hx
      intro c
      induction c using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => rw [add_mul, map_add, ha, hb, add_zero]
      | single k r =>
        rw [AddMonoidAlgebra.single_mul_single]
        refine coefIrr_single_not (fun h => ?_) _
        have e : k + (n + m) = n + (k + m) := by abel
        rcases h.2 n (k + m) e with e | e
        · exact hn e
        · have hk := hzero k m e
          exact hm (by simpa [hk] using e)
  simpa using main a (hle ha) 1

variable (R)

/-- The map `I/I² → (Irr N →₀ R)`. -/
def coefP : Conormal (augN N R hzero) →ₗ[R] (Irr N →₀ R) :=
  (LinearMap.ker (tMap (augN N R hzero))).liftQ (coefIrr N R) (by
    intro b hb
    have hb' : tMap (augN N R hzero) b = 0 := hb
    have hm : b - algebraMap R _ (augN N R hzero b) ∈ (augI (augN N R hzero)) ^ 2 := by
      simp only [tMap, LinearMap.coe_mk, AddHom.coe_mk] at hb'
      exact (Ideal.toCotangent_eq_zero _ _).1 hb'
    have h := coefIrr_of_mem_sq hzero hm
    have h0 : coefIrr N R (algebraMap R _ (augN N R hzero b)) = 0 :=
      coefIrr_single_not (n := 0) (fun h => h.1 rfl) _
    rw [map_sub, h0, sub_zero] at h
    exact h) ∘ₗ
  (LinearMap.quotKerEquivOfSurjective _ (tMap_surjective (augN N R hzero))).symm.toLinearMap

variable {R}

lemma coefP_tMap (b : AddMonoidAlgebra R N) :
    coefP R hzero (tMap (augN N R hzero) b) = coefIrr N R b := by
  have : (LinearMap.quotKerEquivOfSurjective _ (tMap_surjective (augN N R hzero))).symm
      (tMap (augN N R hzero) b) = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [coefP, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
  rfl

variable (R)

/-- The section of the printed proof, given by the irreducibles. -/
def sIrr : Conormal (augN N R hzero) →ₗ[R] AddMonoidAlgebra R N := monIrr N R ∘ₗ coefP R hzero

variable {R}

lemma tMap_single_not {n : N} (h : ¬ (n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0)) (c : R) :
    tMap (augN N R hzero) (AddMonoidAlgebra.single n c) = 0 := by
  by_cases hn : n = 0
  · subst hn; exact tMap_algebraMap _ c
  · push_neg at h
    obtain ⟨a, b, e, ha, hb⟩ := h hn
    have e' : AddMonoidAlgebra.single n c =
        AddMonoidAlgebra.single a c * AddMonoidAlgebra.single b (1 : R) := by
      simp [AddMonoidAlgebra.single_mul_single, e]
    rw [e', tMap_mul, augN_single, augN_single, if_neg ha, if_neg hb]
    simp

lemma tMap_sIrr (p : Conormal (augN N R hzero)) : tMap (augN N R hzero) (sIrr R hzero p) = p := by
  obtain ⟨b, rfl⟩ := tMap_surjective _ p
  simp only [sIrr, LinearMap.comp_apply, coefP_tMap]
  induction b using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n c =>
    by_cases h : n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0
    · have := coefIrr_single_irr (R := R) (⟨n, h⟩ : Irr N) c
      erw [this]
      have e : AddMonoidAlgebra.single n c = c • AddMonoidAlgebra.single n (1 : R) := by simp
      have e2 : monIrr N R (Finsupp.single (⟨n, h⟩ : Irr N) c) =
          c • AddMonoidAlgebra.single n (1 : R) := Finsupp.linearCombination_single _ _ _
      rw [e2, ← e]
    · rw [coefIrr_single_not h, map_zero, map_zero, tMap_single_not hzero h]

lemma π_sIrr (p : Conormal (augN N R hzero)) : augN N R hzero (sIrr R hzero p) = 0 := by
  have : ∀ v : Irr N →₀ R, augN N R hzero (monIrr N R v) = 0 := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single i c =>
      simp only [monIrr, Finsupp.linearCombination_single, map_smul, augN_single, if_neg i.2.1]
      simp
  exact this _

include hzero in
/-- `ψ`: `X_i ↦ [X^i]`, and its left inverse. -/
theorem gen_injective_of_smooth [Nontrivial R] [Algebra.FormallySmooth R (AddMonoidAlgebra R N)] :
    Function.Injective (gen N) := by
  let S' := SymmetricAlgebra R (Conormal (augN N R hzero))
  let Φ : S' →ₐ[R] AddMonoidAlgebra R N := SymmetricAlgebra.lift (sIrr R hzero)
  have hΦ : Function.Injective Φ := phi_injective _ (π_sIrr hzero) (tMap_sIrr hzero)
  let ψ : MvPolynomial (Irr N) R →ₐ[R] S' := MvPolynomial.aeval fun i =>
    SymmetricAlgebra.ι R _ (tMap (augN N R hzero) (AddMonoidAlgebra.single i.1 1))
  let inv : S' →ₐ[R] MvPolynomial (Irr N) R := SymmetricAlgebra.lift
    ((Finsupp.linearCombination R fun i : Irr N => (MvPolynomial.X i : MvPolynomial (Irr N) R)) ∘ₗ
      coefP R hzero)
  have hψ : Function.Injective ψ := by
    have : inv.comp ψ = AlgHom.id R _ := by
      refine MvPolynomial.algHom_ext fun i => ?_
      simp only [AlgHom.comp_apply, ψ, MvPolynomial.aeval_X, inv, AlgHom.id_apply]
      erw [SymmetricAlgebra.lift_ι_apply]
      rw [LinearMap.comp_apply, coefP_tMap, coefIrr_single_irr, Finsupp.linearCombination_single, one_smul]
    exact Function.LeftInverse.injective (g := inv) fun x => DFunLike.congr_fun this x
  have hmon : ∀ x : Irr N →₀ ℕ, Φ (ψ (MvPolynomial.monomial x 1)) =
      AddMonoidAlgebra.single (gen N x) (1 : R) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero =>
      have e : MvPolynomial.monomial (0 : Irr N →₀ ℕ) (1 : R) = 1 := rfl
      rw [e, map_one, map_one, map_zero]; rfl
    | add a b ha hb =>
      have e : MvPolynomial.monomial (a + b) (1 : R) =
          MvPolynomial.monomial a 1 * MvPolynomial.monomial b 1 := by
        simp [MvPolynomial.monomial_mul]
      rw [e, map_mul, map_mul, ha, hb, AddMonoidAlgebra.single_mul_single, map_add, one_mul]
    | single i k =>
      have e : MvPolynomial.monomial (Finsupp.single i k) (1 : R) = (MvPolynomial.X i) ^ k := by
        simp [MvPolynomial.X_pow_eq_monomial]
      have hX : Φ (ψ (MvPolynomial.X i)) = AddMonoidAlgebra.single i.1 (1 : R) := by
        simp only [ψ, MvPolynomial.aeval_X, Φ]
        erw [SymmetricAlgebra.lift_ι_apply]
        rw [sIrr, LinearMap.comp_apply, coefP_tMap, coefIrr_single_irr]
        exact (Finsupp.linearCombination_single _ _ _).trans (one_smul _ _)
      rw [e, map_pow, map_pow, hX, AddMonoidAlgebra.single_pow, gen_single, one_pow]
  intro x y hxy
  have h1 : Φ (ψ (MvPolynomial.monomial x 1)) = Φ (ψ (MvPolynomial.monomial y 1)) := by
    rw [hmon, hmon, hxy]
  exact MvPolynomial.monomial_left_injective (R := R) one_ne_zero (hψ (hΦ h1))

lemma gen_surjective {w : N →+ ℕ} (hw : ∀ n : N, w n = 0 → n = 0) : Function.Surjective (gen N) := by
  have main : ∀ (k : ℕ) (n : N), w n = k → n ∈ Set.range (gen N) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hn
      by_cases h : n ≠ 0 ∧ ∀ a b : N, n = a + b → a = 0 ∨ b = 0
      · exact ⟨Finsupp.single ⟨n, h⟩ 1, (gen_single N ⟨n, h⟩ 1).trans (one_nsmul _)⟩
      · by_cases h0 : n = 0
        · exact ⟨0, by simp [h0]⟩
        · push_neg at h
          obtain ⟨a, b, e, ha, hb⟩ := h h0
          have hwa : w a ≠ 0 := fun x => ha (hw a x)
          have hwb : w b ≠ 0 := fun x => hb (hw b x)
          have he : w a + w b = k := by rw [← hn, e, map_add]
          obtain ⟨x, hx⟩ := ih (w a) (by omega) a rfl
          obtain ⟨y, hy⟩ := ih (w b) (by omega) b rfl
          exact ⟨x + y, by rw [map_add, hx, hy, e]⟩
  exact fun n => main _ n rfl

variable {S : Scheme.{u}} (N)

/-- **Corollary 12.5**, global form. `N` is finitely generated and sharp, `S` is nonempty. If `𝔸(N)_S → S`
is smooth, then `ℕ^{(Irr N)} → N` is an isomorphism, so `𝔸(N)_S → 𝔸(ℕ^{(Irr N)})_S` is an isomorphism over
`S`: `𝔸(N)_S → S` is a (trivial) vector bundle. Over the empty scheme there is nothing to prove. -/
theorem cor125_global (hfg : N.FG) (hsharp : ∀ x ∈ N, -x ∈ N → x = 0) [Smooth (A N S).hom]
    (x : S) : ∃ e : (Irr N →₀ ℕ) ≃+ N, e.toAddMonoidHom = gen N ∧ IsIso (Amap (gen N) S) := by
  have hface : IsFace (⊥ : AddSubmonoid M) N := by
    refine ⟨bot_le, fun {a b} ha hb h => ?_⟩
    have e : a + b = 0 := h
    have ha0 : a = 0 := hsharp a ha (by rwa [neg_eq_of_add_eq_zero_right e])
    have hb0 : b = 0 := by simpa [ha0] using e
    exact ⟨ha0, hb0⟩
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hface hfg
  have hzero : ∀ n n' : N, n + n' = 0 → n = 0 := by
    rintro ⟨n, hn⟩ ⟨n', hn'⟩ e
    have e' : n + n' = 0 := congrArg Subtype.val e
    exact Subtype.ext (hsharp n hn (by rwa [neg_eq_of_add_eq_zero_right e']))
  let k := S.residueField x
  let T : Over S := Over.mk (S.fromSpecResidueField x)
  haveI : IsAffine T.left := by dsimp [T]; infer_instance
  haveI : Nontrivial Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso k).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hsm : Smooth (magnetπ N T.left) :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_magnet N T) inferInstance
  have hsm₂ : Smooth (Spec.map (magnetConst N T.left)) := by
    have e : Spec.map (magnetConst N T.left) = magnetπ N T.left ≫ T.left.isoSpec.hom := by
      simp [magnetπ]
    rw [e]
    infer_instance
  have hR : (magnetConst N T.left).hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hsm₂
  have hS : Algebra.Smooth Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N) := by
    have : (magnetConst N T.left).hom = algebraMap Γ(T.left, ⊤) (AddMonoidAlgebra Γ(T.left, ⊤) N) := rfl
    rw [this] at hR
    exact (RingHom.smooth_algebraMap).1 hR
  have hinj := gen_injective_of_smooth (R := Γ(T.left, ⊤)) hzero
  have hsurj := gen_surjective (N := N) (w := w) fun n hn => Subtype.ext ((hw n).1 hn)
  let e : (Irr N →₀ ℕ) ≃+ N := AddEquiv.ofBijective (gen N) ⟨hinj, hsurj⟩
  refine ⟨e, AddMonoidHom.ext fun _ => rfl, ?_⟩
  have hc : ∀ {P Q R : Type u} [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid R] (φ : P →+ Q) (ψ : R →+ P),
      Amap φ S ≫ Amap ψ S = Amap (φ.comp ψ) S := by
    intro P Q R _ _ _ φ ψ
    refine (pts _).injective ?_
    rw [pts_comp_Amap]
    conv_lhs => rw [show Amap φ S = 𝟙 _ ≫ Amap φ S from (Category.id_comp _).symm, pts_comp_Amap]
    conv_rhs => rw [show Amap (φ.comp ψ) S = 𝟙 _ ≫ Amap (φ.comp ψ) S from (Category.id_comp _).symm, pts_comp_Amap]
    rfl
  have hid : ∀ {Q : Type u} [AddCommMonoid Q], Amap (AddMonoidHom.id Q) S = 𝟙 _ := by
    intro Q _
    refine (pts _).injective ?_
    conv_lhs => rw [show Amap (AddMonoidHom.id Q) S = 𝟙 _ ≫ Amap (AddMonoidHom.id Q) S from (Category.id_comp _).symm, pts_comp_Amap]
    rfl
  refine ⟨Amap e.symm.toAddMonoidHom S, ?_, ?_⟩
  · rw [hc, show (gen N).comp e.symm.toAddMonoidHom = AddMonoidHom.id N from
      AddMonoidHom.ext fun n => e.apply_symm_apply n, hid]
  · rw [hc, show e.symm.toAddMonoidHom.comp (gen N) = AddMonoidHom.id _ from
      AddMonoidHom.ext fun n => e.symm_apply_apply n, hid]

end AlgMag.Final

#print axioms AlgMag.Final.cor125_global
