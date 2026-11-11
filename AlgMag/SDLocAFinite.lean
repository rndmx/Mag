/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDLocABijective
import AlgMag.SDExistIsolate
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat

/-!
# Lemma D, Step 3 (iv): the corner `D = T/(1-e)` is finite, flat, finitely presented

Step 3 (iv) of the proof of Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, at
finite level ("`D` is étale and integral over `B`, hence finite étale and locally free"), base changed along
`R → R''`.
-/

open TensorProduct

universe u

namespace AlgMag.SD

/-- Step 3 (iv), abstractly: `T` integral over `S`, `T_x` étale over `S`, and `x` a unit on the corner of an idempotent `e`.
Then `T/(1-e)` is étale, finite and flat over `S`. -/
theorem SDLocA_corner {S T Tx : Type u} [CommRing S] [CommRing T] [CommRing Tx] [Algebra S T] [Algebra S Tx]
    [Algebra T Tx] [IsScalarTower S T Tx] {x : T} [IsLocalization.Away x Tx] [Algebra.Etale S Tx]
    [Algebra.IsIntegral S T] {e : T} (he : IsIdempotentElem e) (hu : ∃ u, e = u * x * e) :
    Algebra.Etale S (T ⧸ Ideal.span {1 - e}) ∧ Module.Finite S (T ⧸ Ideal.span {1 - e}) ∧
      Module.Flat S (T ⧸ Ideal.span {1 - e}) := by
  let J : Ideal T := Ideal.span {1 - e}
  let mk : T →+* T ⧸ J := Ideal.Quotient.mk J
  have hme : mk e = 1 := by
    have : mk (1 - e) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  obtain ⟨u, hu⟩ := hu
  have hxu : IsUnit (mk x) := by
    refine IsUnit.of_mul_eq_one (mk u) ?_
    have := congrArg mk hu
    rw [map_mul, map_mul, hme, mul_one] at this
    rw [mul_comm]
    exact this.symm
  let g : Tx →+* T ⧸ J := IsLocalization.Away.lift x hxu
  have hg : ∀ t : T, g (algebraMap T Tx t) = mk t := fun t => IsLocalization.Away.lift_eq x hxu t
  letI : Algebra Tx (T ⧸ J) := g.toAlgebra
  have hT : IsScalarTower T Tx (T ⧸ J) := .of_algebraMap_eq fun t => (hg t).symm
  have hS : IsScalarTower S Tx (T ⧸ J) := .of_algebraMap_eq fun s => by
    rw [IsScalarTower.algebraMap_apply S T Tx s]
    exact (hg _).symm
  let e' := algebraMap T Tx e
  have he' : IsIdempotentElem e' := he.map _
  have hsurj : Function.Surjective (algebraMap Tx (T ⧸ J)) := fun z => by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap T Tx t, hg t⟩
  have hker : RingHom.ker (algebraMap Tx (T ⧸ J)) = Ideal.span {1 - e'} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨⟨t, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers x) z
      simp only at hm
      have ht : mk t = 0 := by
        rw [← hg, ← hm, map_mul]
        have : g z = 0 := hz
        rw [this, zero_mul]
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 ht)
      have hun := IsLocalization.map_units Tx m
      have : z * algebraMap T Tx m ∈ Ideal.span {1 - e'} := by
        rw [hm, map_mul, map_sub, map_one]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      obtain ⟨w, hw⟩ := hun.exists_right_inv
      have h2 := Ideal.mul_mem_right w _ this
      rwa [mul_assoc, hw, mul_one] at h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change g (1 - e') = 0
      rw [map_sub, map_one, hg, hme, sub_self]
  haveI : IsLocalization.Away e' (T ⧸ J) := IsLocalization.away_of_isIdempotentElem he' hker hsurj
  haveI : Algebra.Etale Tx (T ⧸ J) := Algebra.Etale.of_isLocalizationAway e'
  have hE : Algebra.Etale S (T ⧸ J) := Algebra.Etale.comp S Tx (T ⧸ J)
  have hSm : Algebra.Smooth S (T ⧸ J) := (Algebra.Etale.iff_formallyUnramified_and_smooth.1 hE).2
  haveI : Algebra.IsIntegral S (T ⧸ J) := Algebra.IsIntegral.of_surjective
    (Ideal.Quotient.mkₐ S J) Ideal.Quotient.mk_surjective
  exact ⟨hE, Algebra.IsIntegral.finite, inferInstance⟩

variable (R B X R'' : Type u) [CommRing R] [CommRing B] [CommRing X] [CommRing R''] [Algebra R B] [Algebra R X]
  [Algebra B X] [IsScalarTower R B X] [Algebra R R'']

/-- The algebra structure of `R'' ⊗ X` over `R'' ⊗ B`. -/
noncomputable abbrev SDLocA_alg : Algebra (R'' ⊗[R] B) (R'' ⊗[R] X) :=
  (Algebra.TensorProduct.map (AlgHom.id R R'') (IsScalarTower.toAlgHom R B X)).toRingHom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The square `B → R'' ⊗ B`, `B → X`, with corner `R'' ⊗ X`, is a pushout. -/
theorem SDLocA_exists_equiv :
    letI := SDLocA_alg R B X R''
    Nonempty (((R'' ⊗[R] B) ⊗[B] X) ≃ₐ[R'' ⊗[R] B] (R'' ⊗[R] X)) := by
  letI := SDLocA_alg R B X R''
  letI : Algebra B (R'' ⊗[R] X) := .compHom _ (algebraMap B X)
  have : IsScalarTower B (R'' ⊗[R] B) (R'' ⊗[R] X) := .of_algebraMap_eq fun b => by
    change (1 : R'') ⊗ₜ[R] algebraMap B X b =
      (Algebra.TensorProduct.map (AlgHom.id R R'') (IsScalarTower.toAlgHom R B X)) ((1 : R'') ⊗ₜ[R] b)
    simp
  have : IsScalarTower R'' (R'' ⊗[R] B) (R'' ⊗[R] X) := .of_algebraMap_eq fun r => by
    change _ = (Algebra.TensorProduct.map (AlgHom.id R R'') (IsScalarTower.toAlgHom R B X)) (r ⊗ₜ[R] (1 : B))
    simp
  have : IsScalarTower B X (R'' ⊗[R] X) := .of_algebraMap_eq' rfl
  have : IsScalarTower R (R'' ⊗[R] B) (R'' ⊗[R] X) := .of_algebraMap_eq fun r => by
    change _ = (Algebra.TensorProduct.map (AlgHom.id R R'') (IsScalarTower.toAlgHom R B X)) (algebraMap R _ r)
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hL : Algebra.IsPushout R B R'' (R'' ⊗[R] B) := Algebra.IsPushout.symm inferInstance
  have hT : Algebra.IsPushout R X R'' (R'' ⊗[R] X) := Algebra.IsPushout.symm inferInstance
  have : Algebra.IsPushout B (R'' ⊗[R] B) X (R'' ⊗[R] X) :=
    Algebra.IsPushout.symm ((Algebra.IsPushout.comp_iff R B R'' (R'' ⊗[R] B) (T := X) (T' := R'' ⊗[R] X)).1 hT)
  exact ⟨Algebra.IsPushout.equiv B (R'' ⊗[R] B) X (R'' ⊗[R] X)⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `R'' ⊗ X` is étale over `R'' ⊗ B` when `X` is étale over `B`. -/
theorem SDLocA_etale_bc [Algebra.Etale B X] :
    letI := SDLocA_alg R B X R''
    Algebra.Etale (R'' ⊗[R] B) (R'' ⊗[R] X) := by
  letI := SDLocA_alg R B X R''
  obtain ⟨E⟩ := SDLocA_exists_equiv R B X R''
  exact Algebra.Etale.of_equiv E

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `R'' ⊗ X` is integral over `R'' ⊗ B` when `X` is integral over `B`. -/
theorem SDLocA_integral_bc [Algebra.IsIntegral B X] :
    letI := SDLocA_alg R B X R''
    Algebra.IsIntegral (R'' ⊗[R] B) (R'' ⊗[R] X) := by
  letI := SDLocA_alg R B X R''
  obtain ⟨E⟩ := SDLocA_exists_equiv R B X R''
  exact Algebra.IsIntegral.of_surjective E.toAlgHom E.surjective

/-- **Step 3 (iv), base changed.** `C` integral over `B`, `C_d` étale over `B`, `e` idempotent of `R'' ⊗ C` on whose corner
`1 ⊗ d` is a unit. Then `D = (R'' ⊗ C)/(1-e)` is finite, flat and finitely presented (indeed étale) over `R'' ⊗ B`. -/
theorem SDLocA_finite (C : Type u) [CommRing C] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Algebra.IsIntegral B C] (d : C) [Algebra.Etale B (Localization.Away d)]
    {e : R'' ⊗[R] C} (he : IsIdempotentElem e) (hu : ∃ u, e = u * ((1 : R'') ⊗ₜ[R] d) * e) :
    letI := SDLocA_alg R B C R''
    Algebra.Etale (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) ∧
      Module.Finite (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) ∧
      Module.Flat (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) ∧
      Algebra.FinitePresentation (R'' ⊗[R] B) ((R'' ⊗[R] C) ⧸ Ideal.span {1 - e}) := by
  letI := SDLocA_alg R B C R''
  let Cd := Localization.Away d
  have : IsScalarTower R B Cd := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R C Cd, IsScalarTower.algebraMap_apply B C Cd,
      ← IsScalarTower.algebraMap_apply R B C]
  letI : Algebra (R'' ⊗[R] B) (R'' ⊗[R] Cd) := SDLocA_alg R B Cd R''
  letI : Algebra (R'' ⊗[R] C) (R'' ⊗[R] Cd) := SDLocA_alg R C Cd R''
  have hT : IsScalarTower (R'' ⊗[R] B) (R'' ⊗[R] C) (R'' ⊗[R] Cd) := .of_algebraMap_eq fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => rw [map_add, map_add, map_add, ha, hc]
    | tmul r b =>
      change r ⊗ₜ[R] algebraMap B Cd b = r ⊗ₜ[R] algebraMap C Cd (algebraMap B C b)
      rw [IsScalarTower.algebraMap_apply B C Cd]
  have hE : Algebra.Etale (R'' ⊗[R] B) (R'' ⊗[R] Cd) := SDLocA_etale_bc R B Cd R''
  have hT2 : IsScalarTower R'' (R'' ⊗[R] C) (R'' ⊗[R] Cd) := .of_algebraMap_eq fun r => by
    change r ⊗ₜ[R] (1 : Cd) = r ⊗ₜ[R] algebraMap C Cd (1 : C)
    rw [map_one]
  have hLoc : IsLocalization.Away ((1 : R'') ⊗ₜ[R] d) (R'' ⊗[R] Cd) := by
    have h0 := IsLocalization.tensorProduct_tensorProduct_right R R'' (Submonoid.powers d) Cd
      (A := C) (by ext; simp [RingHom.algebraMap_toAlgebra])
    rw [Submonoid.map_powers] at h0
    exact h0
  have hI : Algebra.IsIntegral (R'' ⊗[R] B) (R'' ⊗[R] C) := SDLocA_integral_bc R B C R''
  obtain ⟨h1, h2, h3⟩ := SDLocA_corner (S := R'' ⊗[R] B) (T := R'' ⊗[R] C) (Tx := R'' ⊗[R] Cd) he hu
  exact ⟨h1, h2, h3, inferInstance⟩

/-- The output of `SDExist_isolate` after inverting `h` in `R'`, in `R'_h ⊗ C`: an idempotent `e₂`, on whose corner `1 ⊗ d`
is a unit. This is the input of `SDLocA_finite`. -/
theorem SDLocA_of_isolate {R C R' : Type u} [CommRing R] [CommRing C] [Algebra R C] [CommRing R'] [Algebra R R']
    (d : C) (hd : d ∈ Algebra.adjoin R {d}) (e₀ : R' ⊗[R] Algebra.adjoin R {d}) (he₀ : IsIdempotentElem e₀)
    (h : R') (u : R' ⊗[R] Algebra.adjoin R {d})
    (hu : (algebraMap R' _ h) * e₀ = u * ((1 : R') ⊗ₜ[R] (⟨d, hd⟩ : Algebra.adjoin R {d})) * e₀) :
    let φ : R' ⊗[R] Algebra.adjoin R {d} →ₐ[R] Localization.Away h ⊗[R] C :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R' (Localization.Away h)) (Algebra.adjoin R {d}).val
    IsIdempotentElem (φ e₀) ∧ ∃ u', φ e₀ = u' * ((1 : Localization.Away h) ⊗ₜ[R] d) * φ e₀ := by
  intro φ
  refine ⟨he₀.map φ, ?_⟩
  obtain ⟨w, hw⟩ := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h).exists_left_inv
  refine ⟨(w ⊗ₜ[R] (1 : C)) * φ u, ?_⟩
  have e1 := congrArg φ hu
  rw [map_mul, map_mul, map_mul] at e1
  have e2 : φ (algebraMap R' _ h) = algebraMap R' (Localization.Away h) h ⊗ₜ[R] (1 : C) := by
    change φ (h ⊗ₜ[R] 1) = _
    simp [φ, Algebra.TensorProduct.map_tmul]
  have e3 : φ ((1 : R') ⊗ₜ[R] (⟨d, hd⟩ : Algebra.adjoin R {d})) = (1 : Localization.Away h) ⊗ₜ[R] d := by
    simp [φ, Algebra.TensorProduct.map_tmul]
  rw [e2, e3] at e1
  have e4 : (w ⊗ₜ[R] (1 : C)) * (algebraMap R' (Localization.Away h) h ⊗ₜ[R] (1 : C)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hw, mul_one]
    rfl
  calc φ e₀ = (w ⊗ₜ[R] (1 : C)) * (algebraMap R' (Localization.Away h) h ⊗ₜ[R] (1 : C)) * φ e₀ := by rw [e4, one_mul]
    _ = (w ⊗ₜ[R] (1 : C)) * ((algebraMap R' (Localization.Away h) h ⊗ₜ[R] (1 : C)) * φ e₀) := by ring
    _ = _ := by rw [e1]; ring

end AlgMag.SD

#print axioms AlgMag.SD.SDLocA_corner
#print axioms AlgMag.SD.SDLocA_finite
#print axioms AlgMag.SD.SDLocA_of_isolate
