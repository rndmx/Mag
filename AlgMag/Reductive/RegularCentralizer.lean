/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Weyl.WeylRootAttractor
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Character

/-!
# Regular elements of `T` and the normalizer (step C1 of `components-NGT-B.md`)

Let `k` be algebraically closed, `G` smooth with `T = D(X) ⊆ G` (closed immersion `π`), `N` a
magnet, `K = (G^N)°` and `R = N ∩ Φ`. A point `t ∈ T(k)` is *regular* (`regularPoints π N`) if
`α(t) ≠ 1` for all `α ∈ R`.

* `conj_torusPt_apply` : for `t ∈ T(A)` and `a` of weight `χ`, `(t g t⁻¹)(a) = χ(t) g(a)`;
* `magnetIdeal_inf_fix_le_ker` : if `g ∈ G^N(A)` commutes with `t' ∈ T(k)`, then
  `g ∈ G^{N ∩ L_{t'}}(A)`, `L_{t'} = {χ : χ(t') = 1}` (`Z_G(t') ⊆ G^{L_{t'}}` on points);
* `compIdeal_fix_eq_bot` : for `t'` regular, `(G^{N ∩ L_{t'}})° = (G^0)°` (Lemma 3: no roots);
* `ker_le_ker_conj` : if `y ∈ G^N(k)` and `y t y⁻¹ = t'` with `t' ∈ T(k)` regular, then
  `t ↦ y t y⁻¹` maps `T` into `(G^{N ∩ L_{t'}})° = (Z_G T)°`; with `(Z_G T)° = T` (hypothesis
  `hT`) it maps `T` into `T`;
* `isNormalizingWith_of_conj_regular` (**C1**) : such a `y` normalizes `T`:
  `∃ σ, Weyl.IsNormalizingWith π k y σ`.

The hypothesis `hT : (G^0)° = T` (`compIdeal π ⊥` is the kernel of `π`) is `(Z_G(T))° = T`,
true for `G` reductive and `T` maximal. It is needed: for `G = G_m² ⋊ ℤ/2` and `T = G_m × 1`
there are no roots, every point of `T` is regular, and the swap conjugates `1` to `1` without
normalizing `T`. The Lie-algebra content (`Lie Z_K(t') = Lie T`) enters through
`compIdeal_eq_of_roots` (F9 Lemma 3, `TangentRoots` / `RootAttractor`).
-/

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

section Torus

variable {A : Type u} [CommRing A] [Algebra k A]

/-- Points of `T` commute. -/
lemma torusPt_commute (τ τ' : MonoidAlgebra k X →ₐ[k] A) :
    Commute (toConv (τ.comp π.toAlgHom)) (toConv (τ'.comp π.toAlgHom)) := by
  have h : ∀ φ : MonoidAlgebra k X →ₐ[k] A,
      toConv (φ.comp π.toAlgHom) = BialgHom.mapDomain π (toConv φ) := by
    intro φ
    rw [BialgHom.mapDomain_apply, ofConv_toConv]
  rw [h, h]
  exact (Commute.all (toConv τ) (toConv τ')).map (BialgHom.mapDomain π)

/-- **Conjugation by a point of `T`** on a coordinate of weight `χ`: `(t g t⁻¹)(a) = χ(t) g(a)`. -/
lemma conj_torusPt_apply (τ : MonoidAlgebra k X →ₐ[k] A) (g : WithConv (H →ₐ[k] A))
    {χ : Additive X} {a : H} (ha : a ∈ torusGrading π χ) :
    (toConv (τ.comp π.toAlgHom) * g * (toConv (τ.comp π.toAlgHom))⁻¹).ofConv a =
      τ (MonoidAlgebra.single (Additive.toMul χ) 1) * g.ofConv a := by
  let φ : A ⊗[k] MonoidAlgebra k X →ₐ[k] A :=
    Algebra.TensorProduct.lift (AlgHom.id k A) τ (fun _ _ => Commute.all _ _)
  have h1 : AlgHom.mapValue φ (torusPoint π A) = toConv (τ.comp π.toAlgHom) := by
    rw [AlgHom.mapValue_apply, torusPoint, ofConv_toConv]
    congr 1
    ext x
    simp [φ]
  have h2 : AlgHom.mapValue φ (AlgHom.mapValue Algebra.TensorProduct.includeLeft g) = g := by
    rw [AlgHom.mapValue_apply, AlgHom.mapValue_apply, ofConv_toConv]
    apply WithConv.ofConv_injective
    ext x
    simp [φ]
  have h3 : AlgHom.mapValue φ (orbitHom π A g) =
      toConv (τ.comp π.toAlgHom) * g * (toConv (τ.comp π.toAlgHom))⁻¹ := by
    rw [orbitHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_mul, map_inv, h1, h2]
  rw [← h3, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Weyl.orbitHom_apply_of_mem g ha]
  simp [φ, mul_comm]

/-- A point commuting with `t ∈ T(A)`: `g(a) = χ(t) g(a)` for `a` of weight `χ`. -/
lemma apply_eq_of_commute (τ : MonoidAlgebra k X →ₐ[k] A) (g : WithConv (H →ₐ[k] A))
    (hc : Commute (toConv (τ.comp π.toAlgHom)) g) {χ : Additive X} {a : H}
    (ha : a ∈ torusGrading π χ) :
    g.ofConv a = τ (MonoidAlgebra.single (Additive.toMul χ) 1) * g.ofConv a := by
  have h := conj_torusPt_apply π τ g ha
  rwa [hc.eq, mul_inv_cancel_right] at h

/-- A point commuting with `t ∈ T(A)` kills the coordinates of weight `χ` when `χ(t) - 1` is a
unit. -/
lemma apply_eq_zero_of_commute (τ : MonoidAlgebra k X →ₐ[k] A) (g : WithConv (H →ₐ[k] A))
    (hc : Commute (toConv (τ.comp π.toAlgHom)) g) {χ : Additive X}
    (hu : IsUnit (τ (MonoidAlgebra.single (Additive.toMul χ) 1) - 1)) {a : H}
    (ha : a ∈ torusGrading π χ) : g.ofConv a = 0 := by
  have h := conj_torusPt_apply π τ g ha
  rw [hc.eq, mul_inv_cancel_right] at h
  have h' : (τ (MonoidAlgebra.single (Additive.toMul χ) 1) - 1) * g.ofConv a = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (hu.mul_right_eq_zero).1 h'

/-- `π` kills the coordinates of nonzero weight: `T` acts trivially on itself. -/
lemma torus_apply_eq_zero {χ : Additive X} (hχ : χ ≠ 0) {a : H} (ha : a ∈ torusGrading π χ) :
    π a = 0 := by
  have hc := torusPt_commute π (A := MonoidAlgebra k X ⊗[k] MonoidAlgebra k X) Algebra.TensorProduct.includeRight
    Algebra.TensorProduct.includeLeft
  have h := apply_eq_of_commute π (A := MonoidAlgebra k X ⊗[k] MonoidAlgebra k X)
    Algebra.TensorProduct.includeRight
    (toConv (Algebra.TensorProduct.includeLeft.comp π.toAlgHom)) hc ha
  rw [ofConv_toConv, AlgHom.comp_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h
  have hne : (1 : X) ≠ Additive.toMul χ := fun h => hχ (by rw [← ofMul_toMul χ, ← h]; rfl)
  have h1 := congrArg (LinearMap.tensorComponent
    (Comodule.monoidCoeff k X (Additive.toMul χ))) h
  rw [LinearMap.tensorComponent_tmul, LinearMap.tensorComponent_tmul,
    Comodule.monoidCoeff_apply, Comodule.monoidCoeff_apply, MonoidAlgebra.one_def,
    MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply, if_pos rfl,
    if_neg hne, one_smul, zero_smul] at h1
  exact h1.symm

/-- `T ⊆ G^N`: `J_N` is killed by `π`. -/
lemma magnetIdeal_le_ker_torus (N : Magnet (Additive X)) :
    magnetIdeal (torusGrading π) N ≤ RingHom.ker π.toAlgHom := by
  rw [magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro χ hχ a ha
  exact torus_apply_eq_zero π (fun h => hχ (by rw [h]; exact N.zero_mem)) ha

/-- The magnet `L_τ = {χ : χ(τ) = 1}` of characters trivial at `τ ∈ T(k)`. -/
def fixMagnet (τ : MonoidAlgebra k X →ₐ[k] k) : Magnet (Additive X) where
  carrier := {χ | τ (MonoidAlgebra.single (Additive.toMul χ) 1) = 1}
  zero_mem' := by
    show τ (MonoidAlgebra.single (Additive.toMul 0) 1) = 1
    rw [toMul_zero, ← MonoidAlgebra.one_def, map_one]
  add_mem' {a b} ha hb := by
    show τ (MonoidAlgebra.single (Additive.toMul (a + b)) 1) = 1
    rw [toMul_add, ← one_mul (1 : k), ← MonoidAlgebra.single_mul_single, map_mul, ha, hb,
      one_mul]

/-- **`Z_G(t') ⊆ G^{L_{t'}}` on points.** A point of `G^N(A)` commuting with `t' ∈ T(k)` lies in
`G^{N ∩ L_{t'}}(A)`. -/
lemma magnetIdeal_inf_fix_le_ker (N : Magnet (Additive X)) (τ : MonoidAlgebra k X →ₐ[k] k)
    (g : WithConv (H →ₐ[k] A)) (hg : g ∈ attractorSubgroup π N A)
    (hc : Commute (toConv (((Algebra.ofId k A).comp τ).comp π.toAlgHom)) g) :
    magnetIdeal (torusGrading π) (N ⊓ fixMagnet τ) ≤ RingHom.ker g.ofConv := by
  rw [magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro χ hχ a ha
  by_cases hN : χ ∈ N
  · have hL : τ (MonoidAlgebra.single (Additive.toMul χ) 1) ≠ 1 := fun h => hχ ⟨hN, h⟩
    have hu : IsUnit (((Algebra.ofId k A).comp τ) (MonoidAlgebra.single (Additive.toMul χ) 1)
        - 1) := by
      rw [AlgHom.comp_apply, Algebra.ofId_apply, ← map_one (algebraMap k A), ← map_sub]
      exact (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hL)).map _
    exact apply_eq_zero_of_commute π _ g hc hu ha
  · exact (mem_attractorSubgroup π).1 hg (mem_magnetIdeal_of_notMem hN ha)

end Torus

section Regular

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **Regular points of `T(k)`** for the magnet `N`: `t = τ ∘ π` with `α(τ) ≠ 1` for every root
`α ∈ N ∩ Φ`. -/
def regularPoints (N : Magnet (Additive X)) : Set (WithConv (H →ₐ[k] k)) :=
  {t | ∃ τ : MonoidAlgebra k X →ₐ[k] k, t = toConv (τ.comp π.toAlgHom) ∧
    ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1}

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **No roots in `N ∩ L_{t'}`** for `t'` regular, so `(G^{N ∩ L_{t'}})° = (G^0)°` (Lemma 3). -/
lemma compIdeal_fix_eq_bot (N : Magnet (Additive X)) (τ : MonoidAlgebra k X →ₐ[k] k)
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) :
    compIdeal π (N ⊓ fixMagnet τ) = compIdeal π ⊥ :=
  (compIdeal_eq_of_roots π bot_le fun α hα =>
    ⟨fun h => (bot_le : (⊥ : Magnet (Additive X)) ≤ N ⊓ fixMagnet τ) h,
      fun h => absurd (AddSubmonoid.mem_inf.1 h).2 (hτ α hα (AddSubmonoid.mem_inf.1 h).1)⟩).symm

omit [Module.Finite k (Bialgebra.CotangentSpace k H)] [Algebra.Smooth k H] in
/-- `(G^0)° = T` makes `Spec k[X]` connected. -/
lemma connectedSpace_of_compIdeal_bot (hπ : Function.Surjective π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) :
    ConnectedSpace (PrimeSpectrum (MonoidAlgebra k X)) := by
  have heq : RingHom.ker π.toAlgHom = RingHom.ker (compMk π ⊥).toAlgHom := by
    ext x
    exact (hT x).symm
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) hπ
  let e2 := Ideal.quotientKerAlgEquivOfSurjective (f := (compMk π ⊥).toAlgHom)
    (compMk_surjective π ⊥)
  let E := e1.symm.trans ((Ideal.quotientEquivAlgOfEq k heq).trans e2)
  have : ConnectedSpace (PrimeSpectrum
      ((H ⧸ (magnetHopfIdeal π ⊥).toIdeal) ⧸ (attrComp π ⊥).toIdeal)) :=
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent
      (FiniteTypeCommHopfAlgCat.of (R := k) (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
  exact (Homeomorph.connectedSpace_iff
    (PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv)).2 this

/-- **Conjugating `T` into `T`.** If `z ∈ G^N(k)`, `t ∈ T(k)`, `t' ∈ T(k)` regular and
`z t z⁻¹ = t'`, then `t ↦ z t z⁻¹` maps `T` into `(G^{N ∩ L_{t'}})° = (G^0)° = T`:
`π ∘ Int(z)^*` kills `ker π`. -/
theorem ker_le_ker_conj (hπ : Function.Surjective π) (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0)
    (N : Magnet (Additive X)) {z t t' : WithConv (H →ₐ[k] k)}
    (hz : z ∈ attractorSubgroup π N k) (ht : t ∈ regularPoints π N)
    (ht' : t' ∈ regularPoints π N) (h : z * t * z⁻¹ = t') (x : H) (hx : π x = 0) :
    π (HopfAlgebra.pointConjugationAlgHom z x) = 0 := by
  obtain ⟨τ, rfl, -⟩ := ht
  obtain ⟨τ', rfl, hreg⟩ := ht'
  let A := MonoidAlgebra k X
  let ι := Algebra.ofId k A
  let g : WithConv (H →ₐ[k] A) := toConv (π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom z))
  let zA := AlgHom.mapValue ι z
  let s : WithConv (H →ₐ[k] A) := toConv ((AlgHom.id k A).comp π.toAlgHom)
  have hg : g = zA * s * zA⁻¹ := by
    have := HopfAlgebra.comp_pointConjugationAlgHom z (toConv π.toAlgHom)
    rw [ofConv_toConv] at this
    exact this
  have hmv : ∀ σ : MonoidAlgebra k X →ₐ[k] k,
      AlgHom.mapValue ι (toConv (σ.comp π.toAlgHom)) = toConv ((ι.comp σ).comp π.toAlgHom) := by
    intro σ
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_assoc]
  have hzt : zA * toConv ((ι.comp τ).comp π.toAlgHom) * zA⁻¹ =
      toConv ((ι.comp τ').comp π.toAlgHom) := by
    rw [← hmv, ← hmv, ← h, map_mul, map_mul, map_inv]
  have hst := torusPt_commute π (AlgHom.id k A) (ι.comp τ)
  have hcomm : Commute (toConv ((ι.comp τ').comp π.toAlgHom)) g := by
    rw [← hzt, hg]
    show _ = _
    calc zA * toConv ((ι.comp τ).comp π.toAlgHom) * zA⁻¹ * (zA * s * zA⁻¹)
        = zA * (toConv ((ι.comp τ).comp π.toAlgHom) * s) * zA⁻¹ := by group
      _ = zA * (s * toConv ((ι.comp τ).comp π.toAlgHom)) * zA⁻¹ := by rw [hst.eq]
      _ = zA * s * zA⁻¹ * (zA * toConv ((ι.comp τ).comp π.toAlgHom) * zA⁻¹) := by group
  have hzA : zA ∈ attractorSubgroup π N A := by
    refine (mem_attractorSubgroup π).2 fun y hy => ?_
    have := (mem_attractorSubgroup π).1 hz hy
    rw [RingHom.mem_ker] at this ⊢
    simp [zA, this]
  have hs : s ∈ attractorSubgroup π N A :=
    (mem_attractorSubgroup π).2 (magnetIdeal_le_ker_torus π N)
  have hgN : g ∈ attractorSubgroup π N A := by
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzA hs) (Subgroup.inv_mem _ hzA)
  set M := N ⊓ fixMagnet τ'
  have hJ := magnetIdeal_inf_fix_le_ker π N τ' g hgN hcomm
  -- `g` is a bialgebra map `O(G) → k[X]`; lift it to `O(G^M)`.
  let f : H →ₐc[k] A := π.comp (HopfAlgebra.pointConjugationBialgEquiv z : H →ₐc[k] H)
  have hfg : ∀ y, f y = g.ofConv y := fun y => by
    show π (HopfAlgebra.pointConjugationBialgEquiv z y) =
      π (HopfAlgebra.pointConjugationAlgHom z y)
    rw [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
    rfl
  have hJ' : (magnetHopfIdeal π M).toIdeal ≤ RingHom.ker f.toAlgHom.toRingHom := by
    intro y hy
    rw [magnetHopfIdeal_toIdeal] at hy
    have := hJ hy
    rw [RingHom.mem_ker] at this ⊢
    exact (hfg y).trans this
  let f' := Bialgebra.Quotient.liftBialgHom _ f hJ'
  have : ConnectedSpace (PrimeSpectrum A) := connectedSpace_of_compIdeal_bot π hπ hT
  have hI := CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
    (H := _root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π M).toIdeal))
    (K := _root_.CommHopfAlgCat.of k A) (_root_.CommHopfAlgCat.ofHom f')
  have hxM : x ∈ compIdeal π M := by
    rw [compIdeal_fix_eq_bot π N τ' hreg]
    exact (hT x).2 hx
  have hmem : Ideal.Quotient.mk (magnetHopfIdeal π M).toIdeal x ∈ (attrComp π M).toIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.1 hxM
  have h0 := hI hmem
  rw [RingHom.mem_ker] at h0
  have h1 : f x = 0 := h0
  rw [hfg] at h1
  exact h1

/-- **Step C1.** If `y ∈ G^N(k)` conjugates a regular `t ∈ T(k)` to a regular `t' ∈ T(k)`, then
`y` normalizes `T`. Here `hT : (G^0)° = T`, i.e. `(Z_G T)° = T`. -/
theorem isNormalizingWith_of_conj_regular (hπ : Function.Surjective π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (N : Magnet (Additive X))
    {y t t' : WithConv (H →ₐ[k] k)} (hy : y ∈ attractorSubgroup π N k)
    (ht : t ∈ regularPoints π N) (ht' : t' ∈ regularPoints π N) (h : y * t * y⁻¹ = t') :
    ∃ σ : X ≃* X, Weyl.IsNormalizingWith π k y σ := by
  have k1 := ker_le_ker_conj π hπ hT N hy ht ht' h
  have k2 := ker_le_ker_conj π hπ hT N (Subgroup.inv_mem _ hy) ht' ht
    (by rw [← h]; group)
  have hmem : y ∈ BialgHom.normalizerPoints π hπ := by
    rw [BialgHom.mem_normalizerPoints]
    apply le_antisymm
    · intro x hx
      rw [mem_conjugate, mem_kerOfSurjective] at hx
      rw [mem_kerOfSurjective]
      have := k2 _ hx
      rwa [← AlgHom.comp_apply, ← HopfAlgebra.pointConjugationAlgHom_mul, mul_inv_cancel,
        HopfAlgebra.pointConjugationAlgHom_one, AlgHom.id_apply] at this
    · intro x hx
      rw [mem_conjugate, mem_kerOfSurjective]
      exact k1 x ((mem_kerOfSurjective _ _).1 hx)
  set w := BialgHom.normalizerCharacterEquiv π hπ ⟨y, hmem⟩
  have hc : π.toAlgHom.comp (HopfAlgebra.pointConjugationAlgHom y⁻¹) =
      (MonoidAlgebra.domCongr k k w).toAlgHom.comp π.toAlgHom := by
    ext x
    have h1 := BialgHom.normalizerCoordinateMap_apply π hπ ⟨y, hmem⟩ x
    have h2 := AlgHom.congr_fun (BialgHom.normalizerCoordinateMap_eq_domCongr π hπ ⟨y, hmem⟩)
      (π x)
    simp only [BialgHom.coe_toAlgHom, AlgEquiv.coe_toAlgHom] at h2
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, AlgEquiv.coe_toAlgHom]
    rw [← h2, h1]
  have hc' := HopfAlgebra.comp_pointConjugationAlgHom_eq_symm_comp π.toAlgHom y _ hc
  refine ⟨w.symm, ?_⟩
  unfold Weyl.IsNormalizingWith
  have hinc : (Algebra.TensorProduct.includeLeft : k →ₐ[k] k ⊗[k] MonoidAlgebra k X) =
      Algebra.ofId k _ := Subsingleton.elim _ _
  rw [MulAut.conj_apply, hinc, ← HopfAlgebra.comp_pointConjugationAlgHom, Weyl.twistPoint,
    AlgMag.Reductive.torusPoint, ofConv_toConv, AlgHom.comp_assoc, hc']
  congr 2

/-- **C1 in the form of `exists_mul_normalizer_of_irreducible`** (`hC1`), for
`Nm = {n | ∃ σ, IsNormalizingWith π k n σ}`. -/
theorem regular_conj_mem_normalizer (hπ : Function.Surjective π)
    (hT : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0) (N : Magnet (Additive X)) :
    ∀ y ∈ attractorSubgroup π N k, ∀ t ∈ regularPoints π N, ∀ t' ∈ regularPoints π N,
      y * t * y⁻¹ = t' → ∃ σ : X ≃* X, Weyl.IsNormalizingWith π k y σ :=
  fun _ hy _ ht _ ht' h => isNormalizingWith_of_conj_regular π hπ hT N hy ht ht' h

end Regular

end AlgMag.Reductive
