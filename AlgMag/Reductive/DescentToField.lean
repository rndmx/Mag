/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.MonogenicRootBijection
import AlgMag.Reductive.Prop1610Field
import AlgMag.Reductive.IdentityComponentBaseChange

/-!
# Descent of the §13 results from `k̄` to an arbitrary field `k`

Let `G = Spec H` be an affine group over a field `k` with an action of `D(X)` given by `π`, and
`K` a field extension of `k`. Attractors commute with base change
(`magnetIdeal_baseChange`), and an ideal of `H` is recovered from its extension to `K ⊗[k] H`
(`comap_map_includeRight`). Hence `G^L = G^N` over `k` iff `G_K^L = G_K^N`
(`magnetIdeal_eq_iff_baseChange`): pure magnets, the hulls `E(G^N)` and `Π(a)` are unchanged by
`k → K` (`isPure_baseChange`, `hullSet_baseChange`, `pureMagnets_baseChange`).

Tangent vectors extend to `G_K` (`extendDerivation`), so the roots of `G_{k̄}` are the roots of
`G` (`roots_piBar`). Normalizing points base change (`isNormalizingWith_baseChange_iff`), so split
reductive data (with a root datum) over `k` base change to `k̄`
(`SplitReductiveData.baseChange`, `SplitReductiveData.WithRootDatum.baseChange`): `W` and the
root datum are unchanged, and `N_G(T)(ar{k̄}) = ⊔ n_w T` is transported along
`\overline{k̄} ≃ₐ[k] k̄`.

The field versions `*_field` of the `*_lattice` theorems follow, for `G` split reductive over
any field `k` (`D : SplitReductiveData π`), with the roots `Φ = roots π` and the Weyl group of
`D`; the `*_fieldBar` versions take split reductive data over `k̄`.
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u v

section BaseChange

variable {k : Type u} (K : Type v) {H : Type u} {X : Type u}
variable [Field k] [Field K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

omit [CommGroup X] [DecidableEq X] in
/-- **Faithful flatness of `k → K`**: an ideal of `H` is the contraction of its extension to
`K ⊗[k] H`. -/
theorem comap_map_includeRight (I : Ideal H) :
    (I.map (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)).comap
      (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) = I :=
  le_antisymm (fun _ hx => mem_of_one_tmul_mem_map (K := K) hx) Ideal.le_comap_map

/-- **`G^L = G^N` over `k` iff over `K`.** -/
theorem magnetIdeal_eq_iff_baseChange (N L : Magnet (Additive X)) :
    magnetIdeal (torusGrading (torusBaseChange K π)) N =
        magnetIdeal (torusGrading (torusBaseChange K π)) L ↔
      magnetIdeal (torusGrading π) N = magnetIdeal (torusGrading π) L := by
  rw [magnetIdeal_baseChange, magnetIdeal_baseChange]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  calc magnetIdeal (torusGrading π) N
      = ((magnetIdeal (torusGrading π) N).map
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)).comap
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) :=
        (comap_map_includeRight K _).symm
    _ = ((magnetIdeal (torusGrading π) L).map
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H)).comap
          (Algebra.TensorProduct.includeRight : H →ₐ[k] K ⊗[k] H) := by rw [h]
    _ = magnetIdeal (torusGrading π) L := comap_map_includeRight K _

/-- Equality of attractors, in the `affineY` form. -/
theorem affineY_eq_iff_baseChange (N L : Magnet (Additive X)) :
    affineY (torusGrading (torusBaseChange K π)) N =
        affineY (torusGrading (torusBaseChange K π)) L ↔
      affineY (torusGrading π) N = affineY (torusGrading π) L :=
  magnetIdeal_eq_iff_baseChange K π N L

/-- **Pure magnets are unchanged by `k → K`.** -/
theorem isPure_baseChange :
    IsPure (affineY (torusGrading (torusBaseChange K π))) = IsPure (affineY (torusGrading π)) := by
  funext N
  apply propext
  simp only [IsPure, affineY_eq_iff_baseChange]

theorem isPure_baseChange_iff (N : Magnet (Additive X)) :
    IsPure (affineY (torusGrading (torusBaseChange K π))) N ↔
      IsPure (affineY (torusGrading π)) N := by
  rw [isPure_baseChange]

/-- The magnets with the same attractor as `N` are the same over `k` and over `K`. -/
theorem hullSet_baseChange (N : Magnet (Additive X)) :
    {L | affineY (torusGrading (torusBaseChange K π)) L =
        affineY (torusGrading (torusBaseChange K π)) N} =
      {L | affineY (torusGrading π) L = affineY (torusGrading π) N} := by
  ext L
  exact affineY_eq_iff_baseChange K π L N

/-- **`E(G^N)` is unchanged by `k → K`.** -/
theorem hull_baseChange (N : Magnet (Additive X)) :
    sInf {L | affineY (torusGrading (torusBaseChange K π)) L =
        affineY (torusGrading (torusBaseChange K π)) N} =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} := by
  rw [hullSet_baseChange]

/-- **`Π(a)` is unchanged by `k → K`.** -/
theorem pureMagnets_baseChange :
    pureMagnets (affineY (torusGrading (torusBaseChange K π))) =
      pureMagnets (affineY (torusGrading π)) := by
  rw [pureMagnets, pureMagnets, isPure_baseChange]

end BaseChange

/-! ### Tangent vectors and roots base change -/

section Ext

variable {k : Type u} (K : Type v) {H : Type u} [Field k] [Field K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H]

/-- The `K`-linear extension `s ⊗ x ↦ d(x) s` of a tangent vector `d` of `G`. -/
def extendDerivationLin (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    K ⊗[k] H →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid k K K).toLinearMap ∘ₗ
    LinearMap.baseChange K ((Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap ∘ₗ
      (d : H →ₗ[k] Bialgebra.CounitAlgebra k H k))

lemma extendDerivationLin_tmul (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (s : K) (x : H) :
    extendDerivationLin K d (s ⊗ₜ[k] x) =
      algebraMap k K (Bialgebra.CounitAlgebra.algEquivSelf k H k (d x)) * s := by
  rw [← Algebra.smul_def]; rfl

/-- **Tangent vectors extend to `G_K`**: the `K`-derivation `s ⊗ x ↦ d(x) s`. -/
def extendDerivation (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K) :=
  Derivation.mk'
    ((Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K).symm.toLinearMap ∘ₗ
      extendDerivationLin K d)
    (fun a b => by
      apply (Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K).injective
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        AlgEquiv.apply_symm_apply, map_add, Bialgebra.CounitAlgebra.algEquivSelf_smul]
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add a a' ha ha' => simp only [add_mul, map_add, ha, ha']; ring
      | tmul s x =>
        induction b using TensorProduct.induction_on with
        | zero => simp
        | add b b' hb hb' => simp only [mul_add, map_add, hb, hb']; ring
        | tmul t y =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [extendDerivationLin_tmul, Bialgebra.CounitAlgebra.algEquivSelf_apply_mul,
            map_add, map_mul]
          simp [TensorProduct.counit_tmul, Algebra.smul_def]
          ring)

lemma algEquivSelf_extendDerivation_one_tmul (d : Derivation k H (Bialgebra.CounitAlgebra k H k))
    (x : H) :
    Bialgebra.CounitAlgebra.algEquivSelf K (K ⊗[k] H) K (extendDerivation K d ((1 : K) ⊗ₜ[k] x)) =
      algebraMap k K (Bialgebra.CounitAlgebra.algEquivSelf k H k (d x)) := by
  simp [extendDerivation, extendDerivationLin_tmul]
  exact Bialgebra.CounitAlgebra.algEquivSelf_apply (R := K) (A := K ⊗[k] H) (B := K) _

variable {X : Type*} [CommGroup X] [DecidableEq X] (π : H →ₐc[k] MonoidAlgebra k X)

omit [DecidableEq X] in
/-- **Tangent weights ascend**: a tangent weight of `G` is a tangent weight of `G_K`. -/
theorem tangentWeights_subset_baseChange :
    tangentWeights π k ⊆ tangentWeights (torusBaseChange K π) K := by
  rintro χ ⟨d, h, hh, hd⟩
  refine ⟨extendDerivation K d, (1 : K) ⊗ₜ[k] h, one_tmul_mem_torusGrading K π hh, fun h0 => hd ?_⟩
  have := algEquivSelf_extendDerivation_one_tmul K d h
  rw [h0, map_zero] at this
  apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
  rw [map_zero]
  exact (FaithfulSMul.algebraMap_injective k K) (this.symm.trans (map_zero _).symm)

end Ext

section Roots

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Algebra.FiniteType k H]

/-- **The roots of `G_{k̄}` are the roots of `G`.** -/
theorem roots_piBar : roots (piBar π) = roots π := by
  refine (roots_piBar_subset π).antisymm fun α hα => ?_
  have h0 : α ≠ 0 := fun h => hα.1 (by rw [h]; rfl)
  exact (mem_tangentWeights_iff_mem_roots h0).1
    (tangentWeights_subset_baseChange (AlgebraicClosure k) π
      ((mem_tangentWeights_iff_mem_roots (π := π) h0).2 hα))

end Roots

/-! ### Split reductive data base change to `k̄` -/

section NormalizingBaseChange

open AlgMag.Weyl

variable {k : Type u} (K : Type u) {H : Type u} {X : Type u}
variable [Field k] [Field K] [Algebra k K]
variable [CommRing H] [HopfAlgebra k H] [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X)
variable (A : Type u) [CommRing A] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The comparison `A ⊗[k] k[X] → A ⊗[K] K[X]`, `a ⊗ p ↦ a ⊗ p_K`. -/
def valueIncl : A ⊗[k] MonoidAlgebra k X →ₐ[k] A ⊗[K] MonoidAlgebra K X :=
  Algebra.TensorProduct.productMap
    ((Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A)
      (B := MonoidAlgebra K X)).restrictScalars k)
    ((Algebra.TensorProduct.includeRight (R := K) (A := A)
      (B := MonoidAlgebra K X)).restrictScalars k |>.comp
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k))

omit [HopfAlgebra k H] in
@[simp] lemma valueIncl_tmul (a : A) (p : MonoidAlgebra k X) :
    valueIncl (k := k) (X := X) K A (a ⊗ₜ[k] p) =
      a ⊗ₜ[K] MonoidAlgebra.mapAlgHom X (Algebra.ofId k K) p := by
  simp [valueIncl]

omit [HopfAlgebra k H] in
lemma valueIncl_injective : Function.Injective (valueIncl (k := k) (X := X) K A) := by
  let f : MonoidAlgebra K X →ₗ[K] K ⊗[k] MonoidAlgebra k X :=
    (MonoidAlgebra.scalarTensorEquiv k K :
      K ⊗[k] MonoidAlgebra k X ≃ₐ[K] MonoidAlgebra K X).symm.toLinearMap
  let Ψ : A ⊗[K] MonoidAlgebra K X →ₗ[K] A ⊗[k] MonoidAlgebra k X :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K K A (MonoidAlgebra k X)).toLinearMap ∘ₗ
      LinearMap.lTensor A f
  have hf : ∀ p : MonoidAlgebra k X,
      f (MonoidAlgebra.mapAlgHom X (Algebra.ofId k K) p) = (1 : K) ⊗ₜ[k] p := by
    intro p
    simp only [f]
    rw [AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_eq, MonoidAlgebra.scalarTensorEquiv_tmul,
      one_smul]
  have h : ∀ y, Ψ (valueIncl (k := k) K A y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul a p =>
      rw [valueIncl_tmul]
      simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul, hf,
        LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  exact Function.LeftInverse.injective h

omit [HopfAlgebra k H] in
lemma mapDomain_mapAlgHom (f : X →* X) :
    ((MonoidAlgebra.mapDomainAlgHom K K f).restrictScalars k).comp
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k) =
      ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k).comp
        (MonoidAlgebra.mapDomainAlgHom k k f) := by
  apply MonoidAlgebra.algHom_ext
  · intro x
    simp
  · ext

/-- `k`-points and `K`-points of `G` with values in a `K`-algebra. -/
abbrev bcPoints : WithConv (H →ₐ[k] A) ≃* WithConv (K ⊗[k] H →ₐ[K] A) :=
  AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := H) (R := A)

lemma bcPoints_symm_twistPoint (f : X →* X) :
    (bcPoints K (A ⊗[K] MonoidAlgebra K X)).symm (twistPoint (torusBaseChange K π) A f) =
      AlgHom.mapValue (valueIncl (k := k) K A) (twistPoint π A f) := by
  apply WithConv.ext
  ext h
  have := congrArg (fun φ => φ (π h)) (mapDomain_mapAlgHom (k := k) K f)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
  simp [twistPoint, AlgHom.mapValue_apply, this, valueIncl_tmul]

lemma bcPoints_symm_includeLeft (g : WithConv (K ⊗[k] H →ₐ[K] A)) :
    (bcPoints K (A ⊗[K] MonoidAlgebra K X)).symm
        (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A)
          (B := MonoidAlgebra K X)) g) =
      AlgHom.mapValue (valueIncl (k := k) K A) (AlgHom.mapValue (Algebra.TensorProduct.includeLeft
        (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) ((bcPoints K A).symm g)) := by
  apply WithConv.ext
  ext h
  simp [AlgHom.mapValue_apply, valueIncl_tmul]

/-- **Normalizing points base change**: a `K`-point of `G_K` normalizes `T_K` with automorphism
`σ` iff the corresponding `k`-point of `G` normalizes `T` with automorphism `σ`. -/
theorem isNormalizingWith_baseChange_iff (g : WithConv (K ⊗[k] H →ₐ[K] A)) (σ : X ≃* X) :
    IsNormalizingWith (torusBaseChange K π) A g σ ↔
      IsNormalizingWith π A ((bcPoints K A).symm g) σ := by
  have hinj : Function.Injective (AlgHom.mapValue (H := H) (valueIncl (k := k) (X := X) K A)) := by
    intro a b hab
    apply WithConv.ext
    ext h
    exact valueIncl_injective (k := k) K A (congrArg (fun φ => φ.ofConv h) hab)
  rw [IsNormalizingWith, IsNormalizingWith, MulAut.conj_apply, MulAut.conj_apply,
    ← twistPoint_id (torusBaseChange K π), ← twistPoint_id π,
    ← (bcPoints (k := k) (H := H) K (A ⊗[K] MonoidAlgebra K X)).symm.injective.eq_iff, map_mul, map_mul, map_inv,
    bcPoints_symm_includeLeft, bcPoints_symm_twistPoint, bcPoints_symm_twistPoint,
    ← map_inv, ← map_mul, ← map_mul]
  exact hinj.eq_iff

end NormalizingBaseChange

section SplitBaseChange

open AlgMag.Weyl

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

omit [DecidableEq X] in
/-- `T_K → G_K` is a closed immersion. -/
lemma torusBaseChange_surjective (K : Type u) [Field K] [Algebra k K]
    (hπ : Function.Surjective π) : Function.Surjective (torusBaseChange K π) := by
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single x c =>
    obtain ⟨h, hh⟩ := hπ (MonoidAlgebra.single x 1)
    refine ⟨c ⊗ₜ[k] h, ?_⟩
    rw [torusBaseChange_tmul, hh]
    simp

variable [Algebra.FiniteType k H]

/-- **Split reductive data base change to `k̄`**: the Weyl group `W` is unchanged, the
representatives `n_w` are base changed, and `N_{G_{k̄}}(T_{k̄})(\bar{k̄}) = ⊔ n_w T` is
transported along `\overline{k̄} ≃ k̄`. -/
def SplitReductiveData.baseChange (D : SplitReductiveData π) : SplitReductiveData (piBar π) where
  surjective := torusBaseChange_surjective _ D.surjective
  W := D.W
  finite := D.finite
  rep w := bcPoints (AlgebraicClosure k) (AlgebraicClosure k) (toAlgClosure (D.rep w))
  rep_normalizing w := by
    rw [isNormalizingWith_baseChange_iff, MulEquiv.symm_apply_apply]
    exact AlgMag.Reductive.IsNormalizingWith.mapValue π _ (D.rep_normalizing w)
  normalizer_cover g σ hg := by
    let K := AlgebraicClosure k
    let L := AlgebraicClosure K
    have h0 := (isNormalizingWith_baseChange_iff K π L g σ).1 hg
    let φ : L ≃ₐ[k] K := IsAlgClosure.equiv k L K
    have h1 := AlgMag.Reductive.IsNormalizingWith.mapValue π φ.toAlgHom h0
    obtain ⟨hσ, t, ht⟩ := D.normalizer_cover _ σ h1
    let χ : X →* L :=
      (φ.symm.toAlgHom.comp t).toRingHom.toMonoidHom.comp (MonoidAlgebra.of k X)
    let t' : MonoidAlgebra K X →ₐ[K] L := MonoidAlgebra.lift K L X χ
    refine ⟨hσ, t', ?_⟩
    have hcomp : (t'.restrictScalars k).comp
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId k K)).restrictScalars k) =
        φ.symm.toAlgHom.comp t := by
      apply MonoidAlgebra.algHom_ext
      · intro x
        simp [t', χ]
      · exact Subsingleton.elim _ _
    have ht' : ∀ p, t' (MonoidAlgebra.mapAlgHom X (Algebra.ofId k K) p) = φ.symm (t p) :=
      fun p => by simpa using congrArg (fun F : MonoidAlgebra k X →ₐ[k] L => F p) hcomp
    have hg0 : (bcPoints K L).symm g = AlgHom.mapValue φ.symm.toAlgHom
        (toAlgClosure (D.rep ⟨σ, hσ⟩) * torusPointOf π t) := by
      rw [← ht]
      apply WithConv.ext
      ext h
      simp [AlgHom.mapValue_apply]
    apply (bcPoints (k := k) (H := H) K L).symm.injective
    rw [hg0, map_mul, map_mul]
    congr 1
    · apply WithConv.ext
      ext h
      simp only [toAlgClosure, AlgHom.mapValue_apply] at *
      simp
      exact φ.symm.commutes _
    · apply WithConv.ext
      ext h
      simp [torusPointOf, AlgHom.mapValue_apply]
      exact (ht' _).symm
  roots_stable w hw α hα := by
    rw [roots_piBar] at hα ⊢
    exact D.roots_stable w hw α hα

/-- The root datum of `G` is a root datum of `G_{k̄}`. -/
def SplitReductiveData.WithRootDatum.baseChange (D : SplitReductiveData.WithRootDatum π) :
    SplitReductiveData.WithRootDatum (piBar π) :=
  { D.toSplitReductiveData.baseChange with
    ι := D.ι
    N := D.N
    P := D.P
    b := D.b
    range_root := D.range_root.trans (roots_piBar π).symm
    weyl_eq := D.weyl_eq }

end SplitBaseChange

/-! ### The §13 theorems over an arbitrary field -/

section Field

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}
variable [Algebra.FiniteType k H] [Algebra.Smooth k H] [Monoid.FG X] [IsMulTorsionFree X]

/-- **Theorem `thm:red-pure`** over any field, from split reductive data over `k̄`. -/
theorem red_pure_fieldBar (D : SplitReductiveData (piBar π)) (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : D.W => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} := by
  rw [← hull_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact red_pure_lattice D N

/-- **Theorem `thm:red-classification` (i)**, finiteness of `Π(a)`, over any field, from split reductive data over `k̄`. -/
theorem finite_pure_fieldBar (D : SplitReductiveData (piBar π)) :
    {N | IsPure (affineY (torusGrading π)) N}.Finite := by
  rw [← isPure_baseChange (AlgebraicClosure k) π]
  exact finite_pure_lattice D

/-- **Theorem `thm:red-classification` (i)**, bijection, over any field, from split reductive data over `k̄`. -/
theorem red_classification_i_fieldBar (D : SplitReductiveData (piBar π)) :
    Set.BijOn (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} ∧
      Set.InvOn (fun p : Set (Additive X) × Set D.W =>
          Rooted.pairMagnet (fun w : D.W => actW (w : X ≃* X)) p.1 p.2)
        (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact red_classification_i_lattice D

/-- **Theorem `thm:red-classification` (i)**, injectivity, over any field, from split reductive data over `k̄`. -/
theorem red_classification_i_inj_fieldBar (D : SplitReductiveData (piBar π))
    {N L : AddSubmonoid (Additive X)} (hN : IsPure (affineY (torusGrading π)) N)
    (hL : IsPure (affineY (torusGrading π)) L)
    (h1 : (N : Set (Additive X)) ∩ roots π = (L : Set (Additive X)) ∩ roots π)
    (h2 : {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N} =
      {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L}) : N = L := by
  rw [← isPure_baseChange (AlgebraicClosure k) π] at hN hL
  rw [← roots_piBar π] at h1
  exact red_classification_i_inj_lattice D hN hL h1 h2

/-- **Theorem `thm:red-classification` (ii)** over any field, from split reductive data over `k̄`. -/
theorem classification_ii_fieldBar (D : SplitReductiveData (piBar π))
    {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R := by
  rw [← roots_piBar π] at hRΦ hR
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← hull_baseChange (AlgebraicClosure k) π,
    ← roots_piBar π]
  exact classification_ii_lattice D hRΦ hR

/-- **Theorem `thm:red-rooted`** over any field, from split reductive data over `k̄`. -/
theorem reductive_joinDense_fieldBar (D : SplitReductiveData (piBar π)) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : D.W => actW (w : X ≃* X)) := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact reductive_joinDense_lattice D

/-- **Theorem `thm:red-rooted`, minimal root**, over any field, from split reductive data over `k̄`. -/
theorem joinIrreducibles_isLeast_fieldBar (D : SplitReductiveData (piBar π)) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
        (Rooted.joinIrreducibles (IsPure (affineY (torusGrading π)))) ∧
      ∀ Ψ, Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) Ψ →
        Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) ⊆ Ψ := by
  rw [← isPure_baseChange (AlgebraicClosure k) π]
  exact joinIrreducibles_isLeast_lattice D

/-- **Theorem `thm:red-rooted`, minimal-root formula**, over any field, from split reductive data over `k̄`. -/
theorem joinIrreducibles_eq_fieldBar (D : SplitReductiveData.WithRootDatum (piBar π)) :
    Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) = Rooted.mono '' roots π ∪
      {Z | ∃ w : D.W, Z = Rooted.weylMagnet (actW (w : X ≃* X)) ∧
        Rooted.weylMagnet (actW (w : X ≃* X)) ≠
          Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w} := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact joinIrreducibles_eq_lattice D

/-- **Theorem `thm:red-SL-Sp`** over any field, from split reductive data over `k̄`. -/
theorem red_SL_Sp_fieldBar (D : SplitReductiveData.WithRootDatum (piBar π)) :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩
          roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π) (fun w : D.W => actW (w : X ≃* X))] := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact red_SL_Sp_lattice D

/-- **Theorem `thm:red-parabolic`** over any field, from split reductive data over `k̄`. -/
theorem parabolic_bijOn_fieldBar (D : SplitReductiveData.WithRootDatum (piBar π)) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧
          R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧
          R ∪ -R = roots π} := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact parabolic_bijOn_lattice D

/-- **Monogenic pure magnets** over any field, from split reductive data over `k̄`: exactly the rays `ℕα`, `α ∈ Φ`. -/
theorem red_pure_mono_iff_fieldBar (D : SplitReductiveData.WithRootDatum (piBar π))
    (N : AddSubmonoid (Additive X)) :
    (IsPure (affineY (torusGrading π)) N ∧ ∃ x, x ≠ 0 ∧ N = AddSubmonoid.closure {x}) ↔
      ∃ a ∈ roots π, N = AddSubmonoid.closure {a} := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact red_pure_mono_iff_lattice D N

/-- **Corollary `cor:red-monogenic`** over any field, from split reductive data over `k̄`: `α ↦ ℕα` is a bijection from `Φ` onto the
nonzero monogenerated pure magnets. -/
theorem red_mono_bijOn_fieldBar (D : SplitReductiveData.WithRootDatum (piBar π)) :
    Set.BijOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π)
      {N | IsPure (affineY (torusGrading π)) N ∧ (∃ x, N = AddSubmonoid.closure {x}) ∧
        N ≠ ⊥} := by
  rw [← isPure_baseChange (AlgebraicClosure k) π, ← roots_piBar π]
  exact red_mono_bijOn_lattice D

/-! #### From split reductive data over `k` -/

/-- **Theorem `thm:red-pure`** over any field. -/
theorem red_pure_field (D : SplitReductiveData π) (N : AddSubmonoid (Additive X)) :
    Rooted.reductiveHull (roots π) (fun w : D.W => actW (w : X ≃* X)) N =
      sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} :=
  red_pure_fieldBar D.baseChange N

/-- **Theorem `thm:red-classification` (i)**, finiteness of `Π(a)`, over any field. -/
theorem finite_pure_field (D : SplitReductiveData π) :
    {N | IsPure (affineY (torusGrading π)) N}.Finite :=
  finite_pure_fieldBar D.baseChange

/-- **Theorem `thm:red-classification` (i)**, bijection, over any field. -/
theorem red_classification_i_field (D : SplitReductiveData π) :
    Set.BijOn (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} ∧
      Set.InvOn (fun p : Set (Additive X) × Set D.W =>
          Rooted.pairMagnet (fun w : D.W => actW (w : X ≃* X)) p.1 p.2)
        (Rooted.pairOf (roots π) (fun w : D.W => actW (w : X ≃* X)))
        {N | IsPure (affineY (torusGrading π)) N}
        {p | Rooted.IsCompatiblePair (roots π) (fun w : D.W => actW (w : X ≃* X)) p} :=
  red_classification_i_fieldBar D.baseChange

/-- **Theorem `thm:red-classification` (i)**, injectivity, over any field. -/
theorem red_classification_i_inj_field (D : SplitReductiveData π)
    {N L : AddSubmonoid (Additive X)} (hN : IsPure (affineY (torusGrading π)) N)
    (hL : IsPure (affineY (torusGrading π)) L)
    (h1 : (N : Set (Additive X)) ∩ roots π = (L : Set (Additive X)) ∩ roots π)
    (h2 : {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ N} =
      {w : D.W | Rooted.weylMagnet (actW (w : X ≃* X)) ≤ L}) : N = L :=
  red_classification_i_inj_fieldBar D.baseChange hN hL h1 h2

/-- **Theorem `thm:red-classification` (ii)** over any field. -/
theorem classification_ii_field (D : SplitReductiveData π)
    {R : Set (Additive X)} (hRΦ : R ⊆ roots π)
    (hR : (AddSubmonoid.closure R : Set (Additive X)) ∩ roots π = R) :
    IsPure (affineY (torusGrading π))
        (sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)}) ∧
      ((sInf {L | affineY (torusGrading π) L =
          affineY (torusGrading π) (AddSubmonoid.closure R)} : AddSubmonoid (Additive X)) :
          Set (Additive X)) ∩ roots π = R :=
  classification_ii_fieldBar D.baseChange hRΦ hR

/-- **Theorem `thm:red-rooted`** over any field. -/
theorem reductive_joinDense_field (D : SplitReductiveData π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
      (Rooted.reductiveRoot (roots π) fun w : D.W => actW (w : X ≃* X)) :=
  reductive_joinDense_fieldBar D.baseChange

/-- **Theorem `thm:red-rooted`, minimal root**, over any field. -/
theorem joinIrreducibles_isLeast_field (D : SplitReductiveData π) :
    Rooted.IsJoinDense (IsPure (affineY (torusGrading π)))
        (Rooted.joinIrreducibles (IsPure (affineY (torusGrading π)))) ∧
      ∀ Ψ, Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) Ψ →
        Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) ⊆ Ψ :=
  joinIrreducibles_isLeast_fieldBar D.baseChange

/-- **Theorem `thm:red-rooted`, minimal-root formula**, over any field. -/
theorem joinIrreducibles_eq_field (D : SplitReductiveData.WithRootDatum π) :
    Rooted.joinIrreducibles (IsPure (affineY (torusGrading π))) = Rooted.mono '' roots π ∪
      {Z | ∃ w : D.W, Z = Rooted.weylMagnet (actW (w : X ≃* X)) ∧
        Rooted.weylMagnet (actW (w : X ≃* X)) ≠
          Rooted.weylMagnetLower (roots π) (fun w : D.W => actW (w : X ≃* X)) w} :=
  joinIrreducibles_eq_fieldBar D.baseChange

/-- **Theorem `thm:red-SL-Sp`** over any field. -/
theorem red_SL_Sp_field (D : SplitReductiveData.WithRootDatum π) :
    List.TFAE [Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩
          roots π)
        {N | IsPure (affineY (torusGrading π)) N} {E | Rooted.IsStableElt (roots π) E},
      Rooted.IsJoinDense (IsPure (affineY (torusGrading π))) (Rooted.mono '' roots π),
      SLSp.JoinIrredWeylGenerated (roots π) (fun w : D.W => actW (w : X ≃* X))] :=
  red_SL_Sp_fieldBar D.baseChange

/-- **Theorem `thm:red-parabolic`** over any field. -/
theorem parabolic_bijOn_field (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧
          R ∪ -R = roots π} ∧
      Set.InvOn AddSubmonoid.closure
        (fun N : AddSubmonoid (Additive X) => (N : Set (Additive X)) ∩ roots π)
        {N | IsPure (affineY (torusGrading π)) N ∧ ∃ B' ∈ Set.range (fun v : D.P.weylGroup =>
          RootSystem.RootDatum.act D.P v '' (D.P.root '' D.b.support)), B' ⊆ N}
        {R | RootSystem.RootDatum.IsClosedRoots (roots π) R ∧
          R ∪ -R = roots π} :=
  parabolic_bijOn_fieldBar D.baseChange

/-- **Monogenic pure magnets** over any field: exactly the rays `ℕα`, `α ∈ Φ`. -/
theorem red_pure_mono_iff_field (D : SplitReductiveData.WithRootDatum π)
    (N : AddSubmonoid (Additive X)) :
    (IsPure (affineY (torusGrading π)) N ∧ ∃ x, x ≠ 0 ∧ N = AddSubmonoid.closure {x}) ↔
      ∃ a ∈ roots π, N = AddSubmonoid.closure {a} :=
  red_pure_mono_iff_fieldBar D.baseChange N

/-- **Corollary `cor:red-monogenic`** over any field: `α ↦ ℕα` is a bijection from `Φ` onto the
nonzero monogenerated pure magnets. -/
theorem red_mono_bijOn_field (D : SplitReductiveData.WithRootDatum π) :
    Set.BijOn (fun a : Additive X => AddSubmonoid.closure {a}) (roots π)
      {N | IsPure (affineY (torusGrading π)) N ∧ (∃ x, N = AddSubmonoid.closure {x}) ∧
        N ≠ ⊥} :=
  red_mono_bijOn_fieldBar D.baseChange

/-- **Theorem `thm:red-parabolic`, `E(G^N) = ℕB + ℕ(-ξ)`**, over any field. -/
theorem red_parabolic_hull_field (D : SplitReductiveData.WithRootDatum π)
    {N : AddSubmonoid (Additive X)} (hBN : D.P.root '' D.b.support ⊆ N) :
    sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N} =
      AddSubmonoid.closure (D.P.root '' D.b.support ∪
        -Parabolic.xi (D.P.root '' D.b.support) N) := by
  rw [← hull_baseChange (AlgebraicClosure k) π]
  exact red_parabolic_hull_lattice D.baseChange hBN

open TauCeti.Cocharacter in
/-- **Theorem `thm:red-parabolic`, `G^N = P_ξ`**, over any field: for a magnet `N ⊇ B`,
`ξ = {α ∈ B | -α ∈ N}` and a cocharacter `λ` vanishing on `ξ` and positive on `B \ ξ`
(`G` geometrically connected). -/
theorem red_parabolic_field (D : SplitReductiveData.WithRootDatum π)
    [ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] H))]
    (ψ : X →* Multiplicative ℤ) {N : AddSubmonoid (Additive X)}
    (hBN : D.P.root '' D.b.support ⊆ N)
    (hξ : ∀ α ∈ Parabolic.xi (D.P.root '' D.b.support) N, pairingHom ψ α = 0)
    (hpos : ∀ α ∈ D.P.root '' D.b.support,
      α ∉ Parabolic.xi (D.P.root '' D.b.support) N → 0 < pairingHom ψ α) :
    magnetIdeal (torusGrading π) N =
      (parabolicDefiningHopfIdeal (π.cocharacter ψ)).toIdeal := by
  have S := RootSystem.RootDatum.simpleSystem D.P D.b
  have hY : affineY (torusGrading π)
      (sInf {L | affineY (torusGrading π) L = affineY (torusGrading π) N}) =
        affineY (torusGrading π) N := by
    rw [affineY_infPreserving (torusGrading π)]
    apply le_antisymm
    · exact iInf₂_le (f := fun L _ => affineY (torusGrading π) L) N (Set.mem_ofPred.2 rfl)
    · exact le_iInf₂ fun L hL => (Set.mem_ofPred.1 hL).ge
  rw [red_parabolic_hull_field D hBN] at hY
  have hI : magnetIdeal (torusGrading π) (AddSubmonoid.closure (D.P.root '' D.b.support ∪
      -Parabolic.xi (D.P.root '' D.b.support) N)) = magnetIdeal (torusGrading π) N := hY
  rw [← hI]
  refine Parabolic.magnetIdeal_basis_neg_eq_parabolic π ψ ?_ hξ hpos
  rw [← D.range_root]
  exact S.pos_or_neg

end Field

end AlgMag.Reductive
