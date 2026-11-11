/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Weyl.Normalizer

/-!
# The attractor of a group magnet is a centralizer; Weyl magnets

Mayeux, *Algebraic Magnetism*, Proposition 3.35 for magnets which are subgroups: if `L ≤ M` is a
subgroup of characters, the attractor `G^L` of the conjugation action of `T = D(X)` is the
centralizer `Z_G(D(X ⧸ L))` of the diagonalizable subgroup `D(X ⧸ L) ⊆ T`
(`magnetHopfIdeal_groupMagnet_eq_centralizer`, an equality of Hopf ideals).

For an automorphism `σ` of `X`, the Weyl magnet magnet `⟨(1 - σ)M⟩` is the group magnet of
`(1 - σ)X`, whose quotient torus `D(X ⧸ (1 - σ)X)` is the fixed subgroup `T^σ`; hence
`G^{⟨(1-σ)M⟩} = Z_G(T^σ)` (`magnetHopfIdeal_weylMagnet_eq_centralizer`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti WithConv

namespace AlgMag.Weyl

open AlgMag.Reductive

universe u v w

variable {R : Type u} {H : Type v} {X : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommGroup X]
variable (π : H →ₐc[R] MonoidAlgebra R X)
variable {A : Type*} [CommRing A] [Algebra R A]

/-- The magnet of a subgroup `L ≤ X` of characters (a group magnet in `M = Additive X`). -/
def groupMagnet (L : Subgroup X) : Magnet (Additive X) where
  carrier := {χ | Additive.toMul χ ∈ L}
  zero_mem' := L.one_mem
  add_mem' ha hb := L.mul_mem ha hb

@[simp] lemma mem_groupMagnet {L : Subgroup X} {χ : Additive X} :
    χ ∈ groupMagnet L ↔ Additive.toMul χ ∈ L := Iff.rfl

/-- The coordinate map of the diagonalizable subgroup `D(X ⧸ L) ⊆ D(X) ⊆ G`. -/
def quotientTorus (L : Subgroup X) : H →ₐc[R] MonoidAlgebra R (X ⧸ L) :=
  (MonoidAlgebra.mapDomainBialgHom R (QuotientGroup.mk' L)).comp π

variable {π} in
/-- The orbit map on a homogeneous coordinate of degree `χ`. -/
lemma orbitHom_apply_of_mem (g : WithConv (H →ₐ[R] A)) {χ : Additive X} {a : H}
    (ha : a ∈ torusGrading π χ) :
    (orbitHom π A g).ofConv a = g.ofConv a ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul χ) 1 := by
  have hl : (Algebra.TensorProduct.comm R _ _) (torusCoactLeft π a) =
      a ⊗ₜ[R] MonoidAlgebra.single (Additive.toMul χ) 1 := mem_torusGrading.mp ha
  rw [orbitHom_apply, hl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

variable [DecidableEq X]

/-- **Proposition 3.35 for group magnets, on points.** A point `g ∈ G(A)` lies in `G^L(A)`
(it kills the magnet ideal `J_L`) iff it kills the centralizer ideal of `D(X ⧸ L)`. -/
theorem magnetIdeal_groupMagnet_le_ker_iff (L : Subgroup X) (g : WithConv (H →ₐ[R] A)) :
    magnetIdeal (torusGrading π) (groupMagnet L) ≤ RingHom.ker g.ofConv ↔
      BialgHom.centralizerIdeal (quotientTorus π L) ≤ RingHom.ker g.ofConv := by
  classical
  set Φ : A ⊗[R] MonoidAlgebra R X →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L) :=
    Algebra.TensorProduct.map (AlgHom.id R A)
      (MonoidAlgebra.mapDomainAlgHom R R (QuotientGroup.mk' L))
  rw [BialgHom.centralizerIdeal_le_ker_iff_commute_of_injective (quotientTorus π L) g
    (AlgHom.id R _) Function.injective_id]
  set gg : WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L)) :=
    AlgHom.mapValue ((AlgHom.id R _).comp Algebra.TensorProduct.includeLeft) g
  set tt : WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L)) :=
    BialgHom.mapDomain (quotientTorus π L)
      (toConv ((AlgHom.id R _).comp Algebra.TensorProduct.includeRight))
  -- the image of the orbit map along `Φ` is `tt * gg * tt⁻¹`
  have hΦg : AlgHom.mapValue Φ
      (AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A)
        (B := MonoidAlgebra R X)) g) = gg := by
    apply WithConv.ofConv_injective
    ext h
    simp [gg, Φ, MonoidAlgebra.one_def, MonoidAlgebra.mapDomain_single]
  have hΦt : AlgHom.mapValue Φ (torusPoint π A) = tt := by
    apply WithConv.ofConv_injective
    ext h
    simp [tt, Φ, torusPoint, quotientTorus]
    rfl
  have horb : AlgHom.mapValue Φ (orbitHom π A g) = tt * gg * tt⁻¹ := by
    rw [orbitHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_mul, map_inv, hΦg, hΦt]
  have hcomm : Commute gg tt ↔ tt * gg * tt⁻¹ = gg := by
    have key : ∀ a b : WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L)),
        Commute a b ↔ b * a * b⁻¹ = a := fun a b =>
      ⟨fun h => (mul_inv_eq_iff_eq_mul
          (G := WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L)))).mpr h.eq.symm,
        fun h => ((mul_inv_eq_iff_eq_mul
          (G := WithConv (H →ₐ[R] A ⊗[R] MonoidAlgebra R (X ⧸ L)))).mp h).symm⟩
    exact key gg tt
  rw [hcomm, ← horb]
  -- pointwise reformulation
  have hpt : AlgHom.mapValue Φ (orbitHom π A g) = gg ↔
      ∀ h, Φ ((orbitHom π A g).ofConv h) = g.ofConv h ⊗ₜ[R] (1 : MonoidAlgebra R (X ⧸ L)) := by
    constructor
    · intro e h
      have := congrArg (fun F : WithConv (H →ₐ[R] _) => F.ofConv h) e
      simpa [gg] using this
    · intro e
      apply WithConv.ofConv_injective
      ext h
      simpa [gg] using e h
  rw [hpt]
  -- homogeneous coordinates
  have hhom : ∀ (χ : Additive X) (a : H), a ∈ torusGrading π χ →
      Φ ((orbitHom π A g).ofConv a) =
        g.ofConv a ⊗ₜ[R] MonoidAlgebra.single (QuotientGroup.mk' L (Additive.toMul χ)) 1 := by
    intro χ a ha
    rw [orbitHom_apply_of_mem g ha, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  constructor
  · intro hg h
    rw [← DirectSum.sum_support_decompose (torusGrading π) h, map_sum, map_sum, map_sum,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hχ := (DirectSum.decompose (torusGrading π) h χ).2
    rw [hhom χ _ hχ]
    by_cases hL : Additive.toMul χ ∈ L
    · have h1 : QuotientGroup.mk' L (Additive.toMul χ) = 1 := (QuotientGroup.eq_one_iff _).mpr hL
      rw [h1, ← MonoidAlgebra.one_def]
    · rw [hg (mem_magnetIdeal_of_notMem (show χ ∉ groupMagnet L from hL) hχ),
        TensorProduct.zero_tmul, TensorProduct.zero_tmul]
  · intro e
    rw [magnetIdeal, Ideal.span_le]
    simp only [Set.iUnion_subset_iff]
    intro χ hχ a ha
    have h1 := congrArg (LinearMap.tensorComponent
      (Comodule.monoidCoeff R (X ⧸ L) (QuotientGroup.mk' L (Additive.toMul χ)))) (e a)
    have hne : (1 : X ⧸ L) ≠ QuotientGroup.mk' L (Additive.toMul χ) := fun h =>
      hχ ((QuotientGroup.eq_one_iff (N := L) (Additive.toMul χ)).mp h.symm)
    rw [hhom χ a ha, LinearMap.tensorComponent_tmul, LinearMap.tensorComponent_tmul,
      Comodule.monoidCoeff_apply, Comodule.monoidCoeff_apply, MonoidAlgebra.one_def,
      MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply, if_pos rfl,
      if_neg hne, one_smul, zero_smul] at h1
    exact h1

/-- **Proposition 3.35 for group magnets.** The attractor `G^L` of a subgroup magnet is the
centralizer of `D(X ⧸ L)`: `J_L` equals the centralizer Hopf ideal. -/
theorem magnetHopfIdeal_groupMagnet_eq_centralizer (L : Subgroup X) :
    magnetHopfIdeal π (groupMagnet L) =
      BialgHom.centralizerHopfIdeal (quotientTorus π L) := by
  have key : ∀ I J : Ideal H, (∀ (A : Type v) [CommRing A] [Algebra R A]
      (g : WithConv (H →ₐ[R] A)), I ≤ RingHom.ker g.ofConv ↔ J ≤ RingHom.ker g.ofConv) →
      I = J := by
    intro I J hIJ
    refine le_antisymm ?_ ?_
    · intro x hx
      have h := (hIJ (H ⧸ J) (toConv (Ideal.Quotient.mkₐ R J))).mpr (fun y hy => by
        simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy) hx
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using h
    · intro x hx
      have h := (hIJ (H ⧸ I) (toConv (Ideal.Quotient.mkₐ R I))).mp (fun y hy => by
        simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hy) hx
      simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using h
  have hI := key _ _ fun A _ _ g => magnetIdeal_groupMagnet_le_ker_iff π L g
  ext x
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal, magnetHopfIdeal_toIdeal, hI,
    BialgHom.centralizerHopfIdeal_toIdeal]
  rfl

/-- Points of the attractor of a group magnet are the points of the centralizer of
`D(X ⧸ L)`. -/
theorem mem_attractorSubgroup_groupMagnet_iff (L : Subgroup X) (g : WithConv (H →ₐ[R] A)) :
    g ∈ attractorSubgroup π (groupMagnet L) A ↔
      (BialgHom.centralizerHopfIdeal (quotientTorus π L)).toIdeal ≤ RingHom.ker g.ofConv := by
  rw [mem_attractorSubgroup, ← magnetHopfIdeal_groupMagnet_eq_centralizer,
    magnetHopfIdeal_toIdeal]

/-- The subgroup `(1 - σ)X` of characters: the characters vanishing on the fixed subgroup
`T^σ = D(X ⧸ (1 - σ)X)`. -/
def fixedQuotient (σ : X ≃* X) : Subgroup X :=
  (MonoidHom.id X / σ.toMonoidHom).range

omit [DecidableEq X] in
/-- The Weyl magnet magnet is the group magnet of `(1 - σ)X`. -/
theorem weylMagnet_eq_groupMagnet (σ : X ≃* X) :
    weylMagnet σ = groupMagnet (fixedQuotient σ) := by
  have hs : joinIrredWeylMagnets σ = (groupMagnet (fixedQuotient σ) : Set (Additive X)) := by
    ext χ
    simp only [joinIrredWeylMagnets, Set.mem_range, SetLike.mem_coe, mem_groupMagnet, fixedQuotient,
      MonoidHom.mem_range, MonoidHom.div_apply, MonoidHom.id_apply,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨ψ, rfl⟩
      exact ⟨Additive.toMul ψ, by simp [toMul_sub]⟩
    · rintro ⟨y, hy⟩
      exact ⟨Additive.ofMul y, by rw [← ofMul_toMul χ, ← hy]; simp [ofMul_div]⟩
  rw [weylMagnet, hs, AddSubmonoid.closure_eq]

/-- **Attractor of a Weyl magnet magnet (F7).** `G^{⟨(1 - σ)M⟩} = Z_G(T^σ)`, where
`T^σ = D(X ⧸ (1 - σ)X)` is the fixed subgroup of `σ` in `T`. -/
theorem magnetHopfIdeal_weylMagnet_eq_centralizer (σ : X ≃* X) :
    magnetHopfIdeal π (weylMagnet σ) =
      BialgHom.centralizerHopfIdeal (quotientTorus π (fixedQuotient σ)) := by
  rw [weylMagnet_eq_groupMagnet, magnetHopfIdeal_groupMagnet_eq_centralizer]

end AlgMag.Weyl
