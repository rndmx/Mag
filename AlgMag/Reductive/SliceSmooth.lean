/-
Smoothness of the pieces of the regular slice (C2(d)).
-/
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Reductive.RootGroups
import TauCeti.RingTheory.Smooth.Retract
import AlgMag.Reductive.RegularSlice
import Mathlib.Algebra.AffineMonoid.UniqueSums
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SmoothConnected
import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth

/-!
# The source of the regular slice is smooth

* `O((G^N)°)` smooth: use `smooth_compAlg` (RegularSliceEtale.lean).
* `SliceSmooth.smooth_tensor`, `SliceSmooth.smooth_tensor3`: tensor products of smooth
  `k`-algebras are smooth.
* `SliceSmooth.smooth_unipotent`: the dynamic unipotent quotient `O(U(λ))` is smooth.
-/

universe u v w x

open Magnetism TauCeti TauCeti.HopfIdeal WithConv
open scoped TensorProduct

namespace AlgMag.Reductive.SliceSmooth

/-- A tensor product of smooth `k`-algebras is smooth. -/
theorem smooth_tensor {k : Type u} {A : Type v} {B : Type w} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra.Smooth k A] [Algebra.Smooth k B] :
    Algebra.Smooth k (A ⊗[k] B) := by
  have : Algebra.Smooth A (A ⊗[k] B) := inferInstance
  exact Algebra.Smooth.comp k A (A ⊗[k] B)

/-- `(A ⊗ B) ⊗ C` is smooth when `A`, `B`, `C` are (shape of `sliceSource`). -/
theorem smooth_tensor3 {k : Type u} {A : Type v} {B : Type w} {C : Type x} [CommRing k]
    [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B] [Algebra k C]
    [Algebra.Smooth k A] [Algebra.Smooth k B] [Algebra.Smooth k C] :
    Algebra.Smooth k ((A ⊗[k] B) ⊗[k] C) :=
  haveI : Algebra.Smooth k (A ⊗[k] B) := smooth_tensor
  smooth_tensor

/-- The dynamic unipotent subgroup `U(λ)` of a smooth affine group is smooth. -/
theorem smooth_unipotent {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [Algebra.Smooth k H] (l : H →ₐc[k] LaurentPolynomial k) :
    Algebra.Smooth k (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal) :=
  let Hc : FiniteTypeCommHopfAlgCat.{u, u} k := FiniteTypeCommHopfAlgCat.of (R := k) H
  haveI : Algebra.Smooth k Hc := ‹Algebra.Smooth k H›
  BialgHom.smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal (H := Hc) l


section Retract

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **`G^M_e` is a retract of `G^M`** (pointed `M`), through `g ↦ g · lim(g)⁻¹`; hence it is
smooth when `G` is. -/
theorem smooth_quotient_prescribedUnitIdeal [Algebra.Smooth k H] (M : Magnet (Additive X))
    (hM : ∀ a ∈ M, ∀ b ∈ M, a + b = 0 → a = 0) :
    Algebra.Smooth k (H ⧸ prescribedUnitIdeal π M) := by
  set J := magnetIdeal (torusGrading π) M
  set P := prescribedUnitIdeal π M
  have hJ : Algebra.Smooth k (H ⧸ J) := by
    have := smooth_quotient_magnetHopfIdeal π M
    rwa [magnetHopfIdeal_toIdeal] at this
  have hJP : J ≤ P := le_sup_left
  let g : WithConv (H →ₐ[k] H ⧸ J) := toConv (Ideal.Quotient.mkₐ k J)
  have hg : g ∈ attractorSubgroup π M (H ⧸ J) := by
    rw [mem_attractorSubgroup π]
    intro x hx
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  let G : attractorSubgroup π M (H ⧸ J) := ⟨g, hg⟩
  let L : attractorSubgroup π M (H ⧸ J) :=
    ⟨limitHom π hM _ G, attractorSubgroup_bot_le π _ (limitHom_mem π hM _ G)⟩
  let r := G * L⁻¹
  have hr : r.1 ∈ prescribedUnitSubgroup π hM (H ⧸ J) := by
    refine (mem_prescribedUnitSubgroup π hM _).2 ⟨r.2, ?_⟩
    have hL : limitHom π hM _ L = L.1 :=
      limitHom_of_mem_bot π hM _ L (limitHom_mem π hM _ G)
    change limitHom π hM _ (G * L⁻¹) = 1
    rw [map_mul, map_inv, hL]
    exact mul_inv_cancel _
  have hker : P ≤ RingHom.ker r.1.ofConv := (prescribedUnitIdeal_le_ker_iff hM r.1).2 hr
  let α : (H ⧸ P) →ₐ[k] H ⧸ J := Ideal.Quotient.liftₐ P r.1.ofConv (fun a ha => hker ha)
  let β : (H ⧸ J) →ₐ[k] H ⧸ P := Ideal.Quotient.factorₐ k hJP
  have hβL : β.comp L.1.ofConv = (1 : WithConv (H →ₐ[k] H ⧸ P)).ofConv := by
    ext h
    induction h using induction_torusGrading (π := π) with
    | h0 => simp
    | hadd x y hx hy => rw [AlgHom.comp_apply, map_add, map_add, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, hx, hy, map_add]
    | hmem χ x hx =>
      rw [AlgHom.comp_apply, AlgHom.convOne_apply]
      change β (constCoeff _ ((orbitHom π _ g).ofConv x)) = _
      rw [constCoeff_orbitHom_of_mem _ hx]
      by_cases hχ : χ = 0
      · subst hχ
        simp only [↓reduceIte]
        change Ideal.Quotient.mk P x = _
        rw [← Ideal.Quotient.mkₐ_eq_mk k, ← AlgHom.commutes (Ideal.Quotient.mkₐ k P),
          Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
        exact Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, rfl⟩)
      · simp only [hχ, ↓reduceIte]
        rw [counit_eq_zero_of_mem hχ hx, map_zero, map_zero]
  have hβr : β.comp r.1.ofConv = Ideal.Quotient.mkₐ k P := by
    change β.comp (g * L.1⁻¹).ofConv = _
    rw [AlgHom.comp_convMul_distrib]
    have h2 : β.comp (L.1⁻¹).ofConv = ((toConv (β.comp L.1.ofConv))⁻¹).ofConv := rfl
    rw [h2, hβL]
    change ((toConv (β.comp (Ideal.Quotient.mkₐ k J))) * (1 : WithConv (H →ₐ[k] H ⧸ P))⁻¹).ofConv
      = _
    rw [inv_one, mul_one]
    rfl
  have hsplit : β.comp α = AlgHom.id k (H ⧸ P) := by
    apply Ideal.Quotient.algHom_ext
    ext x
    change β (α (Ideal.Quotient.mk P x)) = Ideal.Quotient.mk P x
    exact congrArg (fun F : H →ₐ[k] H ⧸ P => F x) hβr
  have : Algebra.FormallySmooth k (H ⧸ P) := Algebra.FormallySmooth.of_retract' α β hsplit
  have : Algebra.FinitePresentation k (H ⧸ P) := by
    have : Algebra.FiniteType k (H ⧸ P) := Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ_surjective k P)
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end Retract

/-- **The split torus `T = D(X)` is smooth** for a lattice `X`. -/
theorem smooth_monoidAlgebra {k : Type u} {X : Type u} [Field k] [CommGroup X] [Monoid.FG X]
    [IsMulTorsionFree X] : Algebra.Smooth k (MonoidAlgebra k X) := by
  have : TwoUniqueProds X := AffineMonoid.to_twoUniqueProds
  have : UniqueProds X := inferInstance
  have : Group.FG X := Group.fg_iff_monoid_fg.mpr ‹_›
  let G : FGCommGrpCat.{u} := FGCommGrpCat.of X
  have : UniqueProds G := (inferInstance : UniqueProds X)
  exact smoothCommHopfAlgProperty_of_geometricallyReduced k
    (DiagonalizableGroup.coordinateRing k G).obj
    (DiagonalizableGroup.geometricallyReduced_coordinateRing (G := G) k)

section Slice

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Module.Finite k (Bialgebra.CotangentSpace k H)]
  [Algebra.Smooth k H]

/-- **`U⁺ = G^{[R ∩ λ>0⟩}_e` is smooth.** -/
theorem smooth_slice (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ) :
    Algebra.Smooth k (H ⧸ (sliceIdeal π N ψ).toIdeal) := by
  rw [sliceIdeal_toIdeal]
  exact smooth_quotient_prescribedUnitIdeal π _ (sliceMagnet_pointed π N ψ)

/-- **`O(U⁻) ⊗ O(U⁺) ⊗ O(T)` is smooth** (`X` a lattice). -/
theorem smooth_sliceSource [IsAlgClosed k] [Algebra.FiniteType k H] [Monoid.FG X]
    [IsMulTorsionFree X] (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ) :
    Algebra.Smooth k (sliceSource π N ψ) :=
  haveI := smooth_slice π N ψ
  haveI := smooth_slice π N ψ⁻¹
  haveI : Algebra.Smooth k (MonoidAlgebra k X) := smooth_monoidAlgebra
  smooth_tensor3

end Slice

end AlgMag.Reductive.SliceSmooth
