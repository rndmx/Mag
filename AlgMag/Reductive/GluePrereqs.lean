/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ComponentsNormalizer
import AlgMag.Reductive.RegularCentralizer
import AlgMag.Reductive.SplitReductive
import Mathlib.Algebra.AffineMonoid.UniqueSums

/-!
# Prerequisites for gluing C1–C3 (`components-NGT-B.md`)

Over an algebraically closed field `k`, `G = Spec H` finite type, `T = D(X)`:
* `compSubgroup π N`: `K(k) = (G^N)°(k)` as a subgroup of `G(k)`, with membership
  `mem_compSubgroup`: `h ∈ K(k) ↔ compIdeal π N ≤ ker h`;
* `conj_mem_compSubgroup`: conjugation by `G^N(k)` preserves `K(k)` (`(G^N)°` is
  characteristic in `G^N`);
* `magnetIdeal_bot_eq_ker`: `G^0 = T` for split reductive data (`Z_G(T) = T`, from
  `normalizer_cover`), and `compIdeal_bot_iff` / `compIdeal_bot_iff_of_torsionFree`:
  `(G^0)° = T` when `T` is connected (e.g. `X` a lattice) — the hypothesis `hT` of C1;
* `IsNormalizingWith.mapValue`, `mem_W_of_isNormalizingWith`: the automorphism of a
  normalizing `k`-point lies in `W`; `normalizerW D`: the subgroup `N_G(T)(k)` with
  automorphisms in `W`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.HopfIdeal WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-! ### Base change of normalizing points, and `σ ∈ W` -/

section Normalizing

open AlgMag.Weyl

omit [DecidableEq X] in
/-- Normalizing points are stable under base change `A → B`. -/
lemma IsNormalizingWith.mapValue {A B : Type*} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (φ : A →ₐ[k] B) {g : WithConv (H →ₐ[k] A)} {σ : X ≃* X}
    (hg : IsNormalizingWith π A g σ) : IsNormalizingWith π B (AlgHom.mapValue φ g) σ := by
  set Φ : A ⊗[k] MonoidAlgebra k X →ₐ[k] B ⊗[k] MonoidAlgebra k X :=
    Algebra.TensorProduct.map φ (AlgHom.id k _)
  have hincl : AlgHom.mapValue Φ (AlgHom.mapValue
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g) =
      AlgHom.mapValue (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := B)
        (B := MonoidAlgebra k X)) (AlgHom.mapValue φ g) := by
    simp only [AlgHom.mapValue_apply, ← AlgHom.comp_assoc, Φ,
      Algebra.TensorProduct.map_comp_includeLeft]
  have htw : ∀ f : X →* X, AlgHom.mapValue Φ (twistPoint π A f) = twistPoint π B f := by
    intro f
    simp only [twistPoint, AlgHom.mapValue_apply, ofConv_toConv, ← AlgHom.comp_assoc, Φ,
      Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
  have h := congrArg (AlgHom.mapValue Φ) hg
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hincl, ← twistPoint_id, htw, htw,
    twistPoint_id] at h
  rw [IsNormalizingWith, MulAut.conj_apply, h]

/-- **`σ ∈ W`.** The automorphism of a normalizing `k`-point lies in the Weyl group. -/
theorem mem_W_of_isNormalizingWith [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (D : SplitReductiveData π) {y : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hy : IsNormalizingWith π k y σ) : σ ∈ D.W :=
  (D.normalizer_cover (toAlgClosure y) σ
    (IsNormalizingWith.mapValue π (Algebra.ofId k (AlgebraicClosure k)) hy)).1

/-- `N_G(T)(k)` with automorphisms in `W`, as a subgroup (the `Nm` of C3). -/
def normalizerW [Module.Finite k (Bialgebra.CotangentSpace k H)] (D : SplitReductiveData π) :
    Subgroup (WithConv (H →ₐ[k] k)) where
  carrier := {n | ∃ w : D.W, IsNormalizingWith π k n w}
  one_mem' := ⟨1, isNormalizingWith_one π⟩
  mul_mem' := by
    rintro a b ⟨σ, ha⟩ ⟨τ, hb⟩
    exact ⟨τ * σ, IsNormalizingWith.mul π hb ha⟩
  inv_mem' := by
    rintro a ⟨σ, ha⟩
    exact ⟨σ⁻¹, IsNormalizingWith.inv π ha⟩

lemma mem_normalizerW [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (D : SplitReductiveData π) (n : WithConv (H →ₐ[k] k)) :
    n ∈ normalizerW π D ↔ ∃ w : D.W, IsNormalizingWith π k n w := Iff.rfl

/-- Every normalizing `k`-point lies in `normalizerW D`. -/
lemma mem_normalizerW_of_isNormalizingWith [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (D : SplitReductiveData π) {y : WithConv (H →ₐ[k] k)} {σ : X ≃* X}
    (hy : IsNormalizingWith π k y σ) : y ∈ normalizerW π D :=
  ⟨⟨σ, mem_W_of_isNormalizingWith π D hy⟩, hy⟩

end Normalizing

/-! ### `K(k) = (G^N)°(k)` as a subgroup, normal in `G^N(k)` -/

section Component

variable [IsAlgClosed k] [Algebra.FiniteType k H]

/-- **`K(k) = (G^N)°(k)`** as a subgroup of `G(k)`: the image of `(G^N)°(k) → G(k)`. -/
def compSubgroup (N : Magnet (Additive X)) : Subgroup (WithConv (H →ₐ[k] k)) :=
  (BialgHom.mapDomain (A := k) (compMk π N)).range

theorem mem_compSubgroup (N : Magnet (Additive X)) (h : WithConv (H →ₐ[k] k)) :
    h ∈ compSubgroup π N ↔ compIdeal π N ≤ RingHom.ker h.ofConv := by
  constructor
  · rintro ⟨y, rfl⟩ x hx
    have hx' : (compMk π N) x = 0 := hx
    show y.ofConv ((compMk π N) x) = 0
    rw [hx', map_zero]
  · intro hh
    set f := (compMk π N).toAlgHom
    let e := Ideal.quotientKerAlgEquivOfSurjective (f := f) (compMk_surjective π N)
    refine ⟨toConv ((Ideal.Quotient.liftₐ (RingHom.ker f) h.ofConv fun a ha => hh ha).comp
      e.symm.toAlgHom), ?_⟩
    apply WithConv.ofConv_injective
    ext x
    rw [BialgHom.mapDomain_apply, ofConv_toConv]
    show (Ideal.Quotient.liftₐ (RingHom.ker f) h.ofConv fun a ha => hh ha) (e.symm (f x)) = _
    rw [show e.symm (f x) = Ideal.Quotient.mk _ x from e.symm_apply_eq.2 rfl]
    rfl

/-- **`(G^N)°` is stable under conjugation by `G^N(k)`** (on the ideal level). -/
theorem conj_mem_compIdeal (N : Magnet (Additive X)) {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ attractorSubgroup π N k) {x : H} (hx : x ∈ compIdeal π N) :
    HopfAlgebra.pointConjugationAlgHom g x ∈ compIdeal π N := by
  set J := (magnetHopfIdeal π N).toIdeal
  set B := H ⧸ J
  have hgJ : J ≤ RingHom.ker g.ofConv := by
    rw [show J = magnetIdeal (torusGrading π) N from magnetHopfIdeal_toIdeal π N]
    exact (mem_attractorSubgroup π).1 hg
  set gb : WithConv (B →ₐ[k] k) := toConv (Ideal.Quotient.liftₐ J g.ofConv fun a ha => hgJ ha)
  have hgb : BialgHom.mapDomain (attrMk π N) gb = g := by
    apply WithConv.ofConv_injective; ext y; rfl
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  set C := B ⧸ (attrComp π N).toIdeal
  have hC : ConnectedSpace (PrimeSpectrum C) :=
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent
      (FiniteTypeCommHopfAlgCat.of (R := k) B)
  -- `mk_C ∘ Int(ḡ)^*` is a Hopf map to the connected `C`, so it kills `attrComp`.
  set φ : B →ₐc[k] C := (Bialgebra.Quotient.mkBialgHom (attrComp π N).toIdeal).comp
    (HopfAlgebra.pointConjugationBialgEquiv gb).toBialgHom
  have hle := CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
    (H := CommHopfAlgCat.of k B) (K := CommHopfAlgCat.of k C) (CommHopfAlgCat.ofHom φ)
  have hxb : Ideal.Quotient.mk J x ∈ (attrComp π N).toIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.1 hx
  have h1 := hle hxb
  have hmap : attrMk π N (HopfAlgebra.pointConjugationAlgHom g x) =
      HopfAlgebra.pointConjugationAlgHom gb (attrMk π N x) := by
    have := AlgHom.congr_fun (BialgHom.comp_pointConjugationAlgHom_mapDomain (attrMk π N) gb) x
    rw [hgb] at this
    exact this
  show Ideal.Quotient.mk _ (attrMk π N (HopfAlgebra.pointConjugationAlgHom g x)) = 0
  rw [hmap]
  have h2 : φ (Ideal.Quotient.mk J x) = 0 := h1
  rw [← h2]
  simp only [φ, BialgHom.comp_apply]
  rw [← HopfAlgebra.pointConjugationBialgEquiv_toAlgHom]
  rfl

/-- **Normality** (`hnorm` of C3): conjugation by `G^N(k)` preserves `K(k)`. -/
theorem conj_mem_compSubgroup (N : Magnet (Additive X)) {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ attractorSubgroup π N k) {h : WithConv (H →ₐ[k] k)}
    (hh : h ∈ compSubgroup π N) : g * h * g⁻¹ ∈ compSubgroup π N := by
  rw [mem_compSubgroup] at hh ⊢
  have hc := HopfAlgebra.comp_pointConjugationAlgHom (A := k) g h
  have hid : AlgHom.mapValue (H := H) (Algebra.ofId k k) = MonoidHom.id _ := by
    rw [show Algebra.ofId k k = AlgHom.id k k from Subsingleton.elim _ _]
    exact AlgHom.mapValue_id
  rw [hid, MonoidHom.id_apply] at hc
  rw [← hc]
  intro x hx
  rw [RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply]
  exact hh (conj_mem_compIdeal π N hg hx)

/-- `K(k) ≤ G^N(k)`. -/
lemma compSubgroup_le (N : Magnet (Additive X)) : compSubgroup π N ≤ attractorSubgroup π N k :=
  fun h hh => (mem_attractorSubgroup π).2
    ((magnetIdeal_le_compIdeal π N).trans ((mem_compSubgroup π N h).1 hh))

end Component

/-! ### `G^0 = T` and `(G^0)° = T` (the hypothesis `hT` of C1) -/

section Centralizer

open AlgMag.Weyl

/-- A point of `G^0(A)` centralizes `T`: it normalizes `T` with automorphism `1`. -/
lemma isNormalizingWith_one_of_mem_bot {A : Type u} [CommRing A] [Algebra k A]
    {g : WithConv (H →ₐ[k] A)} (hg : g ∈ attractorSubgroup π ⊥ A) :
    IsNormalizingWith π A g 1 := by
  set gg := AlgHom.mapValue
    (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := MonoidAlgebra k X)) g
  have horb : orbitHom π A g = gg := by
    apply WithConv.ofConv_injective
    ext a
    refine Submodule.iSup_induction (torusGrading π) (motive := fun a =>
      (orbitHom π A g).ofConv a = gg.ofConv a)
      ((isInternal_torusGrading π).submodule_iSup_eq_top ▸ Submodule.mem_top) ?_ ?_ ?_
    · intro χ a ha
      rw [AlgMag.Weyl.orbitHom_apply_of_mem g ha]
      simp only [gg, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply]
      by_cases hχ : χ = 0
      · subst hχ; rw [toMul_zero, ← MonoidAlgebra.one_def]
      · have h0 : g.ofConv a = 0 := (mem_attractorSubgroup π).1 hg
          (mem_magnetIdeal_of_notMem (N := (⊥ : Magnet (Additive X)))
            (by rw [AddSubmonoid.mem_bot]; exact hχ) ha)
        rw [h0, TensorProduct.zero_tmul, TensorProduct.zero_tmul]
    · simp
    · intro x y hx hy; rw [map_add, map_add, hx, hy]
  have h1 : (1 : X ≃* X).toMonoidHom = MonoidHom.id X := rfl
  rw [IsNormalizingWith, h1, twistPoint_id, MulAut.conj_apply]
  have h2 : torusPoint π A * gg * (torusPoint π A)⁻¹ = gg :=
    (show orbitHom π A g = torusPoint π A * gg * (torusPoint π A)⁻¹ from rfl).symm.trans horb
  have h3 : torusPoint π A * gg = gg * torusPoint π A := by
    calc torusPoint π A * gg = torusPoint π A * gg * (torusPoint π A)⁻¹ * torusPoint π A :=
          (inv_mul_cancel_right (G := WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X)) _ _).symm
      _ = gg * torusPoint π A := by rw [h2]
  rw [← h3]
  exact mul_inv_cancel_right (G := WithConv (H →ₐ[k] A ⊗[k] MonoidAlgebra k X)) _ _

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

omit [DecidableEq X] [Module.Finite k (Bialgebra.CotangentSpace k H)] in
/-- `torusPointOf` is `mapDomain π`. -/
lemma torusPointOf_eq (t : MonoidAlgebra k X →ₐ[k] AlgebraicClosure k) :
    torusPointOf π t = BialgHom.mapDomain π (toConv t) := rfl

/-- **`Z_G(T)(k) = T(k)`** from `normalizer_cover`: a `k`-point of `G^0` kills `ker π`. -/
theorem ker_le_of_mem_bot (D : SplitReductiveData π) {g : WithConv (H →ₐ[k] k)}
    (hg : g ∈ attractorSubgroup π ⊥ k) : RingHom.ker π.toAlgHom ≤ RingHom.ker g.ofConv := by
  have hn := IsNormalizingWith.mapValue π (Algebra.ofId k (AlgebraicClosure k))
    (isNormalizingWith_one_of_mem_bot π hg)
  obtain ⟨hσ, t, ht⟩ := D.normalizer_cover _ 1 hn
  obtain ⟨hσ', t0, ht0⟩ := D.normalizer_cover 1 1 (isNormalizingWith_one π)
  have hrep : toAlgClosure (D.rep ⟨1, hσ⟩) = (torusPointOf π t0)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← ht0]
  have hg' : toAlgClosure g = BialgHom.mapDomain π ((toConv t0)⁻¹ * toConv t) := by
    rw [map_mul, map_inv, ← torusPointOf_eq, ← torusPointOf_eq, ← hrep]
    exact ht
  intro x hx
  have hx' : π x = 0 := hx
  have := congrArg (fun p : WithConv (H →ₐ[k] AlgebraicClosure k) => p.ofConv x) hg'
  simp only [toAlgClosure, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.mapDomain_apply] at this
  rw [show ((π : H →ₐ[k] MonoidAlgebra k X) x) = 0 from hx', map_zero,
    Algebra.ofId_apply] at this
  rw [RingHom.mem_ker]
  exact (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)) (by rw [this, map_zero])

variable [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **`G^0 = T`** for split reductive data: `J_0 = ker π`. -/
theorem magnetIdeal_bot_eq_ker (D : SplitReductiveData π) :
    magnetIdeal (torusGrading π) ⊥ = RingHom.ker π.toAlgHom := by
  refine le_antisymm (magnetIdeal_le_ker_torus π ⊥) ?_
  set J := magnetIdeal (torusGrading π) ⊥
  have hS : Algebra.Smooth k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal) :=
    smooth_quotient_magnetHopfIdeal π ⊥
  rw [magnetHopfIdeal_toIdeal] at hS
  have : IsReduced (H ⧸ J) := isReduced_of_smooth k _
  have : Algebra.FiniteType k (H ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J) (Ideal.Quotient.mkₐ_surjective k J)
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine OpenCellNotes.eq_zero_of_forall_algHom (K := k) fun φ => ?_
  have hg : toConv (φ.comp (Ideal.Quotient.mkₐ k J)) ∈ attractorSubgroup π ⊥ k := by
    rw [mem_attractorSubgroup]
    intro y hy
    rw [RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]
  have := ker_le_of_mem_bot π D hg hx
  rwa [RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this

/-- **`(G^0)° = T`** (the hypothesis `hT` of C1), when `T` is connected. -/
theorem compIdeal_bot_iff (D : SplitReductiveData π)
    [hconn : ConnectedSpace (PrimeSpectrum (MonoidAlgebra k X))] :
    ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0 := by
  set B := H ⧸ (magnetHopfIdeal π ⊥).toIdeal
  have hJ : (magnetHopfIdeal π ⊥).toIdeal = RingHom.ker π.toAlgHom := by
    rw [magnetHopfIdeal_toIdeal, magnetIdeal_bot_eq_ker π D]
  -- `B ≃ k[X]` is connected, so the identity component ideal is `⊥`.
  have : Algebra.FiniteType k B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  let e : B ≃ₐ[k] MonoidAlgebra k X :=
    (Ideal.quotientEquivAlgOfEq k hJ).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := π.toAlgHom) D.surjective)
  have hB : ConnectedSpace (PrimeSpectrum B) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm.connectedSpace_iff.mp hconn
  have hbot : attrComp π ⊥ = ⊥ :=
    (HopfAlgebra.identityComponentHopfIdeal_eq_bot_iff_connectedSpace (k := k) (H := B)).2 hB
  intro x
  show Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, hbot, HopfIdeal.bot_toIdeal, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem, hJ]
  rfl

/-- **`(G^0)° = T`** for `X` a lattice (finitely generated, torsion-free). -/
theorem compIdeal_bot_iff_of_torsionFree (D : SplitReductiveData π) [Monoid.FG X]
    [IsMulTorsionFree X] : ∀ x, x ∈ compIdeal π ⊥ ↔ π x = 0 := by
  have : TwoUniqueProds X := AffineMonoid.to_twoUniqueProds
  have : IsDomain (MonoidAlgebra k X) := inferInstance
  have : IrreducibleSpace (PrimeSpectrum (MonoidAlgebra k X)) :=
    PrimeSpectrum.irreducibleSpace (R := MonoidAlgebra k X)
  exact compIdeal_bot_iff π D

end Centralizer

end AlgMag.Reductive
