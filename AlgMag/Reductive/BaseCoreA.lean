/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BorelRouteReal
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Representability
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.Algebra.Polynomial.Laurent.Polynomial
import AlgMag.Reductive.GLDiagonalCochar

/-!
# `BaseCore`, part (a): `B ⊆ P(ν₀)` and `B' ⊆ P(−ν₀)`

Ideals order subgroups contravariantly: `P ν ≤ B` means `V(B) ⊆ V(P ν)`.

* `le_of_factor` (proved): if `ν = l ∘ (H → H/B)` is a cocharacter of `G` landing in `V(B)`
  and the dynamic parabolic of `l` inside `V(B)` is all of `V(B)` (`P_B(l) = ⊥`), then
  `B ⊆ P_G(ν)`.  Proof on points: the universal point `H → H/B` of `V(B)` lies in `P_B(l)`,
  hence (functoriality, ported from upstream Tau Ceti `Dynamic/ClosedImmersion/Basic.lean`
  and `Parabolic.lean`) in `P_G(ν)`, so it kills `P_G(ν)`.
* `baseCoreA_of_dynamic` (proved): part (a) from the single named input `BaseADynamic C`.
* `BaseADynamic C` (named, NOT proved): one regular `ν₀` and Borels `B, B' ⊇ T` such that
  `ν₀` factors through `V(B)` with `P_B(ν₀) = V(B)`, and `−ν₀` factors through `V(B')` with
  `P_{B'}(−ν₀) = V(B')`.  This is the dynamic description of a Borel (`B = T ⋉ B_u`,
  `ν₀` positive on the weights of `Lie B_u`) together with the existence of the opposite
  Borel.  True for `GL₂`: `B` upper, `B'` lower triangular, `ν₀ = diag(t, 1)`.
-/

open Magnetism TauCeti TauCeti.Cocharacter

namespace AlgMag.Reductive.BaseCoreA

open AlgMag.Reductive.BorelRoute AlgMag.Reductive.BorelRouteReal

universe u

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

local notation "Hf" => FiniteTypeCommHopfAlgCat.of k H

/-! ### Ported from upstream Tau Ceti `Dynamic/ClosedImmersion` (not in the pinned copy) -/

section Port

open WithConv

variable {R H' K A : Type*} [CommSemiring R] [Semiring H'] [Semiring K]
variable [_root_.HopfAlgebra R H'] [_root_.HopfAlgebra R K]
variable [CommSemiring A] [Algebra R A]

theorem mapDomain_genericPoint' (φ : H' →ₐc[R] K) (l : K →ₐc[R] LaurentPolynomial R) :
    BialgHom.mapDomain φ (genericPoint A l) = genericPoint A (l.comp φ) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  simp [BialgHom.mapDomain_apply, genericPoint_eq_pointsHom, pointsHom_apply]

theorem mapDomain_constPoint' (φ : H' →ₐc[R] K) (g : WithConv (K →ₐ[R] A)) :
    BialgHom.mapDomain φ (constPoint A g) = constPoint A (BialgHom.mapDomain φ g) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  simp [constPoint_apply, BialgHom.mapDomain_apply]

theorem mapDomain_conjugate' (φ : H' →ₐc[R] K) (l : K →ₐc[R] LaurentPolynomial R)
    (g : WithConv (K →ₐ[R] A)) :
    BialgHom.mapDomain φ (conjugate A l g) = conjugate A (l.comp φ) (BialgHom.mapDomain φ g) := by
  simp only [conjugate_apply, map_mul, map_inv, mapDomain_genericPoint', mapDomain_constPoint']

theorem mapDomain_mem_parabolic' (φ : H' →ₐc[R] K) (l : K →ₐc[R] LaurentPolynomial R)
    {g : WithConv (K →ₐ[R] A)} (hg : g ∈ parabolic A l) :
    BialgHom.mapDomain φ g ∈ parabolic A (l.comp φ) := by
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  exact mem_parabolic_of_eq (F := BialgHom.mapDomain φ F) (by
    rw [← BialgHom.mapDomain_ofPolyPoint, hF, mapDomain_conjugate'])

/-- Upstream `mem_parabolic_iff_of_surjective`, hard direction: a point of a closed subgroup
lies in its dynamic parabolic once its image lies in the ambient dynamic parabolic. -/
theorem mem_parabolic_of_surjective' (φ : H' →ₐc[R] K) (hφ : Function.Surjective φ)
    (l : K →ₐc[R] LaurentPolynomial R) {g : WithConv (K →ₐ[R] A)}
    (hg : BialgHom.mapDomain φ g ∈ parabolic A (l.comp φ)) : g ∈ parabolic A l := by
  obtain ⟨F, hF⟩ := mem_parabolic_iff.mp hg
  have hvalue (x : H') : Polynomial.toLaurent (F.ofConv x) =
      (conjugate A l g).ofConv (φ x) := by
    have hv := congrArg (fun p : WithConv (H' →ₐ[R] LaurentPolynomial A) ↦ p.ofConv x) hF
    rw [← mapDomain_conjugate'] at hv
    simpa [ofPolyPoint_apply, BialgHom.mapDomain_apply] using hv
  have hcoeff (y : K) (n : ℤ) (hn : n < 0) :
      ((conjugate A l g).ofConv y).coeff n = 0 := by
    obtain ⟨x, rfl⟩ := hφ y
    rw [← hvalue x]
    exact TauCeti.exists_toLaurent_eq_iff.mp ⟨F.ofConv x, rfl⟩ n hn
  exact mem_parabolic_iff_forall_coeff_conjugate_eq_zero.mpr hcoeff

end Port

/-- `ν` factors through `V(B)` and its dynamic parabolic in `V(B)` is all of `V(B)`. -/
def DynFull (B : HopfIdeal k H) (ν : H →ₐc[k] LaurentPolynomial k) : Prop :=
  ∃ l : (H ⧸ B.toIdeal) →ₐc[k] LaurentPolynomial k,
    l.comp (mk B) = ν ∧ parabolicDefiningHopfIdeal l = ⊥

/-- If `P_B(ν) = V(B)` then `V(B) ⊆ P_G(ν)`. -/
theorem le_of_factor {B : HopfIdeal k H} {ν : H →ₐc[k] LaurentPolynomial k}
    (h : DynFull B ν) : P ν ≤ B := by
  obtain ⟨l, hl, hP⟩ := h
  let A := H ⧸ B.toIdeal
  let g : WithConv (A →ₐ[k] A) := WithConv.toConv (AlgHom.id k A)
  have hg : g ∈ parabolic A l := by
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := A), hP,
      CommHopfAlgCat.quotientPointsSubgroup_bot]
    trivial
  have h2 := mapDomain_mem_parabolic' (mk B) l hg
  rw [hl, ← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := A),
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at h2
  intro x hx
  have h3 := h2 x hx
  simp only [BialgHom.mapDomain_apply, g] at h3
  have h4 : (Ideal.Quotient.mk B.toIdeal x) = 0 := h3
  exact (Ideal.Quotient.eq_zero_iff_mem.mp h4)

/-- **Part (a) of `BaseCore`.** -/
def BaseCoreA (C : HopfIdeal k H) : Prop :=
  ∃ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧ P ν ≤ B) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧ P ν.oppositeCocharacter ≤ B')

/-- **The named input**: dynamic description of a Borel and of its opposite. -/
def BaseADynamic (C : HopfIdeal k H) : Prop :=
  ∃ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧ DynFull B ν) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧ DynFull B' ν.oppositeCocharacter)

theorem baseCoreA_of_dynamic {C : HopfIdeal k H} (h : BaseADynamic C) : BaseCoreA C := by
  obtain ⟨ν, hν, ⟨B, hB, hd⟩, ⟨B', hB', hd'⟩⟩ := h
  exact ⟨ν, hν, ⟨B, hB, le_of_factor hd⟩, ⟨B', hB', le_of_factor hd'⟩⟩

/-! ### Step (3) of the `GL_N` route: transfer along a closed immersion `G ↪ GL_N` -/

section GLN

variable {HN : Type u} [CommRing HN] [HopfAlgebra k HN]

/-- If `ι : O(GL_N) ↠ O(G)` is a closed immersion, `ν` a cocharacter of `G`, and
`V(B) ⊆ P_{GL_N}(ν ∘ ι)` (as ideals: `P(ν.comp ι) ≤ ι⁻¹ B`), then `V(B) ⊆ P_G(ν)`. -/
theorem le_of_le_comap_GL {B : HopfIdeal k H} {ν : H →ₐc[k] LaurentPolynomial k}
    (ι : HN →ₐc[k] H) (hι : Function.Surjective ι)
    (h : parabolicDefiningHopfIdeal (ν.comp ι) ≤ B.comapOfSurjective ι hι) : P ν ≤ B := by
  let A := H ⧸ B.toIdeal
  let g : WithConv (H →ₐ[k] A) := WithConv.toConv (Ideal.Quotient.mkₐ k B.toIdeal)
  have hgN : BialgHom.mapDomain ι g ∈ parabolic A (ν.comp ι) := by
    rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := A),
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    have hx' := HopfIdeal.mem_comapOfSurjective.mp (h hx)
    simp only [BialgHom.mapDomain_apply, g]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx'
  have hg := mem_parabolic_of_surjective' ι hι ν hgN
  rw [← quotientPointsSubgroup_parabolicDefiningHopfIdeal (A := A),
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg
  intro x hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hg x hx)

end GLN

/-- **Named input, `GL_N` form** (steps (1), (2) and the opposite Borel of the route):
a closed immersion `G ↪ GL_N`, a regular `ν₀` of `G`, and Borels `B, B'` of `G` with
`B ⊆ P_{GL_N}(ν₀)` and `B' ⊆ P_{GL_N}(−ν₀)`. For `GL₂` itself: `ι = id`, `ν₀ = diag(t,1)`,
`B`, `B'` upper and lower triangular. -/
def BaseAGL (C : HopfIdeal k H) : Prop :=
  ∃ (HN : Type u) (_ : CommRing HN) (_ : HopfAlgebra k HN) (ι : HN →ₐc[k] H)
    (hι : Function.Surjective ι) (ν : H →ₐc[k] LaurentPolynomial k), IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧
      parabolicDefiningHopfIdeal (ν.comp ι) ≤ B.comapOfSurjective ι hι) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧
      parabolicDefiningHopfIdeal (ν.oppositeCocharacter.comp ι) ≤ B'.comapOfSurjective ι hι)

theorem baseCoreA_of_GL {C : HopfIdeal k H} (h : BaseAGL C) : BaseCoreA C := by
  obtain ⟨HN, _, _, ι, hι, ν, hν, ⟨B, hB, hd⟩, ⟨B', hB', hd'⟩⟩ := h
  exact ⟨ν, hν, ⟨B, hB, le_of_le_comap_GL ι hι hd⟩, ⟨B', hB', le_of_le_comap_GL ι hι hd'⟩⟩

/-! ### `BaseAGL` in diagonal/weight form -/

open TauCeti.GeneralLinear AlgMag.Reductive.GLDiagonalCochar in
theorem diagCochar_neg {N : ℕ} (w : Fin N → ℤ) :
    diagCochar k (-w) = (diagCochar k w).oppositeCocharacter := by
  apply BialgHom.coe_toAlgHom_injective
  apply coordinateHopfAlgebra_algHom_ext k N
  intro i j
  show diagCochar k (-w) (coordinateHopfAlgebraAlgEquiv k N
      (coordinateRingMap k N (MvPolynomial.X (i, j)))) =
    (diagCochar k w).oppositeCocharacter (coordinateHopfAlgebraAlgEquiv k N
      (coordinateRingMap k N (MvPolynomial.X (i, j))))
  rw [diagCochar_X, BialgHom.oppositeCocharacter_apply, diagCochar_X]
  split_ifs <;> simp

open TauCeti.GeneralLinear AlgMag.Reductive.GLDiagonalCochar in
/-- **Named input, weight form**: a closed immersion `ι : G ↪ GL_N` with `ν₀ ∘ ι = diag(t^w)`
(i.e. `T` diagonal, `ν₀` restricting to `diag(t^w)`), `ν₀` regular, and Borels `B, B'` of `G`
that are `w`-block upper (resp. `−w`-block upper, i.e. lower) triangular in `GL_N`.
For `GL₂`: `ι = id`, `w = (1,0)`, `B` upper, `B'` lower triangular. -/
def BaseAGLw (C : HopfIdeal k H) : Prop :=
  ∃ (N : ℕ) (ι : coordinateHopfAlgebra k N →ₐc[k] H) (hι : Function.Surjective ι)
    (w : Fin N → ℤ) (ν : H →ₐc[k] LaurentPolynomial k),
    ν.comp ι = diagCochar k w ∧ IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧
      weightParabolicDefiningHopfIdeal k w ≤ B.comapOfSurjective ι hι) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧
      weightParabolicDefiningHopfIdeal k (-w) ≤ B'.comapOfSurjective ι hι)

open TauCeti.GeneralLinear AlgMag.Reductive.GLDiagonalCochar in
theorem baseAGL_of_w {C : HopfIdeal k H} (h : BaseAGLw C) : BaseAGL C := by
  obtain ⟨N, ι, hι, w, ν, hνw, hν, ⟨B, hB, hd⟩, ⟨B', hB', hd'⟩⟩ := h
  have hopp : ν.oppositeCocharacter.comp ι = diagCochar k (-w) := by
    rw [diagCochar_neg, ← hνw]; rfl
  refine ⟨_, inferInstance, inferInstance, ι, hι, ν, hν, ⟨B, hB, ?_⟩, ⟨B', hB', ?_⟩⟩
  · rw [hνw, parabolicDefiningHopfIdeal_diagCochar]; exact hd
  · rw [hopp, parabolicDefiningHopfIdeal_diagCochar]; exact hd'

theorem baseCoreA_of_w {C : HopfIdeal k H} (h : BaseAGLw C) : BaseCoreA C :=
  baseCoreA_of_GL (baseAGL_of_w h)

open TauCeti.GeneralLinear AlgMag.Reductive.GLDiagonalCochar in
/-- **Named input, weight-basis form** (what remains of step (1) is only the existence of a
`ν₀`-weight basis of a faithful comodule): a faithful finite comodule `M` of `G` with a basis
`b` of `ν₀`-weight vectors of weights `w`, `ν₀` regular, and Borels `B, B'` which are
`w`- resp. `(−w)`-block upper triangular in the coordinates `ρ_b : O(GL_N) ↠ O(G)`. -/
def BaseAWeightBasis (C : HopfIdeal k H) : Prop :=
  ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M) (N : ℕ)
    (b : Module.Basis (Fin N) k M) (hb : Function.Surjective (Comodule.coordinateBialgHom b))
    (w : Fin N → ℤ) (ν : H →ₐc[k] LaurentPolynomial k),
    (∀ j, TensorProduct.map LinearMap.id ν.toLinearMap
        (Comodule.coact (R := k) (C := H) (M := M) (b j)) = b j ⊗ₜ LaurentPolynomial.T (w j)) ∧
    IsRegular C ν ∧
    (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧
      weightParabolicDefiningHopfIdeal k w ≤ B.comapOfSurjective _ hb) ∧
    (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧
      weightParabolicDefiningHopfIdeal k (-w) ≤ B'.comapOfSurjective _ hb)

theorem baseAGLw_of_weightBasis {C : HopfIdeal k H} (h : BaseAWeightBasis C) : BaseAGLw C := by
  obtain ⟨M, _, _, _, N, b, hb, w, ν, hw, hν, hB, hB'⟩ := h
  exact ⟨N, _, hb, w, ν,
    AlgMag.Reductive.GLDiagonalCochar.comp_coordinateBialgHom_eq_diagCochar b ν w hw, hν, hB, hB'⟩

theorem baseCoreA_of_weightBasis {C : HopfIdeal k H} (h : BaseAWeightBasis C) : BaseCoreA C :=
  baseCoreA_of_w (baseAGLw_of_weightBasis h)

open TauCeti.GeneralLinear in
/-- **The named input after step (1)** (only step (2) and the opposite Borel remain):
a regular `ν₀` such that, in every faithful finite comodule with a `ν₀`-weight basis of weights
`w`, some Borel is `w`-block upper triangular and some Borel is `(−w)`-block upper triangular.
For `GL₂` with its standard comodule `k²`: `ν₀ = diag(t,1)`, `w = (1,0)`, upper / lower. -/
def BaseAFlag (C : HopfIdeal k H) : Prop :=
  ∃ ν : H →ₐc[k] LaurentPolynomial k, IsRegular C ν ∧
    ∀ (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : Comodule k H M) (N : ℕ)
      (b : Module.Basis (Fin N) k M) (hb : Function.Surjective (Comodule.coordinateBialgHom b))
      (w : Fin N → ℤ),
      (∀ j, TensorProduct.map LinearMap.id ν.toLinearMap
        (Comodule.coact (R := k) (C := H) (M := M) (b j)) = b j ⊗ₜ LaurentPolynomial.T (w j)) →
      (∃ B, HopfIdeal.IsBorelOverAlgClosed k Hf B ∧
        weightParabolicDefiningHopfIdeal k w ≤ B.comapOfSurjective _ hb) ∧
      (∃ B', HopfIdeal.IsBorelOverAlgClosed k Hf B' ∧
        weightParabolicDefiningHopfIdeal k (-w) ≤ B'.comapOfSurjective _ hb)

theorem baseCoreA_of_flag {C : HopfIdeal k H} (h : BaseAFlag C) : BaseCoreA C := by
  obtain ⟨ν, hν, hflag⟩ := h
  obtain ⟨M, i1, i2, i3, N, b, w, hb, hw⟩ :=
    AlgMag.Reductive.GLDiagonalCochar.exists_weightBasis_embedding (K := k) (H := H) ν
  obtain ⟨hB, hB'⟩ := hflag M i1 i2 i3 N b hb w hw
  exact baseCoreA_of_weightBasis ⟨M, i1, i2, i3, N, b, hb, w, ν, hw, hν, hB, hB'⟩

end AlgMag.Reductive.BaseCoreA
