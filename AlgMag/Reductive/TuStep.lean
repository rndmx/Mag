/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TorusConjDyn
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Levi.Centralizer
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Coordinate
import TauCeti.Algebra.HopfAlgebra.Antipode
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Contraction
import AlgMag.Reductive.PushCocharacter
import AlgMag.Reductive.BigradedF3

/-!
# Step 4 of T1-dyn: the vector-group step `T · U_{≥n} ⇝ T · U_{≥n+1}`

Notes: `equivalence-reductive/T-steps.md` (T1-dyn, step 4) and `lean-tustep.md`.

`tuIdeal_step'` has exactly the statement of `tuIdeal_step` (TorusConjDyn.lean). Route:

* `exists_eq_sub_of_natural_cocycle` (PROVED): T1-vec
  `TauCeti.Comodule.exists_splitting_eq_conj_of_naturality` in cocycle form: a natural crossed
  homomorphism `D(G)(A) → A ⊗ V` is a coboundary of a single vector `y : V`.
* `tuIdeal_le_ker_of_eq_mul`, `exists_eq_mul_of_tuIdeal_le`, `eq_of_mul_eq_mul` (PROVED):
  points of `T · U_{≥n}` are the products `t * u`, uniquely once `tuMap` is surjective.
* Geometric inputs, stated precisely (SORRY):
  - `tuMap_surjective`: `T ⋉ U_{≥n} → B` is a closed immersion (`T ∩ U_{≥n} = 1`);
  - `exists_split_of_isMaximalTorus`: a maximal torus over `k = k̄` is split;
  - `exists_vecQuotient`: (F4) the quotient `U_{≥n} → V_n = (W_n^∨)_a` with its linear
    conjugation action, kernel `U_{≥n+1}`, and surjectivity on `k`-points (via (F3) / (F2)).
* `tuIdeal_step'` (PROVED from the above and (F3) `filtrationIdeal_spec`).
-/

suppress_compilation

open TensorProduct Magnetism TauCeti TauCeti.Cocharacter WithConv

namespace AlgMag.Reductive

universe u

/-! ## T1-vec in cocycle form -/

section Cocycle

open SemidirectProduct TauCeti.Comodule

variable {R : Type u} [CommRing R] {G : Type u} [CommGroup G]
  {V : Type u} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- **T1-vec, cocycle form.** A family of crossed homomorphisms
`c_A : D(G)(A) → A ⊗ V`, `c(gh) = c(g) + g • c(h)`, natural in the value algebra `A`, is the
coboundary `g ↦ y - g • y` of a single vector `y : V`. -/
theorem exists_eq_sub_of_natural_cocycle
    (c : ∀ (A : Type u) [CommRing A] [Algebra R A],
      WithConv (MonoidAlgebra R G →ₐ[R] A) → A ⊗[R] V)
    (hc : ∀ (A : Type u) [CommRing A] [Algebra R A] (g h : WithConv (MonoidAlgebra R G →ₐ[R] A)),
      c A (g * h) = c A g + endOfPoint V g.ofConv (c A h))
    (hnat : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (MonoidAlgebra R G →ₐ[R] A)),
      LinearMap.rTensor V φ.toLinearMap (c A g) = c B (AlgHom.mapValue φ g)) :
    ∃ y : V, ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : WithConv (MonoidAlgebra R G →ₐ[R] A)),
      c A g = (1 : A) ⊗ₜ[R] y - endOfPoint V g.ofConv ((1 : A) ⊗ₜ[R] y) := by
  have h1 : ∀ (A : Type u) [CommRing A] [Algebra R A], c A 1 = 0 := by
    intro A _ _
    have := hc A 1 1
    rw [mul_one, endOfPoint_convOne, LinearMap.id_apply] at this
    simpa using this
  let s : ∀ (A : Type u) [CommRing A] [Algebra R A],
      (toGroupExtension
        (pointsRepresentation (R := R) (H := MonoidAlgebra R G) (A := A) V).toMulAut).Splitting :=
    fun A _ _ ↦
      { toFun := fun g ↦ ⟨Multiplicative.ofAdd (c A g), g⟩
        map_one' := by
          refine SemidirectProduct.ext ?_ rfl
          apply Multiplicative.toAdd.injective
          simp [h1 A]
        map_mul' := fun g h ↦ by
          refine SemidirectProduct.ext ?_ rfl
          apply Multiplicative.toAdd.injective
          simp [mul_left, hc, Representation.toMulAut_apply]
        rightInverse_rightHom := fun _ ↦ rfl }
  have hs : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (MonoidAlgebra R G →ₐ[R] A)),
      pointSemidirectMap V φ (s A g) = s B (AlgHom.mapValue φ g) := by
    intro A B _ _ _ _ φ g
    refine SemidirectProduct.ext ?_ rfl
    apply Multiplicative.toAdd.injective
    rw [toAdd_pointSemidirectMap_left]
    exact hnat A B φ g
  obtain ⟨y, hy⟩ := exists_splitting_eq_conj_of_naturality s hs
  refine ⟨y, fun A _ _ g ↦ ?_⟩
  have := congrArg (fun x ↦ x.left.toAdd) (hy A g)
  rw [inl_mul_inr_mul_inv_inl] at this
  exact this

end Cocycle

/-! ## Plumbing for `exists_vecQuotient`: `A ⊗ W^* ≅ Hom(W, A)` -/

section DualPoints

variable {k : Type u} [Field k] {W : Type u} [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

/-- Points of the vector group `(W^*)_a`: `A ⊗ W^* ≅ Hom_k(W, A)` for finite-dimensional `W`. -/
noncomputable def dualPointsEquiv (A : Type u) [CommRing A] [Algebra k A] :
    A ⊗[k] Module.Dual k W ≃ₗ[k] (W →ₗ[k] A) :=
  (TensorProduct.comm k A (Module.Dual k W)).trans (dualTensorHomEquiv k W A)

lemma dualPointsEquiv_tmul (A : Type u) [CommRing A] [Algebra k A] (a : A)
    (f : Module.Dual k W) (w : W) : dualPointsEquiv A (a ⊗ₜ f) w = f w • a := by
  simp [dualPointsEquiv, dualTensorHom_apply]

/-- Naturality of `dualPointsEquiv` in the value algebra. -/
lemma dualPointsEquiv_rTensor {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (ψ : A →ₐ[k] B) (x : A ⊗[k] Module.Dual k W) :
    dualPointsEquiv B (LinearMap.rTensor _ ψ.toLinearMap x) =
      ψ.toLinearMap.comp (dualPointsEquiv A x) := by
  induction x using TensorProduct.induction_on with
  | zero => ext; simp
  | tmul a f => ext w; simp [dualPointsEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_add]

/-- Additivity is read off the functionals. -/
lemma dualPointsEquiv_symm_add (A : Type u) [CommRing A] [Algebra k A] (f g : W →ₗ[k] A) :
    (dualPointsEquiv A).symm (f + g) = (dualPointsEquiv A).symm f + (dualPointsEquiv A).symm g :=
  map_add _ f g

/-- Base points: the image of `1 ⊗ y` is `w ↦ y w`. -/
lemma dualPointsEquiv_one_tmul (A : Type u) [CommRing A] [Algebra k A] (y : Module.Dual k W)
    (w : W) : dualPointsEquiv A ((1 : A) ⊗ₜ y) w = algebraMap k A (y w) := by
  rw [dualPointsEquiv_tmul, Algebra.algebraMap_eq_smul_one]

end DualPoints

/-! ## Degree argument: Levi points commute with `λ`-conjugation -/

section LeviDegree

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- For `z ∈ Z_B(λ)(A)`, `λ`-conjugation of `z x z⁻¹` is `z · (λ-conjugate of x) · z⁻¹`. -/
theorem conjugate_levi_conj {A : Type u} [CommRing A] [Algebra k A]
    {z : WithConv (H →ₐ[k] A)} (hz : z ∈ levi A l) (x : WithConv (H →ₐ[k] A)) :
    conjugate A l (z * x * z⁻¹) = constPoint A z * conjugate A l x * (constPoint A z)⁻¹ := by
  rw [map_mul, map_mul, map_inv, (mem_levi_iff).1 hz]

/-- Degree-`n` coordinates are read off as the `T^n`-coefficient of the `λ`-conjugate. -/
theorem apply_eq_coeff_conjugate {A : Type u} [CommRing A] [Algebra k A]
    (y : WithConv (H →ₐ[k] A)) {n : ℤ} {w : H} (hw : w ∈ lineGrading l n) :
    y.ofConv w = ((conjugate A l y).ofConv w).coeff n := by
  rw [coeff_conjugate, coeff_of_mem_lineGrading hw, if_pos rfl]

/-- **Degree argument.** For a Levi point `z` and `w` of `λ`-degree `n`, the coordinate
`w(z x z⁻¹)` is the `T^n`-coefficient of `w(z · λ(T) x λ(T)⁻¹ · z⁻¹)`: conjugation by `Z_B(λ)`
preserves the `λ`-grading on points. -/
theorem apply_levi_conj_eq_coeff {A : Type u} [CommRing A] [Algebra k A]
    {z : WithConv (H →ₐ[k] A)} (hz : z ∈ levi A l) (x : WithConv (H →ₐ[k] A)) {n : ℤ} {w : H}
    (hw : w ∈ lineGrading l n) :
    (z * x * z⁻¹).ofConv w =
      ((constPoint A z * conjugate A l x * (constPoint A z)⁻¹).ofConv w).coeff n := by
  rw [apply_eq_coeff_conjugate l _ hw, conjugate_levi_conj l hz]

end LeviDegree

/-! ## Points of `T · U_{≥n}` -/

section Points

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

/-- Points of a Hopf ideal are closed under products. -/
lemma le_ker_mul {I : HopfIdeal k H} {A : Type u} [CommRing A] [Algebra k A]
    {x y : WithConv (H →ₐ[k] A)} (hx : I.toIdeal ≤ RingHom.ker x.ofConv)
    (hy : I.toIdeal ≤ RingHom.ker y.ofConv) : I.toIdeal ≤ RingHom.ker (x * y).ofConv := by
  have hx' : (x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2 fun h hh ↦ hx hh
  have hy' : (y : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2 fun h hh ↦ hy hh
  intro h hh
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 (mul_mem hx' hy') h hh

/-- Points of a Hopf ideal are closed under inverses. -/
lemma le_ker_inv {I : HopfIdeal k H} {A : Type u} [CommRing A] [Algebra k A]
    {x : WithConv (H →ₐ[k] A)} (hx : I.toIdeal ≤ RingHom.ker x.ofConv) :
    I.toIdeal ≤ RingHom.ker x⁻¹.ofConv := by
  have hx' : (x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2 fun h hh ↦ hx hh
  intro h hh
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 (inv_mem hx') h hh

/-- Points of a normal Hopf ideal are stable under conjugation by all points. -/
lemma le_ker_conj {I : HopfIdeal k H} (hI : I.IsNormal) {A : Type u} [CommRing A] [Algebra k A]
    {x : WithConv (H →ₐ[k] A)} (hx : I.toIdeal ≤ RingHom.ker x.ofConv) (b : WithConv (H →ₐ[k] A)) :
    I.toIdeal ≤ RingHom.ker (b * x * b⁻¹).ofConv := by
  have hx' : (x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I (CommAlgCat.of k A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2 fun h hh ↦ hx hh
  have hN := (CommHopfAlgCat.quotientPointsSubgroup_normal (_root_.CommHopfAlgCat.of k H) I hI
    (CommAlgCat.of k A)).conj_mem
  have hb := hN (x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A)) hx'
    (b : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k A))
  intro h hh
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 hb h hh

/-- The unit point lies in every Hopf ideal's points. -/
lemma le_ker_one {I : HopfIdeal k H} {A : Type u} [CommRing A] [Algebra k A] :
    I.toIdeal ≤ RingHom.ker (1 : WithConv (H →ₐ[k] A)).ofConv := by
  intro h hh
  exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1
    (one_mem (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) I
      (CommAlgCat.of k A))) h hh

lemma le_ker_mapValue {I : Ideal H} {A B : Type u} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] (ψ : A →ₐ[k] B) {x : WithConv (H →ₐ[k] A)} (hx : I ≤ RingHom.ker x.ofConv) :
    I ≤ RingHom.ker (AlgHom.mapValue ψ x).ofConv := by
  intro h hh
  simp [RingHom.mem_ker.mp (hx hh)]

end Points

section TU

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H] [DecidableEq H]
  [Algebra.FiniteType k H] [Algebra.Smooth k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- The coordinate map of the multiplication `T × U_{≥n} → B`. -/
noncomputable def tuMap (T : HopfIdeal k H) (n : ℕ) :
    H →ₐ[k] (H ⧸ T.toIdeal) ⊗[k] (H ⧸ filtrationIdeal l n) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal)
    (Ideal.Quotient.mkₐ k (filtrationIdeal l n))).comp (Bialgebra.comulAlgHom k H)

lemma tuIdeal_eq_ker (T : HopfIdeal k H) (n : ℕ) : tuIdeal l T n = RingHom.ker (tuMap l T n) :=
  rfl

variable {l} {T : HopfIdeal k H} {n : ℕ}

/-- The algebra map out of `H/T ⊗ H/J_n` attached to a pair of points `(t, u)`. -/
noncomputable def pairHom {A : Type u} [CommRing A] [Algebra k A] (t u : WithConv (H →ₐ[k] A))
    (ht : T.toIdeal ≤ RingHom.ker t.ofConv) (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv) :
    (H ⧸ T.toIdeal) ⊗[k] (H ⧸ filtrationIdeal l n) →ₐ[k] A :=
  Algebra.TensorProduct.lift
    (Ideal.Quotient.liftₐ T.toIdeal t.ofConv fun a ha ↦ RingHom.mem_ker.mp (ht ha))
    (Ideal.Quotient.liftₐ (filtrationIdeal l n) u.ofConv fun a ha ↦ RingHom.mem_ker.mp (hu ha))
    fun _ _ ↦ Commute.all _ _

lemma pairHom_comp_tuMap {A : Type u} [CommRing A] [Algebra k A] (t u : WithConv (H →ₐ[k] A))
    (ht : T.toIdeal ≤ RingHom.ker t.ofConv) (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv) :
    (pairHom t u ht hu).comp (tuMap l T n) = (t * u).ofConv := by
  have h : (pairHom t u ht hu).comp (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k T.toIdeal)
      (Ideal.Quotient.mkₐ k (filtrationIdeal l n))) =
      (Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map t.ofConv u.ofConv) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [pairHom]
    rfl
  rw [tuMap, ← AlgHom.comp_assoc, h, AlgHom.convMul_def, ofConv_toConv, AlgHom.comp_assoc]

lemma pairHom_tmul_one {A : Type u} [CommRing A] [Algebra k A] (t u : WithConv (H →ₐ[k] A))
    (ht : T.toIdeal ≤ RingHom.ker t.ofConv) (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv)
    (a : H) : pairHom t u ht hu (Ideal.Quotient.mk _ a ⊗ₜ 1) = t.ofConv a := by
  simp [pairHom]
  rfl

lemma pairHom_one_tmul {A : Type u} [CommRing A] [Algebra k A] (t u : WithConv (H →ₐ[k] A))
    (ht : T.toIdeal ≤ RingHom.ker t.ofConv) (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv)
    (a : H) : pairHom t u ht hu (1 ⊗ₜ Ideal.Quotient.mk _ a) = u.ofConv a := by
  simp [pairHom]
  rfl

/-- A product `t * u` with `t ∈ T`, `u ∈ U_{≥n}` lies in `T · U_{≥n}`. -/
theorem tuIdeal_le_ker_of_eq_mul {A : Type u} [CommRing A] [Algebra k A]
    {x t u : WithConv (H →ₐ[k] A)} (ht : T.toIdeal ≤ RingHom.ker t.ofConv)
    (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv) (hx : x = t * u) :
    tuIdeal l T n ≤ RingHom.ker x.ofConv := by
  intro z hz
  rw [tuIdeal_eq_ker, RingHom.mem_ker] at hz
  rw [RingHom.mem_ker, hx, ← pairHom_comp_tuMap t u ht hu, AlgHom.comp_apply, hz, map_zero]

/-- Uniqueness of the factorization `x = t * u`, once `tuMap` is surjective. -/
theorem eq_of_mul_eq_mul (hsurj : Function.Surjective (tuMap l T n)) {A : Type u} [CommRing A]
    [Algebra k A] {t u t' u' : WithConv (H →ₐ[k] A)} (ht : T.toIdeal ≤ RingHom.ker t.ofConv)
    (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv) (ht' : T.toIdeal ≤ RingHom.ker t'.ofConv)
    (hu' : filtrationIdeal l n ≤ RingHom.ker u'.ofConv) (h : t * u = t' * u') :
    t = t' ∧ u = u' := by
  have hψ : pairHom t u ht hu = pairHom t' u' ht' hu' := by
    refine AlgHom.ext fun z ↦ ?_
    obtain ⟨w, rfl⟩ := hsurj z
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, pairHom_comp_tuMap, pairHom_comp_tuMap, h]
  constructor
  · apply ofConv_injective
    ext a
    rw [← pairHom_tmul_one t u ht hu, ← pairHom_tmul_one t' u' ht' hu', hψ]
  · apply ofConv_injective
    ext a
    rw [← pairHom_one_tmul t u ht hu, ← pairHom_one_tmul t' u' ht' hu', hψ]

/-- Existence of the factorization `x = t * u` for a point `x` of `T · U_{≥n}`, once `tuMap` is
surjective. -/
theorem exists_eq_mul_of_tuIdeal_le (hsurj : Function.Surjective (tuMap l T n)) {A : Type u}
    [CommRing A] [Algebra k A] {x : WithConv (H →ₐ[k] A)}
    (hx : tuIdeal l T n ≤ RingHom.ker x.ofConv) :
    ∃ t u : WithConv (H →ₐ[k] A), T.toIdeal ≤ RingHom.ker t.ofConv ∧
      filtrationIdeal l n ≤ RingHom.ker u.ofConv ∧ x = t * u := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let ψ : (H ⧸ T.toIdeal) ⊗[k] (H ⧸ filtrationIdeal l n) →ₐ[k] A :=
    (Ideal.Quotient.liftₐ (RingHom.ker (tuMap l T n)) x.ofConv
      fun a ha ↦ RingHom.mem_ker.mp (hx ha)).comp e.symm.toAlgHom
  have hψ : ∀ z, ψ (tuMap l T n z) = x.ofConv z := by
    intro z
    have : e.symm (tuMap l T n z) = Ideal.Quotient.mk _ z := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hsurj z).symm
    simp [ψ, this]
    rfl
  let t : WithConv (H →ₐ[k] A) := toConv
    (ψ.comp (Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ k T.toIdeal)))
  let u : WithConv (H →ₐ[k] A) := toConv
    (ψ.comp (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ k (filtrationIdeal l n))))
  have ht : T.toIdeal ≤ RingHom.ker t.ofConv := by
    intro a ha
    simp [t, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  have hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv := by
    intro a ha
    simp [u, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  refine ⟨t, u, ht, hu, ?_⟩
  have hpair : pairHom t u ht hu = ψ := by
    apply Algebra.TensorProduct.ext'
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [show pairHom t u ht hu (Ideal.Quotient.mk _ a ⊗ₜ Ideal.Quotient.mk _ b) =
      ψ (Ideal.Quotient.mk _ a ⊗ₜ 1) * ψ (1 ⊗ₜ Ideal.Quotient.mk _ b) from rfl, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  apply ofConv_injective
  rw [← pairHom_comp_tuMap t u ht hu, hpair]
  ext z
  exact (hψ z).symm

/-! ## Geometric inputs (precisely stated, SORRY) -/

/-- **Tori over `k = k̄` are split.** A maximal torus `S` is cut out by a surjective bialgebra map
`H → k[G]` onto the group algebra of a commutative group (its character group).
(From `TauCeti.torusCommHopfAlgProperty.split` and `DiagonalizableGroup.coordinateRing`.) -/
theorem exists_split_of_isMaximalTorus [IsAlgClosed k] (S : HopfIdeal k H)
    (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S) :
    ∃ (G : Type u) (_ : CommGroup G) (φ : H →ₐc[k] MonoidAlgebra k G),
      Function.Surjective φ ∧ RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k G) = S.toIdeal := by
  obtain ⟨r, ⟨i⟩⟩ := (splitTorusCommHopfAlgProperty_iff k _).1
    (torusCommHopfAlgProperty.split k _ hS.1)
  let G0 := SplitTorus.characterGroup (ULift.{u} (Fin r))
  let m : H →ₐc[k] (H ⧸ S.toIdeal) :=
    (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) S).hom
  let ψ : (H ⧸ S.toIdeal) →ₐc[k] MonoidAlgebra k G0 := i.inv.hom.hom
  let ψ' : MonoidAlgebra k G0 →ₐc[k] (H ⧸ S.toIdeal) := i.hom.hom.hom
  have h1 : ∀ x, ψ' (ψ x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.inv_hom_id
  have h2 : ∀ x, ψ (ψ' x) = x := fun x ↦ by
    exact congrArg (fun f ↦ f.hom.hom x) i.hom_inv_id
  have hm : ∀ x, m x = Ideal.Quotient.mk _ x := fun _ ↦ rfl
  refine ⟨G0, inferInstance, ψ.comp m, fun y ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ψ' y)
    exact ⟨x, by simp [hm, hx, h2]⟩
  · ext x
    rw [RingHom.mem_ker]
    change ψ (m x) = 0 ↔ _
    constructor
    · intro hx
      have : m x = 0 := by rw [← h1 (m x), hx, map_zero]
      rw [hm] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro hx
      rw [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Descend an algebra map along a surjective bialgebra map. -/
noncomputable def descAlgHom {K L : Type u} [CommRing K] [Bialgebra k K] [CommRing L]
    [Bialgebra k L] (π : H →ₐc[k] K) (hπ : Function.Surjective π) (f : H →ₐc[k] L)
    (hf : RingHom.ker (π : H →ₐ[k] K) ≤ RingHom.ker (f : H →ₐ[k] L)) : K →ₐ[k] L :=
  (Ideal.Quotient.liftₐ _ (f : H →ₐ[k] L) fun a ha ↦ RingHom.mem_ker.mp (hf ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (π : H →ₐ[k] K)) hπ).symm.toAlgHom

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma descAlgHom_apply {K L : Type u} [CommRing K] [Bialgebra k K] [CommRing L]
    [Bialgebra k L] (π : H →ₐc[k] K) (hπ : Function.Surjective π) (f : H →ₐc[k] L)
    (hf : RingHom.ker (π : H →ₐ[k] K) ≤ RingHom.ker (f : H →ₐ[k] L)) (h : H) :
    descAlgHom π hπ f hf (π h) = f h := by
  have : (Ideal.quotientKerAlgEquivOfSurjective (f := (π : H →ₐ[k] K)) hπ).symm (π h) =
      Ideal.Quotient.mk _ h := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk (f := (π : H →ₐ[k] K)) hπ h).symm
  change Ideal.Quotient.liftₐ (RingHom.ker (π : H →ₐ[k] K)) (f : H →ₐ[k] L)
    (fun a ha ↦ RingHom.mem_ker.mp (hf ha))
    ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : H →ₐ[k] K)) hπ).symm (π h)) = f h
  rw [this]
  rfl

/-- Descend a bialgebra map along a surjective bialgebra map. -/
noncomputable def descBialgHom {K L : Type u} [CommRing K] [Bialgebra k K] [CommRing L]
    [Bialgebra k L] (π : H →ₐc[k] K) (hπ : Function.Surjective π) (f : H →ₐc[k] L)
    (hf : RingHom.ker (π : H →ₐ[k] K) ≤ RingHom.ker (f : H →ₐ[k] L)) : K →ₐc[k] L :=
  BialgHom.ofAlgHom (descAlgHom π hπ f hf)
    (by
      apply AlgHom.ext; intro x
      obtain ⟨h, rfl⟩ := hπ x
      simp only [AlgHom.comp_apply, descAlgHom_apply, Bialgebra.counitAlgHom_apply,
        CoalgHomClass.counit_comp_apply])
    (by
      apply AlgHom.ext; intro x
      obtain ⟨h, rfl⟩ := hπ x
      simp only [AlgHom.comp_apply, descAlgHom_apply, Bialgebra.comulAlgHom_apply]
      rw [← CoalgHomClass.map_comp_comul_apply π h, ← CoalgHomClass.map_comp_comul_apply f h]
      induction Coalgebra.comul (R := k) h using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [descAlgHom_apply]
      | add a b ha hb => simp only [map_add, ha, hb])

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma descBialgHom_comp {K L : Type u} [CommRing K] [Bialgebra k K] [CommRing L]
    [Bialgebra k L] (π : H →ₐc[k] K) (hπ : Function.Surjective π) (f : H →ₐc[k] L)
    (hf : RingHom.ker (π : H →ₐ[k] K) ≤ RingHom.ker (f : H →ₐ[k] L)) :
    (descBialgHom π hπ f hf).comp π = f := by
  ext h
  exact descAlgHom_apply π hπ f hf h

/-- **A maximal torus through which `λ` factors lies in the Levi `Z_B(λ)`.** -/
theorem levi_le_of_le_ker [IsAlgClosed k] {T : HopfIdeal k H}
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) T)
    (hlT : T.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k)) :
    (leviDefiningHopfIdeal l).toIdeal ≤ T.toIdeal := by
  obtain ⟨X, _, π, hπ, hker⟩ := exists_split_of_isMaximalTorus T hT
  have hf : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) ≤
      RingHom.ker (l : H →ₐ[k] LaurentPolynomial k) := hker ▸ hlT
  have hl := descBialgHom_comp π hπ l hf
  have key := BialgHom.centralizerHopfIdeal_comp_le_kerOfSurjective π hπ
    ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp (descBialgHom π hπ l hf))
  rw [BialgHom.comp_assoc, hl, ← BialgHom.leviDefiningHopfIdeal_eq_centralizerHopfIdeal] at key
  intro x hx
  have hx' := key hx
  rw [HopfIdeal.mem_kerOfSurjective] at hx'
  rw [← hker]
  exact hx'

/-- **`T ∩ U_{≥n} = 1` and `T ⋉ U_{≥n} → B` is a closed immersion.** Under DynHyp,
`B = Z_B(λ) ⋉ U_B(λ)` with `T ⊆ Z_B(λ)`, and `U_{≥n} ⊆ U_B(λ)` is closed, so the multiplication
`T × U_{≥n} → B` is a closed immersion: its coordinate map `tuMap` is surjective. -/
theorem tuMap_surjective [IsAlgClosed k] (h : DynHyp l T) (hn : 0 < n) :
    Function.Surjective (tuMap l T n) := by
  set IU := BialgHom.unipotentDefiningHopfIdeal l
  set IZ := leviDefiningHopfIdeal l
  let qU := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) IU).hom
  let qZ := (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) IZ).hom
  let SH : H →ₗ[k] H := HopfAlgebraStruct.antipode k
  let SU : (H ⧸ IU.toIdeal) →ₗ[k] (H ⧸ IU.toIdeal) := HopfAlgebraStruct.antipode k
  let SZ : (H ⧸ IZ.toIdeal) →ₗ[k] (H ⧸ IZ.toIdeal) := HopfAlgebraStruct.antipode k
  -- `F = (qU ⊗ qZ) ∘ Δ` is surjective (Levi decomposition `P = U ⋊ Z`)
  have hF : ∀ y : (H ⧸ IU.toIdeal) ⊗[k] (H ⧸ IZ.toIdeal),
      ∃ x, TensorProduct.map (qU : H →ₗ[k] H ⧸ IU.toIdeal) (qZ : H →ₗ[k] H ⧸ IZ.toIdeal)
        (Coalgebra.comul (R := k) x) = y := by
    intro y
    obtain ⟨z, hz⟩ := l.parabolicCoordinateAlgEquiv.surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, by rw [← hz, BialgHom.parabolicCoordinateAlgEquiv_mk]; rfl⟩
  -- the antipode exchanges the two orders
  have hswap : ∀ t : H ⊗[k] H,
      TensorProduct.map (qZ : H →ₗ[k] H ⧸ IZ.toIdeal) (qU : H →ₗ[k] H ⧸ IU.toIdeal)
        (TensorProduct.map SH SH (TensorProduct.comm k H H t)) =
      TensorProduct.map SZ SU (TensorProduct.comm k _ _
        (TensorProduct.map (qU : H →ₗ[k] H ⧸ IU.toIdeal) (qZ : H →ₗ[k] H ⧸ IZ.toIdeal) t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, SH, SU, SZ]
      rw [BialgHom.coe_toLinearMap, BialgHom.coe_toLinearMap, BialgHomClass.map_antipode,
        BialgHomClass.map_antipode]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinv : ∀ w : (H ⧸ IZ.toIdeal) ⊗[k] (H ⧸ IU.toIdeal),
      TensorProduct.map SZ SU (TensorProduct.map SZ SU w) = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [SU, SZ, TauCeti.HopfAlgebra.antipode_antipode]
    | add a b ha hb => simp only [map_add, ha, hb]
  -- `G = (qZ ⊗ qU) ∘ Δ` is surjective
  have hG : ∀ y : (H ⧸ IZ.toIdeal) ⊗[k] (H ⧸ IU.toIdeal),
      ∃ x, TensorProduct.map (qZ : H →ₗ[k] H ⧸ IZ.toIdeal) (qU : H →ₗ[k] H ⧸ IU.toIdeal)
        (Coalgebra.comul (R := k) x) = y := by
    intro y
    obtain ⟨x0, hx0⟩ := hF (TensorProduct.comm k _ _ (TensorProduct.map SZ SU y))
    refine ⟨SH x0, ?_⟩
    rw [show Coalgebra.comul (R := k) (SH x0) =
        TensorProduct.map SH SH (TensorProduct.comm k H H (Coalgebra.comul (R := k) x0)) from
      TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply x0, hswap, hx0]
    simp [hinv]
  -- factor to `H/T ⊗ H/J_n`
  have hZT : IZ.toIdeal ≤ T.toIdeal := levi_le_of_le_ker h.hT h.hlT
  have hUJ : IU.toIdeal ≤ filtrationIdeal l n := unip_le_filtrationIdeal l n
  let pT := Ideal.Quotient.factorₐ k hZT
  let pJ := Ideal.Quotient.factorₐ k hUJ
  have hp : Function.Surjective (Algebra.TensorProduct.map pT pJ) :=
    Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.factor_surjective hZT)
      (Ideal.Quotient.factor_surjective hUJ)
  intro y
  obtain ⟨y', rfl⟩ := hp y
  obtain ⟨x, hx⟩ := hG y'
  refine ⟨x, ?_⟩
  rw [← hx]
  change Algebra.TensorProduct.map _ _ (Coalgebra.comul (R := k) x) = _
  induction Coalgebra.comul (R := k) x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-! ## The character map `X(T) → X(S)` induced by `S → T`, `s = t · u ↦ t` -/

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma lmul'_map_includeLeft_includeRight {G : Type u} [CommGroup G]
    (z : MonoidAlgebra k G ⊗[k] MonoidAlgebra k G) :
    Algebra.TensorProduct.lmul' k (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := MonoidAlgebra k G)
        (B := MonoidAlgebra k G))
      (Algebra.TensorProduct.includeRight (R := k) (A := MonoidAlgebra k G)
        (B := MonoidAlgebra k G)) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The character map.** Let `T = ker π` (split, `π : H → k[X]`) and `S = ker φ ⊆ T · U_{≥n}`
(`φ : H → k[G]`). The projection `S → T`, `s = t · u ↦ t`, is given on characters by a group
homomorphism `c : X → G`: whenever `s = g ∘ φ` factors as `t · u` with `u ∈ U_{≥n}`, the
`T`-coordinate `t` evaluates the character `χ` as `g` evaluates `c χ`. -/
theorem exists_charMap [IsAlgClosed k] (h : DynHyp l T) (hn : 0 < n)
    {X : Type u} [CommGroup X] (π : H →ₐc[k] MonoidAlgebra k X) (hπs : Function.Surjective π)
    (hπk : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) = T.toIdeal)
    {G : Type u} [CommGroup G] (φ : H →ₐc[k] MonoidAlgebra k G)
    (hle : tuIdeal l T n ≤ RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k G)) :
    ∃ c : X →* G, ∀ (A : Type u) [CommRing A] [Algebra k A]
      (g : WithConv (MonoidAlgebra k G →ₐ[k] A)) (t : WithConv (H →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker t.ofConv →
      filtrationIdeal l n ≤
        RingHom.ker (t⁻¹ * toConv (g.ofConv.comp (φ : H →ₐ[k] MonoidAlgebra k G))).ofConv →
      ∀ (χ : X) (x : H), π x = MonoidAlgebra.single χ 1 →
        t.ofConv x = g.ofConv (MonoidAlgebra.single (c χ) 1) := by
  classical
  have hsurj := tuMap_surjective h hn
  obtain ⟨Jn, hJn, hJnN, -⟩ := filtrationIdeal_spec l h.hP n
  let φA : H →ₐ[k] MonoidAlgebra k G := φ
  obtain ⟨t0, u0, ht0, hu0, h0⟩ :=
    exists_eq_mul_of_tuIdeal_le hsurj (x := toConv φA) (by simpa using hle)
  -- the `T`-coordinate of `g ∘ φ` is `g ∘ t0`
  have key : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (g : WithConv (MonoidAlgebra k G →ₐ[k] A)) (t : WithConv (H →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker t.ofConv →
      filtrationIdeal l n ≤ RingHom.ker (t⁻¹ * toConv (g.ofConv.comp φA)).ofConv →
      t = AlgHom.mapValue g.ofConv t0 := by
    intro A _ _ g t ht hu
    have e1 : toConv (g.ofConv.comp φA) =
        AlgHom.mapValue g.ofConv t0 * AlgHom.mapValue g.ofConv u0 := by
      rw [← map_mul, ← h0]; rfl
    have e2 : toConv (g.ofConv.comp φA) = t * (t⁻¹ * toConv (g.ofConv.comp φA)) := by group
    exact (eq_of_mul_eq_mul hsurj ht hu (le_ker_mapValue _ ht0) (le_ker_mapValue _ hu0)
      (e2.symm.trans e1)).1
  -- descend `t0` along `π`
  have hker : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) ≤ RingHom.ker t0.ofConv :=
    hπk ▸ ht0
  let eπ := Ideal.quotientKerAlgEquivOfSurjective (f := (π : H →ₐ[k] MonoidAlgebra k X)) hπs
  let F : MonoidAlgebra k X →ₐ[k] MonoidAlgebra k G :=
    (Ideal.Quotient.liftₐ _ t0.ofConv fun a ha ↦ RingHom.mem_ker.mp (hker ha)).comp
      eπ.symm.toAlgHom
  have hF : ∀ x, F (π x) = t0.ofConv x := by
    intro x
    have : eπ.symm (π x) = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk
        (f := (π : H →ₐ[k] MonoidAlgebra k X)) hπs x).symm
    change Ideal.Quotient.liftₐ (RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X)) t0.ofConv
      (fun a ha ↦ RingHom.mem_ker.mp (hker ha)) (eπ.symm (π x)) = _
    rw [this]
    rfl
  have ht0F : t0.ofConv = F.comp (π : H →ₐ[k] MonoidAlgebra k X) := by
    exact AlgHom.ext fun x ↦ (hF x).symm
  -- group-likeness of `F (single χ 1)`
  have hgl : ∀ χ : X, IsGroupLikeElem k (F (MonoidAlgebra.single χ 1)) := by
    intro χ
    obtain ⟨x, hx⟩ := hπs (MonoidAlgebra.single χ 1)
    constructor
    · -- counit, via the unit point
      have hφ1 : toConv ((1 : WithConv (MonoidAlgebra k G →ₐ[k] k)).ofConv.comp φA) =
          (1 : WithConv (H →ₐ[k] k)) := by
        apply ofConv_injective
        ext y
        simp [φA, AlgHom.convOne_def, CoalgHomClass.counit_comp_apply]
      have h1 := key k 1 1 le_ker_one (by rw [hφ1, inv_one, one_mul]; exact hJn ▸ le_ker_one)
      have h1x := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv x) h1
      simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at h1x
      rw [← hF, hx, AlgHom.convOne_apply, AlgHom.convOne_apply,
        ← CoalgHomClass.counit_comp_apply π x, hx] at h1x
      simpa using h1x.symm
    · -- comultiplication, via the universal pair of points
      let g1 : WithConv (MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⊗[k] MonoidAlgebra k G)) :=
        toConv Algebra.TensorProduct.includeLeft
      let g2 : WithConv (MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⊗[k] MonoidAlgebra k G)) :=
        toConv Algebra.TensorProduct.includeRight
      let t1 := AlgHom.mapValue g1.ofConv t0
      let t2 := AlgHom.mapValue g2.ofConv t0
      have hs : ∀ g : WithConv (MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⊗[k] MonoidAlgebra k G)),
          toConv (g.ofConv.comp φA) = AlgHom.mapValue g.ofConv t0 * AlgHom.mapValue g.ofConv u0 :=
        fun g ↦ by rw [← map_mul, ← h0]; rfl
      have hmul : toConv ((g1 * g2).ofConv.comp φA) =
          toConv (g1.ofConv.comp φA) * toConv (g2.ofConv.comp φA) :=
        congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib g1 g2 φ)
      have hT12 : T.toIdeal ≤ RingHom.ker (t1 * t2).ofConv :=
        le_ker_mul (le_ker_mapValue _ ht0) (le_ker_mapValue _ ht0)
      have hU12 : filtrationIdeal l n ≤
          RingHom.ker ((t1 * t2)⁻¹ * toConv ((g1 * g2).ofConv.comp φA)).ofConv := by
        rw [hmul, hs g1, hs g2]
        have e : (t1 * t2)⁻¹ * (t1 * AlgHom.mapValue g1.ofConv u0 *
            (t2 * AlgHom.mapValue g2.ofConv u0)) =
            t2⁻¹ * AlgHom.mapValue g1.ofConv u0 * t2⁻¹⁻¹ * AlgHom.mapValue g2.ofConv u0 := by
          have hg : ∀ {M : Type u} [Group M] (a b x y : M),
              (a * b)⁻¹ * (a * x * (b * y)) = b⁻¹ * x * b⁻¹⁻¹ * y := by
            intros; group
          exact hg (M := WithConv (H →ₐ[k] (MonoidAlgebra k G ⊗[k] MonoidAlgebra k G))) _ _ _ _
        rw [e, ← hJn]
        exact le_ker_mul (le_ker_conj hJnN (hJn ▸ le_ker_mapValue _ hu0) _)
          (hJn ▸ le_ker_mapValue _ hu0)
      have h12 := key _ (g1 * g2) (t1 * t2) hT12 hU12
      have h12x := congrArg (fun p : WithConv (H →ₐ[k] (MonoidAlgebra k G ⊗[k] MonoidAlgebra k G)) ↦
        p.ofConv x) h12
      simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at h12x
      rw [← hF, hx] at h12x
      have hL : (t1 * t2).ofConv x =
          F (MonoidAlgebra.single χ 1) ⊗ₜ F (MonoidAlgebra.single χ 1) := by
        have e : (t1 * t2).ofConv =
            (toConv (g1.ofConv.comp F) * toConv (g2.ofConv.comp F)).ofConv.comp
              (π : H →ₐ[k] MonoidAlgebra k X) := by
          rw [AlgHom.convMul_comp_bialgHom_distrib]
          simp only [t1, t2, AlgHom.mapValue_apply, ht0F, AlgHom.comp_assoc]
        rw [e, AlgHom.comp_apply,
          show (π : H →ₐ[k] MonoidAlgebra k X) x = MonoidAlgebra.single χ 1 from hx,
          AlgHom.convMul_apply]
        simp [MonoidAlgebra.comul_single, g1, g2, Algebra.TensorProduct.tmul_mul_tmul]
      have hR : (g1 * g2).ofConv (F (MonoidAlgebra.single χ 1)) =
          Coalgebra.comul (R := k) (F (MonoidAlgebra.single χ 1)) := by
        rw [AlgHom.convMul_def, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
          Bialgebra.comulAlgHom_apply]
        exact lmul'_map_includeLeft_includeRight _
      rw [← hR, ← h12x, hL]
  choose c hc using fun χ ↦ ((TauCeti.MonoidAlgebra.isGroupLikeElem_iff_eq_single k _).1 (hgl χ)).exists
  have hcu : ∀ χ γ, F (MonoidAlgebra.single χ 1) = MonoidAlgebra.single γ 1 → c χ = γ :=
    fun χ γ hγ ↦ ((TauCeti.MonoidAlgebra.isGroupLikeElem_iff_eq_single k _).1 (hgl χ)).unique (hc χ) hγ
  let cM : X →* G :=
    { toFun := c
      map_one' := hcu 1 1 (by rw [← MonoidAlgebra.one_def, map_one, MonoidAlgebra.one_def])
      map_mul' := fun χ ψ ↦ hcu _ _ (by
        rw [← mul_one (1 : k), ← MonoidAlgebra.single_mul_single, map_mul, hc, hc,
          MonoidAlgebra.single_mul_single, mul_one]) }
  refine ⟨cM, fun A _ _ g t ht hu χ x hx ↦ ?_⟩
  rw [key A g t ht hu, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply, ← hF, hx]
  exact congrArg g.ofConv (hc χ)

/-- **`λ` factors through the split torus `T`**: `l = π.cocharacter ψ`, so the `T`-grading refines
the `λ`-grading along a homomorphism `χ : X → ℤ`. -/
theorem exists_weight_of_le_ker {T : HopfIdeal k H} {X : Type u} [CommGroup X]
    (π : H →ₐc[k] MonoidAlgebra k X) (hπs : Function.Surjective π)
    (hπk : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) = T.toIdeal)
    (hlT : T.toIdeal ≤ RingHom.ker (l : H →ₐ[k] LaurentPolynomial k)) :
    ∃ χ : Additive X →+ ℤ, ∀ μ, torusGrading π μ ≤ lineGrading l (χ μ) := by
  have hf : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) ≤
      RingHom.ker (l : H →ₐ[k] LaurentPolynomial k) := hπk ▸ hlT
  set lb := descBialgHom π hπs l hf
  let F : MonoidAlgebra k X →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) :=
    (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp lb
  let ψ : X →* Multiplicative ℤ := TauCeti.MonoidAlgebra.mapDomainBialgHomPreimage k F
  have hl : π.cocharacter ψ = l := by
    rw [BialgHom.cocharacter, TauCeti.MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHomPreimage]
    ext h
    have e := congrArg (fun f : H →ₐc[k] LaurentPolynomial k ↦ f h) (descBialgHom_comp π hπs l hf)
    simp only [BialgHom.comp_apply] at e ⊢
    simp [F, lb, e]
  let χ : Additive X →+ ℤ :=
    { toFun := fun μ ↦ (ψ (Additive.toMul μ)).toAdd
      map_zero' := by simp
      map_add' := fun a b ↦ by simp }
  refine ⟨χ, fun μ ↦ ?_⟩
  have := torusGrading_le_lineGrading (π := π) (ψ := ψ) μ
  rwa [hl] at this

/-! ## (F4) the vector quotient, diagonal form -/

/-- **(F4) on points.** Degree-`n` coordinates are additive on `U_{≥n}`. -/
lemma apply_mul_of_mem_lineGrading (hP : parabolicDefiningHopfIdeal l = ⊥) (hn : 0 < n)
    {w : H} (hw : w ∈ lineGrading l (n : ℤ)) {A : Type u} [CommRing A] [Algebra k A]
    {u u' : WithConv (H →ₐ[k] A)} (hu : filtrationIdeal l n ≤ RingHom.ker u.ofConv)
    (hu' : filtrationIdeal l n ≤ RingHom.ker u'.ofConv) :
    (u * u').ofConv w = u.ofConv w + u'.ofConv w := by
  have hmem := comul_sub_mem_of_mem_lineGrading l hP hn hw
  let ψ : H ⊗[k] H →ₐ[k] A :=
    (Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map u.ofConv u'.ofConv)
  have hle : Ideal.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := H) (B := H))
      (filtrationIdeal l n) ⊔
      Ideal.map (Algebra.TensorProduct.includeRight (R := k) (A := H)) (filtrationIdeal l n) ≤
      RingHom.ker ψ := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_)
      (Ideal.map_le_iff_le_comap.2 fun j hj ↦ ?_)
    · rw [Ideal.mem_comap, RingHom.mem_ker]
      simp [ψ, RingHom.mem_ker.mp (hu hj)]
    · rw [Ideal.mem_comap, RingHom.mem_ker]
      simp [ψ, RingHom.mem_ker.mp (hu' hj)]
  have h1 := hle hmem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  have h2 : ψ (w ⊗ₜ (1 : H) + (1 : H) ⊗ₜ w) = u.ofConv w + u'.ofConv w := by simp [ψ]
  rw [AlgHom.convMul_def, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
    Bialgebra.comulAlgHom_apply]
  exact h1.trans h2

omit [DecidableEq H] [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- **Torus weights on points.** For `h` of `T`-weight `μ` and `t = τ ∘ π`,
`h(t y t⁻¹) = τ(μ) · h(y)`. -/
lemma apply_torus_conj {X : Type u} [CommGroup X] (π : H →ₐc[k] MonoidAlgebra k X)
    {μ : Additive X} {h : H} (hh : h ∈ torusGrading π μ) {A : Type u} [CommRing A]
    [Algebra k A] (τ : MonoidAlgebra k X →ₐ[k] A) (y : WithConv (H →ₐ[k] A)) :
    (toConv (τ.comp (π : H →ₐ[k] MonoidAlgebra k X)) * y *
        (toConv (τ.comp (π : H →ₐ[k] MonoidAlgebra k X)))⁻¹).ofConv h =
      τ (MonoidAlgebra.single (Additive.toMul μ) 1) * y.ofConv h := by
  have hl : torusCoactLeft π h = MonoidAlgebra.single (Additive.toMul μ) 1 ⊗ₜ[k] h := by
    rw [mem_torusGrading] at hh
    have := congrArg (TensorProduct.comm k _ _) hh
    simpa [torusCoact] using this
  rw [← HopfAlgebra.productMap_comp_conjugationAlgHom, AlgHom.comp_apply, ofConv_toConv]
  have e : ∀ z : H ⊗[k] H,
      Algebra.TensorProduct.productMap (τ.comp (π : H →ₐ[k] MonoidAlgebra k X)) y.ofConv z =
      Algebra.TensorProduct.productMap τ y.ofConv
        (Algebra.TensorProduct.map (π : H →ₐ[k] MonoidAlgebra k X) (AlgHom.id k H) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [e]
  change Algebra.TensorProduct.productMap τ y.ofConv (torusCoactLeft π h) = _
  rw [hl, Algebra.TensorProduct.productMap_apply_tmul]

/-- Modulo `J_n`, a degree-`n` element is a combination of the degree-`n` generators. -/
lemma exists_sum_generators (hn : 0 < n) {r : ℕ} {x : Fin r → H} {d : Fin r → ℕ}
    (hxd : ∀ i, n ≤ d i ∧ x i ∈ lineGrading l (d i : ℤ))
    (hb : Function.Bijective (MvPolynomial.aeval (R := k)
      (fun i ↦ Ideal.Quotient.mk (filtrationIdeal l n) (x i))))
    {w : H} (hw : w ∈ lineGrading l (n : ℤ)) :
    ∃ c : {i : Fin r // d i = n} → k, w - ∑ i, c i • x i.1 ∈ filtrationIdeal l n := by
  classical
  set J := filtrationIdeal l n
  obtain ⟨p, hp⟩ := hb.2 (Ideal.Quotient.mk J w)
  set q := MvPolynomial.aeval (R := k) x p
  have hq : Ideal.Quotient.mk J q = Ideal.Quotient.mk J w := by
    rw [← hp]
    exact MvPolynomial.comp_aeval_apply (R := k) (f := x) (Ideal.Quotient.mkₐ k J) p
  have hwq : w - q ∈ J := Ideal.Quotient.eq.mp hq.symm
  have hJh : J.IsHomogeneous (lineGrading l) := filtrationIdeal_isHomogeneous l n
  have hproj := hJh (n : ℤ) hwq
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    DirectSum.decompose_of_mem_same _ hw] at hproj
  have hspan : (DirectSum.decompose (lineGrading l) q (n : ℤ) : H) ∈
      Submodule.span k (Set.range fun i : {i : Fin r // d i = n} ↦ x i.1) := by
    simp only [q]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', DirectSum.decompose_sum,
      DFinsupp.finset_sum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun α _ ↦ ?_
    have hm : (algebraMap k H (p.coeff α)) * ∏ i, x i ^ α i ∈
        lineGrading l (∑ i, α i • ((d i : ℕ) : ℤ)) := by
      have := SetLike.prod_pow_mem_graded (lineGrading l) (F := Finset.univ)
        (fun i ↦ ((d i : ℕ) : ℤ)) x α (fun i _ ↦ (hxd i).2)
      have h0 := algebraMap_mem_lineGrading_zero (l := l) (p.coeff α)
      simpa using SetLike.mul_mem_graded h0 this
    by_cases hdeg : (∑ i, α i • ((d i : ℕ) : ℤ)) = n
    · rw [hdeg] at hm
      rw [DirectSum.decompose_of_mem_same _ hm]
      have hα : ∑ j, α j * d j = n := by
        have : ((∑ j, α j * d j : ℕ) : ℤ) = n := by push_cast; simpa [nsmul_eq_mul] using hdeg
        exact_mod_cast this
      obtain ⟨i, rfl, hdi⟩ := eq_single_of_wdeg_eq hn (fun i ↦ (hxd i).1) hα
      have hprod : ∏ j, x j ^ (Finsupp.single i 1 : Fin r →₀ ℕ) j = x i := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj; simp [Finsupp.single_apply, Ne.symm hj]
        · simp
      rw [hprod, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hdi⟩, rfl⟩)
    · rw [DirectSum.decompose_of_mem_ne _ hm hdeg]
      exact zero_mem _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hspan
  exact ⟨c, by rw [hc]; exact hproj⟩

/-- **(F4) the vector quotient `U_{≥n} → V_n`, for a torus `S = ker φ ⊆ T · U_{≥n}`.**
`V_n = k^D` with `D` the degree-`n` generators of the bigraded (F3), a diagonal
`k[G]`-comodule with weights `c(μ_i)` (`exists_charMap`); `q(u) = ∑ u(x_i) ⊗ e_i`. -/
theorem exists_vecQuotient [IsAlgClosed k] (h : DynHyp l T) (hn : 0 < n) {G : Type u}
    [CommGroup G] (φ : H →ₐc[k] MonoidAlgebra k G)
    (hle : tuIdeal l T n ≤ RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k G)) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Comodule k (MonoidAlgebra k G) V)
      (q : ∀ (A : Type u) [CommRing A] [Algebra k A], WithConv (H →ₐ[k] A) → A ⊗[k] V),
      (∀ (A : Type u) [CommRing A] [Algebra k A] (u u' : WithConv (H →ₐ[k] A)),
        filtrationIdeal l n ≤ RingHom.ker u.ofConv → filtrationIdeal l n ≤ RingHom.ker u'.ofConv →
          q A (u * u') = q A u + q A u') ∧
      (∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (ψ : A →ₐ[k] B)
        (u : WithConv (H →ₐ[k] A)), filtrationIdeal l n ≤ RingHom.ker u.ofConv →
          LinearMap.rTensor V ψ.toLinearMap (q A u) = q B (AlgHom.mapValue ψ u)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A))
        (u : WithConv (H →ₐ[k] A)), filtrationIdeal l n ≤ RingHom.ker u.ofConv →
          q A (toConv (g.ofConv.comp (φ : H →ₐ[k] MonoidAlgebra k G)) * u *
            (toConv (g.ofConv.comp (φ : H →ₐ[k] MonoidAlgebra k G)))⁻¹) =
            Comodule.endOfPoint V g.ofConv (q A u)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra k A] (u : WithConv (H →ₐ[k] A)),
        filtrationIdeal l n ≤ RingHom.ker u.ofConv → q A u = 0 →
          filtrationIdeal l (n + 1) ≤ RingHom.ker u.ofConv) ∧
      (∀ y : V, ∃ w : WithConv (H →ₐ[k] k), w ∈ unipotent k l ∧
        filtrationIdeal l n ≤ RingHom.ker w.ofConv ∧ q k w = (1 : k) ⊗ₜ[k] y) := by
  classical
  obtain ⟨X, _, π, hπs, hπk⟩ := exists_split_of_isMaximalTorus T h.hT
  obtain ⟨χ, hχ⟩ := exists_weight_of_le_ker π hπs hπk h.hlT
  obtain ⟨r, x, d, μ, hx, hb⟩ := filtrationIdeal_polynomial_bigraded' l h.hP π χ hχ n
  obtain ⟨c, hc⟩ := exists_charMap h hn π hπs hπk φ hle
  have hsurj := tuMap_surjective h hn
  obtain ⟨Jn, hJn, -, -⟩ := filtrationIdeal_spec l h.hP n
  let D := {i : Fin r // d i = n}
  have hxD : ∀ i : D, x i.1 ∈ lineGrading l (n : ℤ) := fun i ↦ by
    have := (hx i.1).2.2.2.2; rwa [i.2] at this
  let wt : D → G := fun i ↦ c (Additive.toMul (μ i.1))
  letI : Comodule k (MonoidAlgebra k G) (D → k) := Comodule.ofWeights (Pi.basisFun k D) wt
  let q : ∀ (A : Type u) [CommRing A] [Algebra k A], WithConv (H →ₐ[k] A) → A ⊗[k] (D → k) :=
    fun A _ _ u ↦ ∑ i : D, u.ofConv (x i.1) ⊗ₜ Pi.single i (1 : k)
  -- coordinates of `q`
  have hcoord : ∀ (A : Type u) [CommRing A] [Algebra k A] (u : WithConv (H →ₐ[k] A)) (i : D),
      TensorProduct.rid k A (LinearMap.lTensor A (LinearMap.proj i) (q A u)) = u.ofConv (x i.1) := by
    intro A _ _ u i
    simp only [q, map_sum, LinearMap.lTensor_tmul, LinearMap.proj_apply,
      TensorProduct.rid_tmul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, Ne.symm hj]
    · simp
  have hJinv : ∀ {A : Type u} [CommRing A] [Algebra k A] {a : WithConv (H →ₐ[k] A)},
      filtrationIdeal l n ≤ RingHom.ker a.ofConv → filtrationIdeal l n ≤ RingHom.ker a⁻¹.ofConv := by
    intro A _ _ a ha; rw [← hJn] at ha ⊢; exact le_ker_inv ha
  have hJmul : ∀ {A : Type u} [CommRing A] [Algebra k A] {a b : WithConv (H →ₐ[k] A)},
      filtrationIdeal l n ≤ RingHom.ker a.ofConv → filtrationIdeal l n ≤ RingHom.ker b.ofConv →
        filtrationIdeal l n ≤ RingHom.ker (a * b).ofConv := by
    intro A _ _ a b ha hb; rw [← hJn] at ha hb ⊢; exact le_ker_mul ha hb
  have hP := h.hP
  refine ⟨D → k, inferInstance, inferInstance, inferInstance, q, ?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ u u' hu hu'
    simp only [q, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [apply_mul_of_mem_lineGrading hP hn (hxD i) hu hu', add_tmul]
  · intro A B _ _ _ _ ψ u _
    simp [q, map_sum, AlgHom.mapValue_apply]
  · intro A _ _ g u hu
    set s : WithConv (H →ₐ[k] A) := toConv (g.ofConv.comp (φ : H →ₐ[k] MonoidAlgebra k G))
    have hsT : tuIdeal l T n ≤ RingHom.ker s.ofConv := by
      intro z hz
      have h' : φ z = 0 := RingHom.mem_ker.mp (hle hz)
      simp [s, h']
    obtain ⟨t, a, ht, ha, hst⟩ := exists_eq_mul_of_tuIdeal_le hsurj hsT
    have hta : filtrationIdeal l n ≤ RingHom.ker (t⁻¹ * s).ofConv := by
      rw [hst, inv_mul_cancel_left]; exact ha
    -- `t = τ ∘ π`
    have hker : RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X) ≤ RingHom.ker t.ofConv := hπk ▸ ht
    let eπ := Ideal.quotientKerAlgEquivOfSurjective (f := (π : H →ₐ[k] MonoidAlgebra k X)) hπs
    let τ : MonoidAlgebra k X →ₐ[k] A :=
      (Ideal.Quotient.liftₐ _ t.ofConv fun a ha ↦ RingHom.mem_ker.mp (hker ha)).comp
        eπ.symm.toAlgHom
    have hτ : ∀ y, τ (π y) = t.ofConv y := by
      intro y
      have : eπ.symm (π y) = Ideal.Quotient.mk _ y := by
        rw [AlgEquiv.symm_apply_eq]
        exact (Ideal.quotientKerAlgEquivOfSurjective_mk
          (f := (π : H →ₐ[k] MonoidAlgebra k X)) hπs y).symm
      change Ideal.Quotient.liftₐ (RingHom.ker (π : H →ₐ[k] MonoidAlgebra k X)) t.ofConv
        (fun a ha ↦ RingHom.mem_ker.mp (hker ha)) (eπ.symm (π y)) = _
      rw [this]
      rfl
    have htτ : t = toConv (τ.comp (π : H →ₐ[k] MonoidAlgebra k X)) := by
      apply ofConv_injective
      exact AlgHom.ext fun y ↦ (hτ y).symm
    simp only [q, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have e1 : (s * u * s⁻¹).ofConv (x i.1) =
        g.ofConv (MonoidAlgebra.single (wt i) 1) * u.ofConv (x i.1) := by
      have hconj : s * u * s⁻¹ = t * (a * u * a⁻¹) * t⁻¹ := by rw [hst]; group
      rw [hconj]
      rw [htτ]
      rw [apply_torus_conj π (hx i.1).2.2.2.1 τ]
      obtain ⟨x', hx'⟩ := hπs (MonoidAlgebra.single (Additive.toMul (μ i.1)) 1)
      have hcx := hc A g t ht hta _ x' hx'
      have hτ' : τ (MonoidAlgebra.single (Additive.toMul (μ i.1)) 1) = t.ofConv x' := by
        rw [← hx', hτ]
      rw [hτ', hcx]
      congr 1
      have hai := hJinv ha
      rw [apply_mul_of_mem_lineGrading hP hn (hxD i) (hJmul ha hu) hai,
        apply_mul_of_mem_lineGrading hP hn (hxD i) ha hu]
      have h1 := apply_mul_of_mem_lineGrading hP hn (hxD i) ha hai
      rw [mul_inv_cancel] at h1
      have h0 : (1 : WithConv (H →ₐ[k] A)).ofConv (x i.1) = 0 := by
        rw [AlgHom.convOne_apply,
          counit_eq_zero_of_mem_lineGrading l (by exact_mod_cast hn.ne') (hxD i), map_zero]
      rw [h0] at h1
      linear_combination -h1
    rw [e1, Comodule.endOfPoint_tmul]
    have hco : Comodule.coact (R := k) (C := MonoidAlgebra k G) (Pi.single i (1 : k) : D → k) =
        Pi.single i (1 : k) ⊗ₜ MonoidAlgebra.single (wt i) (1 : k) := by
      have := Comodule.ofWeights_coact_basis (Pi.basisFun k D) wt i
      simpa using this
    rw [hco]
    simp [TensorProduct.smul_tmul', mul_comm]
  · intro A _ _ u hu hq0
    have hxi : ∀ i : D, u.ofConv (x i.1) = 0 := fun i ↦ by
      rw [← hcoord A u i, hq0]; simp
    rw [filtrationIdeal]
    refine sup_le ((unip_le_filtrationIdeal l n).trans hu) ?_
    rw [Ideal.span_le]
    intro w hw
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hw
    obtain ⟨m, ⟨hm0, hm⟩, hwm⟩ := hw
    rcases Nat.lt_or_ge m n with hlt | hge
    · exact hu (mem_filtrationIdeal_of_lt l hm0 hlt hwm)
    · have hmn : m = n := by omega
      rw [hmn] at hwm
      obtain ⟨cc, hcc⟩ := exists_sum_generators hn (fun i ↦ ⟨(hx i).1, (hx i).2.2.2.2⟩) hb hwm
      have := hu hcc
      rw [RingHom.mem_ker, map_sub, map_sum, sub_eq_zero] at this
      rw [SetLike.mem_coe, RingHom.mem_ker, this]
      simp [hxi]
  · intro y
    set J := filtrationIdeal l n
    let e := AlgEquiv.ofBijective
      (MvPolynomial.aeval (R := k) (fun i ↦ Ideal.Quotient.mk J (x i))) hb
    let v : Fin r → k := fun i ↦ if hi : d i = n then y ⟨i, hi⟩ else 0
    let u0 : (H ⧸ J) →ₐ[k] k := (MvPolynomial.aeval v).comp e.symm.toAlgHom
    let w : WithConv (H →ₐ[k] k) := toConv (u0.comp (Ideal.Quotient.mkₐ k J))
    have hwx : ∀ i, w.ofConv (x i) = v i := by
      intro i
      have : e.symm (Ideal.Quotient.mk J (x i)) = MvPolynomial.X i := by
        rw [AlgEquiv.symm_apply_eq]
        simp [e]
      simp [w, u0, this]
    have hJ : J ≤ RingHom.ker w.ofConv := fun z hz ↦ by
      simp [w, u0, Ideal.Quotient.eq_zero_iff_mem.mpr hz]
    refine ⟨w, ?_, hJ, ?_⟩
    · have := (unip_le_filtrationIdeal l n).trans hJ
      rw [BialgHom.unipotentDefiningHopfIdeal_toIdeal] at this
      exact (BialgHom.unipotentCoefficientIdeal_le_ker_iff l w).mp this
    · simp only [q, hwx]
      conv_rhs => rw [← Finset.univ_sum_single y, tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [show (Pi.single i (y i) : D → k) = y i • Pi.single i (1 : k) by
        ext j; simp [Pi.single_apply]]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [v, dif_pos i.2]
      rfl

/-! ## The step -/

/-- **Step 4 of T1-dyn**, same statement as `tuIdeal_step`. -/
theorem tuIdeal_step' (h : DynHyp l T) [IsAlgClosed k] (hn : 0 < n)
    (S : HopfIdeal k H) (hS : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) S)
    (hle : tuIdeal l T n ≤ S.toIdeal) :
    ∃ v : WithConv (H →ₐ[k] k), v ∈ unipotent k l ∧ tuIdeal l T (n + 1) ≤ (S.conjugate v).toIdeal := by
  classical
  have hsurj := tuMap_surjective h hn
  -- the filtration subgroups are normal Hopf ideals ((F3))
  have hJ : ∀ m, ∃ J : HopfIdeal k H, J.toIdeal = filtrationIdeal l m ∧ J.IsNormal :=
    fun m ↦ by
      obtain ⟨J, hJ, hJn, -⟩ := filtrationIdeal_spec l h.hP m
      exact ⟨J, hJ, hJn⟩
  obtain ⟨Jn, hJn, hJnN⟩ := hJ n
  obtain ⟨Jn1, hJn1, hJn1N⟩ := hJ (n + 1)
  have jmul : ∀ {A : Type u} [CommRing A] [Algebra k A] {x y : WithConv (H →ₐ[k] A)},
      filtrationIdeal l n ≤ RingHom.ker x.ofConv → filtrationIdeal l n ≤ RingHom.ker y.ofConv →
        filtrationIdeal l n ≤ RingHom.ker (x * y).ofConv := by
    intro A _ _ x y hx hy
    rw [← hJn] at hx hy ⊢
    exact le_ker_mul hx hy
  have jinv : ∀ {A : Type u} [CommRing A] [Algebra k A] {x : WithConv (H →ₐ[k] A)},
      filtrationIdeal l n ≤ RingHom.ker x.ofConv → filtrationIdeal l n ≤ RingHom.ker x⁻¹.ofConv := by
    intro A _ _ x hx
    rw [← hJn] at hx ⊢
    exact le_ker_inv hx
  have jconj : ∀ {A : Type u} [CommRing A] [Algebra k A] {x : WithConv (H →ₐ[k] A)},
      filtrationIdeal l n ≤ RingHom.ker x.ofConv → ∀ b : WithConv (H →ₐ[k] A),
        filtrationIdeal l n ≤ RingHom.ker (b * x * b⁻¹).ofConv := by
    intro A _ _ x hx b
    rw [← hJn] at hx ⊢
    exact le_ker_conj hJnN hx b
  have j1conj : ∀ {A : Type u} [CommRing A] [Algebra k A] {x : WithConv (H →ₐ[k] A)},
      filtrationIdeal l (n + 1) ≤ RingHom.ker x.ofConv → ∀ b : WithConv (H →ₐ[k] A),
        filtrationIdeal l (n + 1) ≤ RingHom.ker (b * x * b⁻¹).ofConv := by
    intro A _ _ x hx b
    rw [← hJn1] at hx ⊢
    exact le_ker_conj hJn1N hx b
  -- split the torus `S` and take the vector quotient `V_n`
  obtain ⟨G, _, φ, hφs, hφk⟩ := exists_split_of_isMaximalTorus S hS
  obtain ⟨V, _, _, _, q, qmul, qnat, qconj, qker, qlift⟩ := exists_vecQuotient h hn φ (by rw [hφk]; exact hle)
  -- the points of `S`
  let s : ∀ (A : Type u) [CommRing A] [Algebra k A], WithConv (MonoidAlgebra k G →ₐ[k] A) →
      WithConv (H →ₐ[k] A) := fun A _ _ g ↦ toConv (g.ofConv.comp (φ : H →ₐ[k] MonoidAlgebra k G))
  have s_mul : ∀ (A : Type u) [CommRing A] [Algebra k A] (g g' : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      s A (g * g') = s A g * s A g' := by
    intro A _ _ g g'
    exact congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib g g' φ)
  have s_S : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      tuIdeal l T n ≤ RingHom.ker (s A g).ofConv := by
    intro A _ _ g z hz
    have hz' : z ∈ RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k G) := hφk ▸ hle hz
    simp only [s, RingHom.mem_ker, ofConv_toConv, AlgHom.comp_apply] at hz' ⊢
    rw [hz', map_zero]
  have s_nat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (ψ : A →ₐ[k] B) (g : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      AlgHom.mapValue ψ (s A g) = s B (AlgHom.mapValue ψ g) := by
    intro A B _ _ _ _ ψ g
    simp [s, AlgHom.comp_assoc]
  -- the `T`-component of a point of `S`
  let tc : ∀ (A : Type u) [CommRing A] [Algebra k A], WithConv (MonoidAlgebra k G →ₐ[k] A) →
      WithConv (H →ₐ[k] A) := fun A _ _ g ↦ (exists_eq_mul_of_tuIdeal_le hsurj (s_S A g)).choose
  have tc_spec : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      T.toIdeal ≤ RingHom.ker (tc A g).ofConv ∧
        filtrationIdeal l n ≤ RingHom.ker ((tc A g)⁻¹ * s A g).ofConv := by
    intro A _ _ g
    obtain ⟨u, ht, hu, hx⟩ := (exists_eq_mul_of_tuIdeal_le hsurj (s_S A g)).choose_spec
    refine ⟨ht, ?_⟩
    have : (tc A g)⁻¹ * s A g = u := by
      change _ * s A g = u
      rw [hx, inv_mul_cancel_left]
    rw [this]; exact hu
  -- uniqueness of `tc`
  have tc_eq : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A))
      (t : WithConv (H →ₐ[k] A)), T.toIdeal ≤ RingHom.ker t.ofConv →
        filtrationIdeal l n ≤ RingHom.ker (t⁻¹ * s A g).ofConv → tc A g = t := by
    intro A _ _ g t ht hu
    have h1 : tc A g * ((tc A g)⁻¹ * s A g) = t * (t⁻¹ * s A g) := by
      rw [mul_inv_cancel_left, mul_inv_cancel_left]
    exact (eq_of_mul_eq_mul hsurj (tc_spec A g).1 (tc_spec A g).2 ht hu h1).1
  -- `x t⁻¹ ∈ U_{≥n}`
  have su_mem : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      filtrationIdeal l n ≤ RingHom.ker (s A g * (tc A g)⁻¹).ofConv := by
    intro A _ _ g
    have := jconj (tc_spec A g).2 (tc A g)
    rwa [mul_inv_cancel_left] at this
  -- `q` vanishes at `1`, is odd, and is invariant under conjugation by `U_{≥n}`
  have q_one : ∀ (A : Type u) [CommRing A] [Algebra k A], q A 1 = 0 := by
    intro A _ _
    have h1 : filtrationIdeal l n ≤ RingHom.ker (1 : WithConv (H →ₐ[k] A)).ofConv := by
      rw [← hJn]; exact le_ker_one
    have := qmul A 1 1 h1 h1
    rw [mul_one] at this
    simpa using this
  have q_inv : ∀ (A : Type u) [CommRing A] [Algebra k A] (u : WithConv (H →ₐ[k] A)),
      filtrationIdeal l n ≤ RingHom.ker u.ofConv → q A u⁻¹ = - q A u := by
    intro A _ _ u hu
    have := qmul A u u⁻¹ hu (jinv hu)
    rw [mul_inv_cancel, q_one] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have q_conjU : ∀ (A : Type u) [CommRing A] [Algebra k A] (a u : WithConv (H →ₐ[k] A)),
      filtrationIdeal l n ≤ RingHom.ker a.ofConv → filtrationIdeal l n ≤ RingHom.ker u.ofConv →
        q A (a * u * a⁻¹) = q A u := by
    intro A _ _ a u ha hu
    rw [qmul A _ _ (jmul ha hu) (jinv ha), qmul A _ _ ha hu, q_inv A a ha]
    abel
  -- conjugation by `tc g` acts on `V_n` like conjugation by `s g`
  have q_conjT : ∀ (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (MonoidAlgebra k G →ₐ[k] A))
      (u : WithConv (H →ₐ[k] A)), filtrationIdeal l n ≤ RingHom.ker u.ofConv →
        q A (tc A g * u * (tc A g)⁻¹) = Comodule.endOfPoint V g.ofConv (q A u) := by
    intro A _ _ g u hu
    set a := s A g * (tc A g)⁻¹
    have ha := su_mem A g
    have hsa : s A g = a * tc A g := by simp [a]
    have := qconj A g u hu
    change q A (s A g * u * (s A g)⁻¹) = _ at this
    rw [← this, hsa, mul_inv_rev]
    have e : a * tc A g * u * ((tc A g)⁻¹ * a⁻¹) = a * (tc A g * u * (tc A g)⁻¹) * a⁻¹ := by
      group
    rw [e, q_conjU A a _ ha (jconj hu _)]
  -- the cocycle
  let c : ∀ (A : Type u) [CommRing A] [Algebra k A], WithConv (MonoidAlgebra k G →ₐ[k] A) →
      A ⊗[k] V := fun A _ _ g ↦ q A (s A g * (tc A g)⁻¹)
  have hc : ∀ (A : Type u) [CommRing A] [Algebra k A] (g g' : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      c A (g * g') = c A g + Comodule.endOfPoint V g.ofConv (c A g') := by
    intro A _ _ g g'
    -- `tc (g g') = tc g * tc g'`
    have htc : tc A (g * g') = tc A g * tc A g' := by
      apply tc_eq
      · exact le_ker_mul (tc_spec A g).1 (tc_spec A g').1
      · rw [s_mul, mul_inv_rev]
        have e : (tc A g')⁻¹ * (tc A g)⁻¹ * (s A g * s A g') =
            (tc A g')⁻¹ * ((tc A g)⁻¹ * s A g) * tc A g' * ((tc A g')⁻¹ * s A g') := by group
        rw [e]
        refine jmul ?_ (tc_spec A g').2
        have := jconj (tc_spec A g).2 (tc A g')⁻¹
        rwa [inv_inv] at this
    simp only [c]
    rw [htc, s_mul, mul_inv_rev]
    have e : s A g * s A g' * ((tc A g')⁻¹ * (tc A g)⁻¹) =
        (s A g * (tc A g)⁻¹) * (tc A g * (s A g' * (tc A g')⁻¹) * (tc A g)⁻¹) := by group
    rw [e, qmul A _ _ (su_mem A g) (jconj (su_mem A g') _), q_conjT A g _ (su_mem A g')]
  have hcnat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (ψ : A →ₐ[k] B) (g : WithConv (MonoidAlgebra k G →ₐ[k] A)),
      LinearMap.rTensor V ψ.toLinearMap (c A g) = c B (AlgHom.mapValue ψ g) := by
    intro A B _ _ _ _ ψ g
    have htc : tc B (AlgHom.mapValue ψ g) = AlgHom.mapValue ψ (tc A g) := by
      apply tc_eq
      · exact le_ker_mapValue ψ (tc_spec A g).1
      · rw [← s_nat, ← map_inv, ← map_mul]
        exact le_ker_mapValue ψ (tc_spec A g).2
    simp only [c]
    rw [qnat A B ψ _ (su_mem A g), htc, map_mul, map_inv, s_nat]
  obtain ⟨y, hy⟩ := exists_eq_sub_of_natural_cocycle c hc hcnat
  -- lift `y` to `w ∈ U_{≥n}(k)`
  obtain ⟨w, hwU, hwJ, hwq⟩ := qlift y
  refine ⟨w⁻¹, inv_mem hwU, ?_⟩
  -- the universal point of `S.conjugate w⁻¹`
  set I := (S.conjugate w⁻¹).toIdeal
  let Q := H ⧸ I
  let π : WithConv (H →ₐ[k] Q) := toConv (Ideal.Quotient.mkₐ k I)
  let wQ : WithConv (H →ₐ[k] Q) := AlgHom.mapValue (H := H) (Algebra.ofId k Q) w
  have hwQJ : filtrationIdeal l n ≤ RingHom.ker wQ.ofConv := le_ker_mapValue _ hwJ
  have hwQq : q Q wQ = (1 : Q) ⊗ₜ[k] y := by
    rw [← qnat k Q (Algebra.ofId k Q) w hwJ, hwq]
    simp
  -- `x := w π w⁻¹` is a point of `S`
  let x : WithConv (H →ₐ[k] Q) := wQ * π * wQ⁻¹
  have hxS : S.toIdeal ≤ RingHom.ker x.ofConv := by
    have hmem := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff S w⁻¹ (CommAlgCat.of k Q)
      (x : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k Q))).1
    have hπ : (AlgHom.mapValue (H := H) (Algebra.ofId k (CommAlgCat.of k Q)) w⁻¹ * x *
        (AlgHom.mapValue (H := H) (Algebra.ofId k (CommAlgCat.of k Q)) w⁻¹)⁻¹ :
          HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k Q)) = π := by
      rw [map_inv]
      show wQ⁻¹ * (wQ * π * wQ⁻¹) * wQ⁻¹⁻¹ = π
      group
    intro z hz
    have := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).1 (hmem (by
      rw [hπ, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      intro h hh
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hh)) z hz
    exact this
  -- write `x = s g`
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := (φ : H →ₐ[k] MonoidAlgebra k G)) hφs
  let g : WithConv (MonoidAlgebra k G →ₐ[k] Q) := toConv
    ((Ideal.Quotient.liftₐ (RingHom.ker (φ : H →ₐ[k] MonoidAlgebra k G)) x.ofConv
      fun a ha ↦ RingHom.mem_ker.mp (hxS (hφk ▸ ha))).comp e.symm.toAlgHom)
  have hxg : s Q g = x := by
    apply ofConv_injective
    ext z
    have : e.symm (φ z) = Ideal.Quotient.mk _ z := by
      rw [AlgEquiv.symm_apply_eq]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk
        (f := (φ : H →ₐ[k] MonoidAlgebra k G)) hφs z).symm
    simp [s, g, this]
    rfl
  -- conclude with the factorization `π = t * z`
  set t := tc Q g
  have ht := (tc_spec Q g).1
  have hπ : π = t * (t⁻¹ * π) := by group
  have key : filtrationIdeal l (n + 1) ≤ RingHom.ker (t⁻¹ * π).ofConv := by
    set m := wQ⁻¹ * (x * t⁻¹) * (t * wQ * t⁻¹)
    have hxt : filtrationIdeal l n ≤ RingHom.ker (x * t⁻¹).ofConv := hxg ▸ su_mem Q g
    have hmJ : filtrationIdeal l n ≤ RingHom.ker m.ofConv :=
      jmul (jmul (jinv hwQJ) hxt) (jconj hwQJ t)
    have hm0 : q Q m = 0 := by
      have h1 := qmul Q _ _ (jmul (jinv hwQJ) hxt) (jconj hwQJ t)
      have h2 := qmul Q _ _ (jinv hwQJ) hxt
      have h3 := q_conjT Q g wQ hwQJ
      have h4 := hy Q g
      simp only [c] at h4
      rw [hxg] at h4
      simp only [m]
      rw [h1, h2, h3, q_inv Q _ hwQJ, hwQq, h4]
      abel
    have hm1 := qker Q m hmJ hm0
    have := j1conj hm1 t⁻¹
    have e' : t⁻¹ * m * t⁻¹⁻¹ = t⁻¹ * π := by
      simp only [m, x]
      group
    rwa [e'] at this
  have hfin := tuIdeal_le_ker_of_eq_mul ht key hπ
  intro z hz
  have := hfin hz
  rw [RingHom.mem_ker] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end TU

end AlgMag.Reductive

