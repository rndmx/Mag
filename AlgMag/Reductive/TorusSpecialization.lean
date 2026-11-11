/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.NoTorusUnipotent

/-!
# Torus specialization: `NoNontrivialTorus` ascends along algebraically closed extensions

`noNontrivialTorus_baseChange`: for `k ⊆ K` algebraically closed fields and `Q` a finite-type
commutative Hopf `k`-algebra, `NoNontrivialTorus k Q → NoNontrivialTorus K (K ⊗[k] Q)`.

Proof (contrapositive). A torus quotient of `K ⊗ Q` with a nontrivial `K`-point is split
(`K = K̄`), giving a surjective bialgebra map `φ : K ⊗ Q → K[M]`, `M = ℤ^n`, `n ≥ 1`. Its
restriction `ψ` to `Q` has coefficients in a finitely generated `k`-subalgebra `R ⊆ K`, which
also contains the coefficients needed to hit the generators `t_i^{±1}`. A `k`-point `ρ : R → k`
(Nullstellensatz) specializes `ψ` to `ψ₀ : Q → k[M]`. The bialgebra axioms are checked on
coefficients (scalar identities over `R`, pushed along `ρ`). `ψ₀` is surjective, its kernel is
a torus Hopf ideal of `Q`, and `t ↦ (a, …, a)` (`a ≠ 0, 1`) is a nontrivial point on it.
-/

open TauCeti CategoryTheory TensorProduct
open AlgMag.Reductive.NoTorusUnipotent

namespace AlgMag.Reductive.TorusSpecialization

universe u

noncomputable section

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### Coefficient functionals on group algebras -/

section Coeff

variable {M : Type u} [Monoid M]

/-- The coefficient at `m`, as an `A`-linear functional. -/
def cf (A : Type u) [CommRing A] (m : M) : MonoidAlgebra A M →ₗ[A] A where
  toFun x := x.coeff m
  map_add' x y := by simp [MonoidAlgebra.coeff_add]
  map_smul' r x := by simp

@[simp] theorem cf_apply (A : Type u) [CommRing A] (m : M) (x : MonoidAlgebra A M) :
    cf A m x = x.coeff m := rfl

/-- The pairing with `m ⊗ m'` on `A[M] ⊗ A[M]`. -/
def T (A : Type u) [CommRing A] (m m' : M) :
    MonoidAlgebra A M ⊗[A] MonoidAlgebra A M →ₗ[A] A :=
  TensorProduct.lift ((LinearMap.mul A A).compl₁₂ (cf A m) (cf A m'))

@[simp] theorem T_tmul (A : Type u) [CommRing A] (m m' : M) (x y : MonoidAlgebra A M) :
    T A m m' (x ⊗ₜ y) = x.coeff m * y.coeff m' := by
  simp [T]

theorem T_comul (A : Type u) [CommRing A] (m m' : M) (z : MonoidAlgebra A M) :
    T A m m' (Coalgebra.comul (R := A) z) = if m = m' then z.coeff m else 0 := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    split_ifs <;> simp [MonoidAlgebra.coeff_add]
  | single m₀ r =>
    rw [MonoidAlgebra.comul_single]
    simp only [CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      T_tmul, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h1 : m₀ = m <;> by_cases h2 : m = m' <;> subst_vars <;> simp_all

/-- The `k`-bilinear coefficient pairing of a `k`-linear map `f : Q → A[M]`. -/
def β {k : Type u} [CommRing k] {Q : Type u} [AddCommGroup Q] [Module k Q]
    (A : Type u) [CommRing A] [Algebra k A] (f : Q →ₗ[k] MonoidAlgebra A M) (m m' : M) :
    Q →ₗ[k] Q →ₗ[k] A :=
  (LinearMap.mul k A).compl₁₂ ((cf A m).restrictScalars k ∘ₗ f)
    ((cf A m').restrictScalars k ∘ₗ f)

@[simp] theorem β_apply {k : Type u} [CommRing k] {Q : Type u} [AddCommGroup Q] [Module k Q]
    (A : Type u) [CommRing A] [Algebra k A] (f : Q →ₗ[k] MonoidAlgebra A M) (m m' : M)
    (a b : Q) : β A f m m' a b = (f a).coeff m * (f b).coeff m' := rfl

/-- Pushing a coefficient pairing along an algebra map of coefficient rings. -/
theorem lift_β_map {k : Type u} [CommRing k] {Q : Type u} [AddCommGroup Q] [Module k Q]
    {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] (g : A →ₐ[k] B)
    (f : Q →ₗ[k] MonoidAlgebra A M) (m m' : M) (x : Q ⊗[k] Q) :
    g (TensorProduct.lift (β A f m m') x) =
      TensorProduct.lift (β B ((MonoidAlgebra.mapAlgHom M g).toLinearMap ∘ₗ f) m m') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [MonoidAlgebra.coeff_mapAlgHom]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Over a field, `A[M] ⊗ A[M]` is separated by the pairings `T m m'`. -/
theorem ext_T {k : Type u} [Field k] {x y : MonoidAlgebra k M ⊗[k] MonoidAlgebra k M}
    (h : ∀ m m', T k m m' x = T k m m' y) : x = y := by
  let b := (MonoidAlgebra.basis M k).tensorProduct (MonoidAlgebra.basis M k)
  have hb : ∀ m m', T k m m' = (Finsupp.lapply (m, m')) ∘ₗ b.repr.toLinearMap := by
    intro m m'
    ext a c
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      T_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Finsupp.lapply_apply, b, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  apply b.repr.injective
  ext ⟨m, m'⟩
  have := h m m'
  rw [hb] at this
  simpa using this

/-- A `k`-algebra map `Q → k[M]` satisfying the coefficient identities is a bialgebra map. -/
def ofCoeff {k : Type u} [Field k] {Q : Type u} [CommRing Q] [Bialgebra k Q]
    (f : Q →ₐ[k] MonoidAlgebra k M)
    (hε : ∀ q, Coalgebra.counit (R := k) (f q) = Coalgebra.counit (R := k) q)
    (hΔ : ∀ q m m', TensorProduct.lift (β k f.toLinearMap m m') (Coalgebra.comul (R := k) q) =
      if m = m' then (f q).coeff m else 0) :
    Q →ₐc[k] MonoidAlgebra k M :=
  BialgHom.ofAlgHom f (by ext q; simpa using hε q) (by
    ext q
    apply ext_T
    intro m m'
    have key : ∀ x : Q ⊗[k] Q, T k m m' (Algebra.TensorProduct.map f f x) =
        TensorProduct.lift (β k f.toLinearMap m m') x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
    rw [key, hΔ, T_comul])

@[simp] theorem ofCoeff_apply {k : Type u} [Field k] {Q : Type u} [CommRing Q] [Bialgebra k Q]
    (f : Q →ₐ[k] MonoidAlgebra k M) (hε hΔ) (q : Q) : ofCoeff f hε hΔ q = f q := rfl

/-- Counits commute with changing the coefficient ring. -/
theorem counit_mapAlgHom {k : Type u} [CommRing k] {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (z : MonoidAlgebra A M) :
    Coalgebra.counit (R := B) (MonoidAlgebra.mapAlgHom M g z) =
      g (Coalgebra.counit (R := A) z) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | single m r => simp [MonoidAlgebra.counit_single]

end Coeff

/-! ### The restriction of a bialgebra map `K ⊗ Q → K[M]` to `Q` -/

section Upstairs

variable {k K Q : Type u} [Field k] [Field K] [Algebra k K] [CommRing Q] [HopfAlgebra k Q]
  {M : Type u} [Monoid M]

/-- `ψ q = φ (1 ⊗ q)`. -/
def ψ (φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M) : Q →ₐ[k] MonoidAlgebra K M :=
  ((φ : K ⊗[k] Q →ₐ[K] MonoidAlgebra K M).restrictScalars k).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem ψ_apply (φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M) (q : Q) :
    ψ φ q = φ (1 ⊗ₜ q) := rfl

theorem ψ_comul (φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M) (q : Q) (m m' : M) :
    TensorProduct.lift (β K (ψ φ).toLinearMap m m') (Coalgebra.comul (R := k) q) =
      if m = m' then (ψ φ q).coeff m else 0 := by
  have h := congrArg (T K m m')
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul φ) ((1 : K) ⊗ₜ[k] q))
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  rw [T_comul, TensorProduct.comul_tmul] at h
  refine Eq.trans ?_ h
  induction (Coalgebra.comul (R := k) q) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [tmul_add, map_add, map_add, map_add, map_add, hx, hy]

theorem ψ_counit (φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M) (q : Q) :
    Coalgebra.counit (R := K) (ψ φ q) = algebraMap k K (Coalgebra.counit (R := k) q) := by
  rw [ψ_apply, CoalgHomClass.counit_comp_apply, TensorProduct.counit_tmul]
  simp [Algebra.algebraMap_eq_smul_one]

end Upstairs

/-! ### Specialization along a `k`-point of a finitely generated subalgebra of `K` -/

section Descent

variable {k K Q : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [CommRing Q]
  [HopfAlgebra k Q] [Algebra.FiniteType k Q] {M : Type u} [Monoid M]

theorem descent (φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M) (hφ : Function.Surjective φ)
    (Gs : Finset M) :
    ∃ ψ₀ : Q →ₐc[k] MonoidAlgebra k M, ∀ m ∈ Gs,
      MonoidAlgebra.single m (1 : k) ∈ (ψ₀ : Q →ₐ[k] MonoidAlgebra k M).range := by
  obtain ⟨gens, hgens⟩ := Algebra.FiniteType.out (R := k) (A := Q)
  choose x hx using fun m : M ↦ hφ (MonoidAlgebra.single m 1)
  choose S hS using fun m : M ↦ TensorProduct.exists_finset (x m)
  let s : Finset K := gens.biUnion (fun q ↦ (ψ φ q).coeff.frange) ∪
    Gs.biUnion (fun m ↦ (S m).image Prod.fst)
  let R : Subalgebra k K := Algebra.adjoin k (s : Set K)
  have : Algebra.FiniteType k R := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  let ι : MonoidAlgebra R M →ₐ[k] MonoidAlgebra K M := MonoidAlgebra.mapAlgHom M R.val
  have hιc : ∀ z m, (ι z).coeff m = (z.coeff m : K) := fun z m ↦ by
    simp [ι, MonoidAlgebra.coeff_mapAlgHom]
  have hι : Function.Injective ι := by
    intro z w h
    apply MonoidAlgebra.ext
    ext m
    have := congrArg (fun y ↦ y.coeff m) h
    simpa [hιc] using this
  have hmem : ∀ z : MonoidAlgebra K M, (∀ m, z.coeff m ∈ R) → z ∈ ι.range := by
    intro z hz
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun m ↦ ⟨z.coeff m, hz m⟩) ?_), ?_⟩
    · apply z.coeff.support.finite_toSet.subset
      intro m hm
      rw [Function.mem_support] at hm
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hm (Subtype.ext h0)
    · apply MonoidAlgebra.ext
      ext m
      exact (hιc _ m).trans rfl
  have hrange : ∀ q, ψ φ q ∈ ι.range := by
    have hle : Algebra.adjoin k (gens : Set Q) ≤ ι.range.comap (ψ φ) := by
      rw [Algebra.adjoin_le_iff]
      intro q hq
      apply hmem
      intro m
      show (ψ φ q).coeff m ∈ R
      by_cases h0 : (ψ φ q).coeff m = 0
      · rw [h0]; exact R.zero_mem
      · apply Algebra.subset_adjoin
        rw [Finset.coe_union]
        left
        exact Finset.mem_biUnion.2 ⟨q, hq, Finsupp.mem_frange.2 ⟨h0, m, rfl⟩⟩
    intro q
    exact hle (hgens ▸ Algebra.mem_top)
  let e := AlgEquiv.ofInjective ι hι
  let ψR : Q →ₐ[k] MonoidAlgebra R M :=
    (e.symm : ι.range →ₐ[k] MonoidAlgebra R M).comp ((ψ φ).codRestrict ι.range hrange)
  have hψR : ∀ q, ι (ψR q) = ψ φ q := fun q ↦
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ φ q, hrange q⟩)
  have hc : ∀ q m, ((ψR q).coeff m : K) = (ψ φ q).coeff m := fun q m ↦ by
    rw [← hψR, hιc]
  obtain ⟨ρ⟩ : Nonempty (R →ₐ[k] k) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact not_isNilpotent_one ((forall_algHom_apply_eq_zero_iff_isNilpotent (K := k)
      (1 : R)).1 fun f ↦ (hne.false f).elim)
  let ψ0 : Q →ₐ[k] MonoidAlgebra k M := (MonoidAlgebra.mapAlgHom M ρ).comp ψR
  have hf : (MonoidAlgebra.mapAlgHom M R.val).toLinearMap ∘ₗ ψR.toLinearMap =
      (ψ φ).toLinearMap := LinearMap.ext hψR
  have hΔR : ∀ q m m', TensorProduct.lift (β R ψR.toLinearMap m m')
      (Coalgebra.comul (R := k) q) = if m = m' then (ψR q).coeff m else 0 := by
    intro q m m'
    apply Subtype.val_injective
    have h1 := lift_β_map R.val ψR.toLinearMap m m' (Coalgebra.comul (R := k) q)
    rw [hf, ψ_comul] at h1
    rw [← Subalgebra.coe_val]
    rw [h1]
    split_ifs <;> simp [hc]
  have hεR : ∀ q, Coalgebra.counit (R := R) (ψR q) =
      algebraMap k R (Coalgebra.counit (R := k) q) := by
    intro q
    apply Subtype.val_injective
    rw [← Subalgebra.coe_val]
    rw [← counit_mapAlgHom, show MonoidAlgebra.mapAlgHom M R.val (ψR q) = ψ φ q from hψR q,
      ψ_counit, AlgHom.commutes]
  let ψ₀ : Q →ₐc[k] MonoidAlgebra k M := ofCoeff ψ0
    (fun q ↦ by
      change Coalgebra.counit (R := k) (MonoidAlgebra.mapAlgHom M ρ (ψR q)) = _
      rw [counit_mapAlgHom, hεR, AlgHom.commutes]
      rfl)
    (fun q m m' ↦ by
      have h1 := lift_β_map ρ ψR.toLinearMap m m' (Coalgebra.comul (R := k) q)
      change _ = TensorProduct.lift (β k ψ0.toLinearMap m m') _ at h1
      rw [← h1, hΔR]
      split_ifs <;> simp [ψ0, MonoidAlgebra.coeff_mapAlgHom])
  refine ⟨ψ₀, fun m hm ↦ ?_⟩
  let cR : K → R := fun c ↦ if h : c ∈ R then ⟨c, h⟩ else 0
  have hcR : ∀ i ∈ S m, (cR i.1 : K) = i.1 := by
    intro i hi
    have : i.1 ∈ R := Algebra.subset_adjoin (by
      rw [Finset.coe_union]
      right
      exact Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image_of_mem _ hi⟩)
    simp [cR, this]
  have hK : ∀ m', ∑ i ∈ S m, i.1 * (ψ φ i.2).coeff m' =
      (MonoidAlgebra.single m (1 : K)).coeff m' := by
    intro m'
    rw [← hx m, hS m, map_sum, ← cf_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have : i.1 ⊗ₜ[k] i.2 = i.1 • ((1 : K) ⊗ₜ[k] i.2) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, ψ_apply, cf_apply, smul_eq_mul]
  have hR : ∀ m', ∑ i ∈ S m, cR i.1 * (ψR i.2).coeff m' =
      (MonoidAlgebra.single m (1 : R)).coeff m' := by
    intro m'
    apply Subtype.val_injective
    rw [← Subalgebra.coe_val]
    rw [map_sum]
    simp only [map_mul, Subalgebra.coe_val]
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [hcR i hi, hc], hK]
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> simp
  refine ⟨∑ i ∈ S m, ρ (cR i.1) • i.2, ?_⟩
  apply MonoidAlgebra.ext
  ext m'
  change (ψ0 _).coeff m' = _
  rw [map_sum, ← cf_apply, map_sum]
  have : ∑ i ∈ S m, cf k m' (ψ0 (ρ (cR i.1) • i.2)) =
      ρ (∑ i ∈ S m, cR i.1 * (ψR i.2).coeff m') := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, map_smul, map_mul]
    simp [ψ0, MonoidAlgebra.coeff_mapAlgHom]
  rw [this, hR]
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

end Descent

/-! ### Group algebras of lattices are generated by `t_i^{±1}` -/

theorem eq_top_of_single_mem {k : Type u} [CommRing k] {σ : Type u}
    (B : Subalgebra k (MonoidAlgebra k (Multiplicative (σ →₀ ℤ))))
    (h : ∀ i, MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : k) ∈ B)
    (h' : ∀ i,
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (-1 : ℤ))) (1 : k) ∈ B) :
    B = ⊤ := by
  have hmul : ∀ a b : σ →₀ ℤ, MonoidAlgebra.single (Multiplicative.ofAdd a) (1 : k) ∈ B →
      MonoidAlgebra.single (Multiplicative.ofAdd b) (1 : k) ∈ B →
      MonoidAlgebra.single (Multiplicative.ofAdd (a + b)) (1 : k) ∈ B := by
    intro a b ha hb
    have := B.mul_mem ha hb
    rwa [MonoidAlgebra.single_mul_single, ← ofAdd_add, mul_one] at this
  have h0 : MonoidAlgebra.single (Multiplicative.ofAdd (0 : σ →₀ ℤ)) (1 : k) ∈ B := by
    rw [ofAdd_zero, ← MonoidAlgebra.one_def]
    exact B.one_mem
  have hS : ∀ f : σ →₀ ℤ, MonoidAlgebra.single (Multiplicative.ofAdd f) (1 : k) ∈ B := by
    intro f
    refine Finsupp.induction f h0 ?_
    intro i n f _ hn0 hf
    clear hn0
    refine hmul _ _ ?_ hf
    induction n using Int.induction_on with
    | zero => simpa using h0
    | succ n hn => rw [Finsupp.single_add]; exact hmul _ _ hn (h i)
    | pred n hn => rw [sub_eq_add_neg, Finsupp.single_add]; exact hmul _ _ hn (h' i)
  rw [eq_top_iff]
  rintro x -
  refine MonoidAlgebra.induction_on x (fun m ↦ ?_) (fun x y hx hy ↦ B.add_mem hx hy)
    (fun r x hx ↦ B.smul_mem hx r)
  rw [MonoidAlgebra.of_apply]
  exact hS (Multiplicative.toAdd m)

/-! ### Main theorem -/

/-- **Torus specialization.** For algebraically closed fields `k ⊆ K` and a finite-type
commutative Hopf `k`-algebra `Q`, absence of nontrivial tori ascends from `Q` to `K ⊗[k] Q`. -/
theorem noNontrivialTorus_baseChange {k K Q : Type u} [Field k] [IsAlgClosed k] [Field K]
    [IsAlgClosed K] [Algebra k K] [CommRing Q] [HopfAlgebra k Q] [Algebra.FiniteType k Q]
    (h : NoNontrivialTorus k Q) : NoNontrivialTorus K (K ⊗[k] Q) := by
  intro J hJ g hg
  by_contra hne
  obtain ⟨n, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff _ _).1
    (torusCommHopfAlgProperty.split K _ hJ)
  let σ := ULift.{u} (Fin n)
  let M := Multiplicative (σ →₀ ℤ)
  let E := CommHopfAlgCat.ofIso
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} K) (CommHopfAlgCat.{u} K)).mapIso e)
  let φ : K ⊗[k] Q →ₐc[K] MonoidAlgebra K M := e.inv.hom.hom.comp (qMk J)
  have hφs : Function.Surjective φ := fun y ↦ by
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := J.toIdeal) (E y)
    refine ⟨x, ?_⟩
    change E.symm (Ideal.Quotient.mk J.toIdeal x) = y
    rw [hx, E.symm_apply_apply]
  let g' : (K ⊗[k] Q ⧸ J.toIdeal) →ₐ[K] K := Ideal.Quotient.liftₐ J.toIdeal g.ofConv hg
  let gb : MonoidAlgebra K M →ₐ[K] K := g'.comp (e.hom.hom.hom : _ →ₐ[K] _)
  have hgb : ∀ x, g.ofConv x = gb (φ x) := fun x ↦ by
    change _ = g' (E (E.symm (Ideal.Quotient.mk J.toIdeal x)))
    rw [E.apply_symm_apply]
    rfl
  obtain ⟨i₀⟩ : Nonempty σ := by
    by_contra hσ
    rw [not_nonempty_iff] at hσ
    apply hne
    have hM : ∀ m : M, m = 1 := fun m ↦
      Multiplicative.toAdd.injective (Subsingleton.elim _ _)
    have hgb1 : gb = Bialgebra.counitAlgHom K (MonoidAlgebra K M) :=
      MonoidAlgebra.algHom_ext (fun m ↦ by rw [hM m, ← MonoidAlgebra.one_def, map_one, map_one])
        (Subsingleton.elim _ _)
    apply WithConv.ofConv_injective
    rw [AlgHom.convOne_def]
    refine AlgHom.ext fun x ↦ ?_
    rw [hgb, hgb1]
    simp [φ]
  let Gs : Finset M := Finset.univ.image (fun i ↦ Multiplicative.ofAdd (Finsupp.single i 1)) ∪
    Finset.univ.image (fun i ↦ Multiplicative.ofAdd (Finsupp.single i (-1)))
  obtain ⟨ψ₀, hψ₀⟩ := descent φ hφs Gs
  have hsurj : Function.Surjective ψ₀ := by
    have htop : (ψ₀ : Q →ₐ[k] MonoidAlgebra k M).range = ⊤ :=
      eq_top_of_single_mem _ (fun i ↦ hψ₀ _ (by simp [Gs])) (fun i ↦ hψ₀ _ (by simp [Gs]))
    intro y
    have hy : y ∈ (ψ₀ : Q →ₐ[k] MonoidAlgebra k M).range := htop ▸ Algebra.mem_top
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, hq⟩
  let J₀ := HopfIdeal.kerOfSurjective ψ₀ hsurj
  have hT : torusCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k Q) J₀) := by
    apply splitTorusCommHopfAlgProperty.torus
    rw [splitTorusCommHopfAlgProperty_iff]
    exact ⟨n, ⟨(ObjectProperty.isoMk _ (CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
      (CommHopfAlgCat.ofHom ψ₀) hsurj)).symm⟩⟩
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := fun h0 ↦ ha (by simp [h0])
  have ha1 : a ≠ 1 := fun h1 ↦ ha (by simp [h1])
  let u : kˣ := Units.mk0 a ha0
  let deg : (σ →₀ ℤ) →+ ℤ := Finsupp.liftAddHom (α := σ) fun _ ↦ AddMonoidHom.id ℤ
  let χ : M →* k := (Units.coeHom k).comp
    ((zpowersHom kˣ u).comp (AddMonoidHom.toMultiplicative deg))
  let g₀ : WithConv (Q →ₐ[k] k) :=
    WithConv.toConv ((MonoidAlgebra.lift k k M χ).comp (ψ₀ : Q →ₐ[k] MonoidAlgebra k M))
  have h1 := h J₀ hT g₀ (fun y hy ↦ by
    have hy' : ψ₀ y = 0 := (HopfIdeal.mem_kerOfSurjective ψ₀ hsurj).1 hy
    simp [g₀, hy'])
  obtain ⟨q, hq⟩ := hsurj (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i₀ 1)) 1)
  have hcq : Coalgebra.counit (R := k) q = 1 := by
    rw [← CoalgHomClass.counit_comp_apply ψ₀, hq, MonoidAlgebra.counit_single]
    simp
  have h2 := congrArg (fun g : WithConv (Q →ₐ[k] k) ↦ g.ofConv q) h1
  simp only [g₀, AlgHom.convOne_def] at h2
  simp [hq, hcq, χ, deg, u] at h2
  change a ^ (Finsupp.liftAddHom (α := σ) (fun _ ↦ AddMonoidHom.id ℤ)
    (Finsupp.single i₀ 1)) = 1 at h2
  rw [Finsupp.liftAddHom_apply_single] at h2
  exact ha1 (by simpa using h2)

end

end AlgMag.Reductive.TorusSpecialization
