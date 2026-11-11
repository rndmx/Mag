/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.TangentRoots
import AlgMag.Reductive.LieAttractor
import AlgMag.Sec16Lie

/-!
# Root groups by magnets (Definition `def:root-group`, Proposition `prop:root-groups`)

`G = Spec H` an affine group over a field `k`, with the conjugation action of `T = D(X)`
(`π : H → k[X]`), `H_χ` the weight spaces (`torusGrading π χ`), `Φ = roots π`.

* `IsRootGroup π α I` (Conrad, *Reductive group schemes*, Def. 4.1.1, as specified by the author):
  the closed subgroup `Spec (H/I)` is `T`-stable (`I` homogeneous), `Lie(U) = 𝔤_α`
  (tangent vectors at `e` vanishing on every `H_χ`, `χ ≠ α`), and `U ≅ 𝔾_a`, `T`-equivariantly
  through `α`: `H/I = k[x]` with `x` primitive and the class of an element of `H_α`.
* `rootGroupIdeal π α`: `U_α = G^{[α⟩}_e`, the attractor of the magnet `[α⟩ = ℕα` with prescribed
  limit `e` for the face `0`. Its points are the `g ∈ G^{[α⟩}(A)` with `lim g = 1`, where
  `lim g = g ∘ (H → H_0)` is the limit map `G^{[α⟩} → G^0` (`limitHom`).
* `attractor_semidirect_rootGroup`: `G^{[α⟩}(A) ≃ U_α(A) ⋊ G^0(A)` (Prop. 16.6 for `[α⟩`, face `0`).
* `isHomogeneous_rootGroupIdeal`, `mem_lieSubalgebra_rootGroupIdeal_iff`: `U_α` is `T`-stable
  and `Lie(U_α) = 𝔤_α`, with no hypothesis beyond: `α` of infinite order and `nα ∉ Φ`
  for `n ≥ 2` (reducedness).
* `isRootGroup_rootGroupIdeal`: `IsRootGroup` for `U_α`, the `𝔾_a`-coordinate being the one
  remaining hypothesis.
-/

suppress_compilation

open Magnetism TauCeti WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-! ### The constant coefficient on `A ⊗ k[N]` -/

section ConstCoeff

variable {A : Type u} [CommRing A] [Algebra k A]

variable (A) in
/-- The coefficient of `t^0` on `A ⊗ k[X]`. -/
def constCoeff : A ⊗[k] MonoidAlgebra k X →ₗ[k] A :=
  LinearMap.tensorComponent (Comodule.monoidCoeff k X 1)

lemma constCoeff_tmul_single (a : A) (χ : Additive X) :
    constCoeff A (a ⊗ₜ[k] MonoidAlgebra.single (Additive.toMul χ) (1 : k)) =
      if χ = 0 then a else 0 := by
  rw [constCoeff, LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply,
    MonoidAlgebra.coeff_single_apply]
  by_cases h : χ = 0
  · subst h; simp
  · have : Additive.toMul χ ≠ 1 := fun e => h (by simpa using congrArg Additive.ofMul e)
    simp [h, this]

/-- For a pointed magnet (`a + b = 0` in `N` forces `a = 0`), the constant coefficient is
multiplicative on `A ⊗ k[N]`. -/
lemma constCoeff_mul {N : Magnet (Additive X)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0)
    {x y : A ⊗[k] MonoidAlgebra k X} (hx : x ∈ magnetSubalgebra (R := k) A N)
    (hy : y ∈ magnetSubalgebra (R := k) A N) :
    constCoeff A (x * y) = constCoeff A x * constCoeff A y := by
  change x ∈ Submodule.span k _ at hx
  change y ∈ Submodule.span k _ at hy
  induction hx using Submodule.span_induction with
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul, map_add, ha, hb, map_add, add_mul]
  | smul r a _ ha => rw [smul_mul_assoc, map_smul, ha, map_smul, smul_mul_assoc]
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add, map_add, ha, hb, map_add, mul_add]
    | smul r a _ ha => rw [mul_smul_comm, map_smul, ha, map_smul, mul_smul_comm]
    | mem y hy =>
      obtain ⟨a, χ, hχ, rfl⟩ := hx
      obtain ⟨b, χ', hχ', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, MonoidAlgebra.single_mul_single, mul_one,
        ← toMul_add, constCoeff_tmul_single, constCoeff_tmul_single, constCoeff_tmul_single]
      by_cases h : χ + χ' = 0
      · have h1 := hN χ hχ χ' hχ' h
        have h2 : χ' = 0 := by rw [h1, zero_add] at h; exact h
        simp [h, h1, h2]
      · by_cases h1 : χ = 0
        · have h2 : χ' ≠ 0 := by rintro rfl; exact h (by rw [h1, add_zero])
          simp [h, h2]
        · simp [h, h1]

end ConstCoeff

/-! ### The orbit map on homogeneous elements -/

variable {π}

lemma orbitHom_apply_of_mem {A : Type u} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    (orbitHom π A g).ofConv h = g.ofConv h ⊗ₜ[k] MonoidAlgebra.single (Additive.toMul χ) 1 := by
  rw [orbitHom_apply, torusCoactLeft_of_mem hh, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

lemma constCoeff_orbitHom_of_mem {A : Type u} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    constCoeff A ((orbitHom π A g).ofConv h) = if χ = 0 then g.ofConv h else 0 := by
  rw [orbitHom_apply_of_mem g hh, constCoeff_tmul_single]

/-- Induction over the weight decomposition `H = ⊕ H_χ`. -/
lemma induction_torusGrading {p : H → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hmem : ∀ χ, ∀ x ∈ torusGrading π χ, p x) (h : H) : p h := by
  have htop := (isInternal_torusGrading π).submodule_iSup_eq_top
  have : h ∈ ⨆ χ, torusGrading π χ := htop ▸ Submodule.mem_top
  exact Submodule.iSup_induction (torusGrading π) (motive := p) this hmem h0 hadd

/-- The counit vanishes on `H_χ` for `χ ≠ 0` (the unit is a `T`-fixed point). -/
lemma counit_eq_zero_of_mem {χ : Additive X} (hχ : χ ≠ 0) {h : H}
    (hh : h ∈ torusGrading π χ) : Coalgebra.counit (R := k) h = 0 := by
  have h1 : (1 : WithConv (H →ₐ[k] k)) ∈ attractorSubgroup π ⊥ k := Subgroup.one_mem _
  rw [mem_attractorSubgroup π] at h1
  have h2 := h1 (mem_magnetIdeal_of_notMem (N := (⊥ : Magnet (Additive X)))
    (by rwa [AddSubmonoid.mem_bot]) hh)
  rw [RingHom.mem_ker, AlgHom.convOne_apply] at h2
  simpa using h2

/-! ### The limit map `G^N → G^0` -/

section Limit

variable {N : Magnet (Additive X)} (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0)
variable (π) (A : Type u) [CommRing A] [Algebra k A]

/-- The limit of a point of `G^N` (pointed `N`): `lim g = g ∘ (H → H_0)`, as an algebra map. -/
def limitPoint (g : attractorSubgroup π N A) : WithConv (H →ₐ[k] A) :=
  toConv (AlgHom.ofLinearMap (constCoeff A ∘ₗ (orbitHom π A g.1).ofConv.toLinearMap)
    (by simp [Algebra.TensorProduct.one_def, constCoeff, MonoidAlgebra.one_def])
    (fun x y => by
      have hg := (mem_subalgebraPoints.1 g.2)
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
      exact constCoeff_mul hN (hg x) (hg y)))

lemma limitPoint_apply (g : attractorSubgroup π N A) (h : H) :
    (limitPoint π hN A g).ofConv h = constCoeff A ((orbitHom π A g.1).ofConv h) := rfl

/-- The limit map `G^N(A) → G(A)` is a group homomorphism. -/
def limitHom : attractorSubgroup π N A →* WithConv (H →ₐ[k] A) where
  toFun := limitPoint π hN A
  map_one' := by
    ext h
    rw [limitPoint_apply]
    change constCoeff A ((orbitHom π A 1).ofConv h) = _
    rw [map_one, AlgHom.convOne_apply, AlgHom.convOne_apply, Algebra.algebraMap_eq_smul_one,
      map_smul, Algebra.TensorProduct.one_def, constCoeff, LinearMap.tensorComponent_tmul,
      Comodule.monoidCoeff_apply, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single_apply,
      if_pos rfl, one_smul, Algebra.algebraMap_eq_smul_one]
  map_mul' g g' := by
    ext h
    rw [limitPoint_apply]
    change constCoeff A ((orbitHom π A (g.1 * g'.1)).ofConv h) = _
    rw [map_mul, AlgHom.convMul_apply, AlgHom.convMul_apply]
    have hg := mem_subalgebraPoints.1 g.2
    have hg' := mem_subalgebraPoints.1 g'.2
    induction Coalgebra.comul (R := k) h using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
        constCoeff_mul hN (hg a) (hg' b)]
      rfl

lemma limitHom_apply (g : attractorSubgroup π N A) (h : H) :
    (limitHom π hN A g).ofConv h = constCoeff A ((orbitHom π A g.1).ofConv h) := rfl

/-- `lim g` lies in `G^0`. -/
lemma limitHom_mem (g : attractorSubgroup π N A) :
    limitHom π hN A g ∈ attractorSubgroup π ⊥ A := by
  rw [mem_attractorSubgroup, magnetIdeal, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro χ hχ x hx
  rw [SetLike.mem_coe, RingHom.mem_ker, limitHom_apply, constCoeff_orbitHom_of_mem _ hx,
    if_neg (by rwa [AddSubmonoid.mem_bot] at hχ)]

/-- `lim g = 1` iff `g = ε` on `H_0`. -/
lemma limitHom_eq_one_iff (g : attractorSubgroup π N A) :
    limitHom π hN A g = 1 ↔ ∀ x ∈ torusGrading π 0,
      g.1.ofConv x = algebraMap k A (Coalgebra.counit (R := k) x) := by
  constructor
  · intro h1 x hx
    have := congrArg (fun F : WithConv (H →ₐ[k] A) => F.ofConv x) h1
    simp only [limitHom_apply, constCoeff_orbitHom_of_mem _ hx, if_pos rfl,
      AlgHom.convOne_apply] at this
    exact this
  · intro h1
    ext h
    induction h using induction_torusGrading (π := π) with
    | h0 => simp
    | hadd x y hx hy => rw [map_add, map_add, hx, hy]
    | hmem χ x hx =>
      rw [limitHom_apply, constCoeff_orbitHom_of_mem _ hx, AlgHom.convOne_apply]
      by_cases hχ : χ = 0
      · subst hχ; rw [if_pos rfl, h1 x hx]
      · rw [if_neg hχ, counit_eq_zero_of_mem hχ hx, map_zero]

/-- On `G^0 ⊆ G^N`, the limit is the identity. -/
lemma limitHom_of_mem_bot (g : attractorSubgroup π N A) (hg : g.1 ∈ attractorSubgroup π ⊥ A) :
    limitHom π hN A g = g.1 := by
  rw [mem_attractorSubgroup π] at hg
  ext h
  induction h using induction_torusGrading (π := π) with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hmem χ x hx =>
    rw [limitHom_apply, constCoeff_orbitHom_of_mem _ hx]
    by_cases hχ : χ = 0
    · rw [if_pos hχ]
    · rw [if_neg hχ]
      exact (hg (mem_magnetIdeal_of_notMem (by rwa [AddSubmonoid.mem_bot]) hx)).symm

/-- `G^0 ⊆ G^N`. -/
lemma attractorSubgroup_bot_le : attractorSubgroup π ⊥ A ≤ attractorSubgroup π N A := by
  intro g hg
  rw [mem_attractorSubgroup π] at hg ⊢
  refine le_trans (Ideal.span_mono ?_) hg
  simp only [Set.iUnion_subset_iff]
  intro χ hχ x hx
  have hχ0 : χ ∉ (⊥ : Magnet (Additive X)) := by
    rw [AddSubmonoid.mem_bot]; rintro rfl; exact hχ N.zero_mem
  exact Set.mem_iUnion₂.2 ⟨χ, hχ0, hx⟩

/-- The limit `G^N(A) → G^0(A)`. -/
def limitToBot : attractorSubgroup π N A →* attractorSubgroup π ⊥ A :=
  (limitHom π hN A).codRestrict _ (limitHom_mem π hN A)

/-- The inclusion `G^0(A) → G^N(A)`. -/
def botToAttractor : attractorSubgroup π ⊥ A →* attractorSubgroup π N A :=
  Subgroup.inclusion (attractorSubgroup_bot_le π A)

lemma limitToBot_botToAttractor (b : attractorSubgroup π ⊥ A) :
    limitToBot π hN A (botToAttractor π A b) = b :=
  Subtype.ext (limitHom_of_mem_bot π hN A _ b.2)

/-- **Proposition 16.6 (pointed magnet `N`, face `0`).** `G^N(A) ≃ G^N_e(A) ⋊ G^0(A)`, where
`G^N_e(A) = ker(lim)`. -/
def attractorSemidirect :
    attractorSubgroup π N A ≃*
      (limitToBot π hN A).ker ⋊[(MulAut.conjNormal (H := (limitToBot π hN A).ker)).comp
        (botToAttractor π A)] attractorSubgroup π ⊥ A :=
  semidirectOfSection _ _ (limitToBot_botToAttractor π hN A)

/-- `G^N_e(A)`: the points of `G^N` with limit `e`, a subgroup of `G(A)`. -/
def prescribedUnitSubgroup : Subgroup (WithConv (H →ₐ[k] A)) :=
  (limitToBot π hN A).ker.map (attractorSubgroup π N A).subtype

lemma mem_prescribedUnitSubgroup {g : WithConv (H →ₐ[k] A)} :
    g ∈ prescribedUnitSubgroup π hN A ↔ ∃ hg : g ∈ attractorSubgroup π N A,
      limitHom π hN A ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, congrArg Subtype.val (MonoidHom.mem_ker.1 hg')⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 (Subtype.ext h1), rfl⟩

/-- The kernel of `lim` is `G^N_e(A)`. -/
lemma ker_limitToBot_eq :
    ((limitToBot π hN A).ker.map (attractorSubgroup π N A).subtype) = prescribedUnitSubgroup π hN A :=
  rfl

end Limit

/-! ### The ideal of `G^N_e` -/

variable (π) in
/-- The equations of `G^N_e`: those of `G^N`, and `x = ε(x)` for `x ∈ H_0`. -/
def prescribedUnitIdeal (N : Magnet (Additive X)) : Ideal H :=
  magnetIdeal (torusGrading π) N ⊔
    Ideal.span {y | ∃ x ∈ torusGrading π 0, x - algebraMap k H (Coalgebra.counit (R := k) x) = y}

lemma prescribedUnitIdeal_le_ker_iff {N : Magnet (Additive X)}
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0) {A : Type u} [CommRing A] [Algebra k A]
    (g : WithConv (H →ₐ[k] A)) :
    prescribedUnitIdeal π N ≤ RingHom.ker g.ofConv ↔ g ∈ prescribedUnitSubgroup π hN A := by
  rw [mem_prescribedUnitSubgroup, prescribedUnitIdeal, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨hg, h0⟩
    have hg' : g ∈ attractorSubgroup π N A := (mem_attractorSubgroup π).2 hg
    refine ⟨hg', (limitHom_eq_one_iff π hN A ⟨g, hg'⟩).2 fun x hx => ?_⟩
    have := h0 ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this
  · rintro ⟨hg, h1⟩
    refine ⟨(mem_attractorSubgroup π).1 hg, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
    exact (limitHom_eq_one_iff π hN A ⟨g, hg⟩).1 h1 x hx

variable (π)

/-- **`G^N_e` as a closed subgroup** (pointed magnet `N`). -/
def prescribedUnitHopfIdeal (N : Magnet (Additive X))
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0) : HopfIdeal k H :=
  HopfIdeal.ofIdealOfPointsSubgroup (prescribedUnitIdeal π N)
    (fun A => prescribedUnitSubgroup π hN A)
    (fun _ g => (prescribedUnitIdeal_le_ker_iff hN g).symm)

lemma prescribedUnitHopfIdeal_toIdeal (N : Magnet (Additive X))
    (hN : ∀ a ∈ N, ∀ b ∈ N, a + b = 0 → a = 0) :
    (prescribedUnitHopfIdeal π N hN).toIdeal = prescribedUnitIdeal π N := by
  rw [prescribedUnitHopfIdeal, HopfIdeal.ofIdealOfPointsSubgroup_toIdeal]

/-! ### Root groups -/

/-- The magnet `[α⟩ = ℕα`. -/
def rayMagnet (α : Additive X) : Magnet (Additive X) := AddSubmonoid.closure {α}

lemma rayMagnet_pointed {α : Additive X} (hα : ∀ n : ℕ, n • α = 0 → n = 0) :
    ∀ a ∈ rayMagnet α, ∀ b ∈ rayMagnet α, a + b = 0 → a = 0 := by
  intro a ha b hb hab
  obtain ⟨m, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 ha
  obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hb
  rw [← add_smul] at hab
  have := hα _ hab
  have hm : m = 0 := by omega
  simp [hm]

/-- **`U_α = G^{[α⟩}_e`**, the attractor of `[α⟩` with prescribed limit `e` (face `0`). -/
def rootGroupIdeal (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0) : HopfIdeal k H :=
  prescribedUnitHopfIdeal π (rayMagnet α) (rayMagnet_pointed hα)

/-- **Definition `def:root-group`** (Conrad, Def. 4.1.1). A closed subgroup `U = Spec (H/I)` is a
root group for `α` if it is `T`-stable, `Lie(U) = 𝔤_α`, and `U ≅ 𝔾_a` `T`-equivariantly through
`α`: `H/I = k[x]` with `x` primitive and the class of an element of `H_α`. -/
structure IsRootGroup [Module.Finite k (Bialgebra.CotangentSpace k H)] (α : Additive X)
    (I : HopfIdeal k H) : Prop where
  stable : I.toIdeal.IsHomogeneous (torusGrading π)
  lie : ∀ d : Derivation k H (Bialgebra.CounitAlgebra k H k),
    d ∈ I.lieSubalgebra (B := k) ↔ ∀ χ ≠ α, ∀ h ∈ torusGrading π χ, d h = 0
  ga : ∃ y ∈ torusGrading π α,
    Function.Bijective (Polynomial.aeval (R := k) (Ideal.Quotient.mk I.toIdeal y)) ∧
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I.toIdeal) (Ideal.Quotient.mkₐ k I.toIdeal)
        (Coalgebra.comul (R := k) y) =
      Ideal.Quotient.mk I.toIdeal y ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Ideal.Quotient.mk I.toIdeal y

variable {π}

/-- `U_α` is `T`-stable. -/
theorem isHomogeneous_rootGroupIdeal (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0) :
    (rootGroupIdeal π α hα).toIdeal.IsHomogeneous (torusGrading π) := by
  rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal,
    ← Ideal.span_union]
  refine Ideal.homogeneous_span _ _ ?_
  rintro x (hx | ⟨x, hx, rfl⟩)
  · obtain ⟨χ, -, hx⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨χ, hx⟩
  · refine ⟨0, Submodule.sub_mem _ hx ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- **`Lie(U_α) = 𝔤_α`.** -/
theorem mem_lieSubalgebra_rootGroupIdeal_iff (α : Additive X)
    (hα : ∀ n : ℕ, n • α = 0 → n = 0) (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (rootGroupIdeal π α hα).lieSubalgebra (B := k) ↔
      ∀ χ ≠ α, ∀ h ∈ torusGrading π χ, d h = 0 := by
  have hspan : (rootGroupIdeal π α hα).toIdeal = Ideal.span
      ((⋃ (m : Additive X) (_ : m ∉ rayMagnet α), (torusGrading π m : Set H)) ∪
        {y | ∃ x ∈ torusGrading π 0, x - algebraMap k H (Coalgebra.counit (R := k) x) = y}) := by
    rw [rootGroupIdeal, prescribedUnitHopfIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal,
      Ideal.span_union]
  have hα0 : α ≠ 0 := fun h => by simpa using hα 1 (by simp [h])
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan]
  constructor
  · intro hd χ hχ h hh
    by_cases hN : χ ∈ rayMagnet α
    · by_cases h0 : χ = 0
      · subst h0
        have := hd _ (Or.inr ⟨h, hh, rfl⟩)
        simpa only [map_sub, d.map_algebraMap, sub_zero] using this
      · obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.1 hN
        by_contra hne
        have hW : n • α ∈ tangentWeights π k := ⟨d, h, hh, hne⟩
        have hn0 : n ≠ 0 := by rintro rfl; exact h0 (zero_smul _ _)
        have hn1 : n ≠ 1 := by rintro rfl; exact hχ (one_smul _ _)
        rcases tangentWeights_subset_insert_roots hW with h' | h'
        · exact h0 h'
        · exact hred n (by omega) h'
    · exact hd h (Or.inl (Set.mem_iUnion₂.2 ⟨χ, hN, hh⟩))
  · intro hd x hx
    rcases hx with hx | ⟨x, hx, rfl⟩
    · obtain ⟨χ, hχ, hx⟩ := Set.mem_iUnion₂.1 hx
      exact hd χ (fun h => hχ (h ▸ AddSubmonoid.subset_closure rfl)) x hx
    · simpa only [map_sub, d.map_algebraMap, sub_zero] using hd 0 (Ne.symm hα0) x hx

/-- **Proposition `prop:root-groups`, existence by magnets.** `U_α = G^{[α⟩}_e` is a root group
for `α`, given its `𝔾_a`-coordinate (`hGa`). -/
theorem isRootGroup_rootGroupIdeal (α : Additive X)
    (hα : ∀ n : ℕ, n • α = 0 → n = 0) (hred : ∀ n : ℕ, 2 ≤ n → n • α ∉ roots π)
    (hGa : ∃ y ∈ torusGrading π α,
      Function.Bijective (Polynomial.aeval (R := k)
        (Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal y)) ∧
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (rootGroupIdeal π α hα).toIdeal)
          (Ideal.Quotient.mkₐ k (rootGroupIdeal π α hα).toIdeal) (Coalgebra.comul (R := k) y) =
        Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal y ⊗ₜ[k] 1 +
          1 ⊗ₜ[k] Ideal.Quotient.mk (rootGroupIdeal π α hα).toIdeal y) :
    IsRootGroup π α (rootGroupIdeal π α hα) where
  stable := isHomogeneous_rootGroupIdeal α hα
  lie := mem_lieSubalgebra_rootGroupIdeal_iff α hα hred
  ga := hGa

/-- **Proposition `prop:root-groups`, `G^{[α⟩} = T ⋉ U_α` on points**: `G^{[α⟩}(A)` is the
semidirect product of `U_α(A) = ker(lim)` and `G^0(A)` (`= Z_G(T)(A)`, which is `T(A)` for `G`
reductive). -/
def attractor_semidirect_rootGroup (α : Additive X) (hα : ∀ n : ℕ, n • α = 0 → n = 0)
    (A : Type u) [CommRing A] [Algebra k A] :
    attractorSubgroup π (rayMagnet α) A ≃*
      (limitToBot π (rayMagnet_pointed hα) A).ker ⋊[(MulAut.conjNormal
        (H := (limitToBot π (rayMagnet_pointed hα) A).ker)).comp (botToAttractor π A)]
        attractorSubgroup π ⊥ A :=
  attractorSemidirect π (rayMagnet_pointed hα) A

/-! ### The comultiplication respects the weight grading -/

variable (π) in
/-- `⊕_{a+b=χ} H_a ⊗ H_b ⊆ H ⊗ H`. -/
def tensorGrading (χ : Additive X) : Submodule k (H ⊗[k] H) :=
  Submodule.span k {t | ∃ a b : Additive X, a + b = χ ∧
    ∃ x ∈ torusGrading π a, ∃ y ∈ torusGrading π b, t = x ⊗ₜ[k] y}

/-- **`Δ(H_χ) ⊆ ⊕_{a+b=χ} H_a ⊗ H_b`**: the comultiplication is `T`-equivariant for the
conjugation action. Proof: the orbit map `G(A) → G(A ⊗ k[X])` is a group homomorphism; apply it
to the two universal points of `G(H ⊗ H)` and take the coefficient of `t^χ`. -/
theorem comul_mem_tensorGrading {χ : Additive X} {h : H} (hh : h ∈ torusGrading π χ) :
    Coalgebra.comul (R := k) h ∈ tensorGrading π χ := by
  classical
  let g : WithConv (H →ₐ[k] H ⊗[k] H) := toConv Algebra.TensorProduct.includeLeft
  let g' : WithConv (H →ₐ[k] H ⊗[k] H) := toConv Algebra.TensorProduct.includeRight
  let c : (H ⊗[k] H) ⊗[k] MonoidAlgebra k X →ₗ[k] H ⊗[k] H :=
    LinearMap.tensorComponent (Comodule.monoidCoeff k X (Additive.toMul χ))
  have hgg : (g * g').ofConv h = Coalgebra.comul (R := k) h := by
    rw [AlgHom.convMul_apply]
    induction Coalgebra.comul (R := k) h using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, ha, hb]
    | tmul a b =>
      rw [Algebra.TensorProduct.lift_tmul]
      simp [g, g', Algebra.TensorProduct.tmul_mul_tmul]
  have hL : c ((orbitHom π _ (g * g')).ofConv h) = Coalgebra.comul (R := k) h := by
    rw [orbitHom_apply_of_mem _ hh, hgg]
    simp [c, LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply]
  rw [← hL, map_mul, AlgHom.convMul_apply]
  induction Coalgebra.comul (R := k) h using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul]
    induction a using induction_torusGrading (π := π) with
    | h0 => simp
    | hadd x y hx hy => rw [map_add, add_mul, map_add]; exact Submodule.add_mem _ hx hy
    | hmem i x hx =>
      induction b using induction_torusGrading (π := π) with
      | h0 => simp
      | hadd y z hy hz => rw [map_add, mul_add, map_add]; exact Submodule.add_mem _ hy hz
      | hmem j y hy =>
        rw [orbitHom_apply_of_mem _ hx, orbitHom_apply_of_mem _ hy,
          Algebra.TensorProduct.tmul_mul_tmul, MonoidAlgebra.single_mul_single, mul_one]
        simp only [c, g, g', LinearMap.tensorComponent_tmul, Comodule.monoidCoeff_apply,
          MonoidAlgebra.coeff_single_apply, ofConv_toConv,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        split_ifs with hij
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, j, ?_, x, hx, y, hy, rfl⟩)
          rw [← toMul_add] at hij
          exact Additive.toMul.injective hij
        · rw [zero_smul]; exact Submodule.zero_mem _

end AlgMag.Reductive
