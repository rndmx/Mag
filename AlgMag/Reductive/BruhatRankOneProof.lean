/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.BruhatRankOne
import TauCeti.AlgebraicGeometry.AugmentationPoint.ClosedPoints
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Basic
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Opposite
import AlgMag.Reductive.OpenCellPoints

/-!
# The rank-one Bruhat core: proof

Notation: `Ω = U(λ⁻)·Z(λ)·U(λ) ≅ Spec(V ⊗ L ⊗ U)` (`openCellIso`), with `V = k[U(λ⁻)]`,
`L = k[Z(λ)]`, `U = k[U(λ)]`, and `cellProj l : Spec(V ⊗ L ⊗ U) ⟶ Spec V` the first projection.
The puncture is on `V = k[U(λ⁻)]` (for `U(λ)` apply everything to `l.oppositeCocharacter`).

Chain of reductions (all proved, no sorry):
* `bruhatRankOneCore_of_openEq`: `BruhatOpenEq` (`ω⁻¹(n·Ω) = cellProj⁻¹(V ∖ {one})`) ⇒ core;
  `p` = first projection on `Ω ∩ n·Ω`, `s` = unit section `(id, 1, 1)`.
* `bruhatOpenEq_of_pointEq` (`k = k̄`, Jacobson): `BruhatPointEq` (scheme `k`-points) ⇒ open form.
* `bruhatPointEq_of_convEq`: `BruhatConvEq` (`φ∘ω ∈ n·Ω(k) ⇔ φ∘incl ≠ ε`) ⇒ `BruhatPointEq`.
* `bruhatConvEq_of_groupEq` + `cellPointsSurj`: `BruhatGroupEq` (`v p ∈ n U⁻(k) P(k) ⇔ v ≠ 1`)
  ⇒ `BruhatConvEq`, via `openCellMap_point` (`φ∘ω = v z u`) and the Levi decomposition.
* `bruhat_rankOne_group` (`T`-orbit argument) ⇒ `BruhatGroupEq`; inputs `inv_not_mem_cell`
  (`hn` from `n⁻¹ P(λ) n ⊆ P(λ⁻)`, `U(λ)(k) ≠ 1`) and `hne_of_irreducible` (`G` irreducible).
* **`bruhatRankOneCore_of_rankOne`**: the core from `k = k̄`, `G` irreducible, `hconj`, `hU`, and a
  subgroup `T ≤ P(λ)(k)` normalizing `U(λ⁻)(k)`, with `n⁻¹ T n ⊆ T`, transitive by conjugation on
  `U(λ⁻)(k) ∖ {1}`.
SL₂ check: `n·Ω = {c ≠ 0}`, `c(u⁻(x) t(a) u⁺(y)) = x a`, so `v z u ∈ n·Ω ⇔ x ≠ 0`.
-/

suppress_compilation

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Cocharacter WithConv

universe u

namespace AlgMag.Reductive

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable (l : H →ₐc[k] LaurentPolynomial k)

/-- `V = k[U(λ⁻)]`, the first factor of the open cell ring. -/
abbrev CellV : Type u := H ⧸ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal

/-- The inclusion `V → V ⊗ L ⊗ U`, `v ↦ v ⊗ 1 ⊗ 1`. -/
def cellIncl : CellV l →ₐ[k] OpenCellRing l :=
  Algebra.TensorProduct.includeLeft.comp Algebra.TensorProduct.includeLeft

/-- The retraction `V ⊗ L ⊗ U → V`, `v ⊗ z ⊗ u ↦ ε(z) ε(u) v` (unit section of `Z(λ) × U(λ)`). -/
def cellRetr : OpenCellRing l →ₐ[k] CellV l :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift (AlgHom.id k (CellV l))
      ((Algebra.ofId k (CellV l)).comp
        (Bialgebra.counitAlgHom k (H ⧸ (leviDefiningHopfIdeal l).toIdeal)))
      (fun _ _ => Commute.all _ _))
    ((Algebra.ofId k (CellV l)).comp
      (Bialgebra.counitAlgHom k (H ⧸ l.unipotentDefiningHopfIdeal.toIdeal)))
    (fun _ _ => Commute.all _ _)

lemma cellRetr_comp_cellIncl : (cellRetr l).comp (cellIncl l) = AlgHom.id k (CellV l) := by
  ext v
  simp [cellRetr, cellIncl]

/-- The first projection `Ω ≅ Spec(V ⊗ L ⊗ U) ⟶ Spec V`. -/
abbrev cellProj : Spec (CommRingCat.of (OpenCellRing l)) ⟶ Spec (CommRingCat.of (CellV l)) :=
  Spec.map (CommRingCat.ofHom (cellIncl l).toRingHom)

/-- The unit section `Spec V ⟶ Spec(V ⊗ L ⊗ U)`, `v ↦ (v, 1, 1)`. -/
abbrev cellSect : Spec (CommRingCat.of (CellV l)) ⟶ Spec (CommRingCat.of (OpenCellRing l)) :=
  Spec.map (CommRingCat.ofHom (cellRetr l).toRingHom)

lemma cellSect_cellProj : cellSect l ≫ cellProj l = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (cellRetr l).toRingHom.comp (cellIncl l).toRingHom = RingHom.id _ := by
    have h := congrArg AlgHom.toRingHom (cellRetr_comp_cellIncl l)
    exact h
  rw [this, CommRingCat.ofHom_id, Spec.map_id]

variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

/-- **Bruhat open identity** (the named rank-one input). Under the open cell
`ω : Spec(V ⊗ L ⊗ U) ≅ Ω`, the translate `n·Ω` pulls back to `(Spec V ∖ {one}) × Spec L × Spec U`.
On `k`-points: `v z u ∈ n·Ω ⇔ v ≠ 1`. True for `SL₂` (see the module docstring). -/
def BruhatOpenEq (n : WithConv (H →ₐ[k] k)) (one : Spec (CommRingCat.of (CellV l)))
    (closed : IsClosed ({one} : Set (Spec (CommRingCat.of (CellV l))))) : Prop :=
  openCellMor l ⁻¹ᵁ translateOpenCell l n = cellProj l ⁻¹ᵁ puncturedOpen one closed

/-- **The rank-one Bruhat core from the Bruhat open identity.** -/
theorem bruhatRankOneCore_of_openEq (n : WithConv (H →ₐ[k] k))
    (one : Spec (CommRingCat.of (CellV l)))
    (closed : IsClosed ({one} : Set (Spec (CommRingCat.of (CellV l)))))
    (h : BruhatOpenEq l n one closed) : BruhatRankOneCore l n one closed := by
  set W := openCellOpens l ⊓ translateOpenCell l n
  set P := puncturedOpen one closed
  -- `a : Ω ∩ nΩ ⟶ Spec(V ⊗ L ⊗ U)`, the open cell coordinates
  have h1 : Set.range W.ι ⊆ Set.range (openCellMor l) := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx => hx.1
  let a := IsOpenImmersion.lift (openCellMor l) W.ι h1
  have ha : a ≫ openCellMor l = W.ι := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range (a ≫ cellProj l) ⊆ Set.range P.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hax : (openCellMor l) (a x) = W.ι x := by rw [← Scheme.Hom.comp_apply, ha]
    have hx : a x ∈ openCellMor l ⁻¹ᵁ translateOpenCell l n := by
      show (openCellMor l) (a x) ∈ translateOpenCell l n
      rw [hax]
      exact ((Scheme.Opens.range_ι W).subset ⟨x, rfl⟩).2
    rw [h] at hx
    exact hx
  let p := IsOpenImmersion.lift P.ι (a ≫ cellProj l) h2
  have h3 : Set.range (P.ι ≫ cellSect l ≫ openCellMor l) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : (cellProj l) ((cellSect l) (P.ι z)) = P.ι z := by
      rw [← Scheme.Hom.comp_apply, cellSect_cellProj]; rfl
    have hzP : (cellSect l) (P.ι z) ∈ cellProj l ⁻¹ᵁ P := by
      show (cellProj l) ((cellSect l) (P.ι z)) ∈ P
      rw [hz]; exact (Scheme.Opens.range_ι P).subset ⟨z, rfl⟩
    rw [← h] at hzP
    refine ⟨⟨(cellSect l) (P.ι z), ?_⟩, ?_⟩
    · simp
    · simpa [Scheme.Hom.comp_apply] using hzP
  let s := IsOpenImmersion.lift W.ι (P.ι ≫ cellSect l ≫ openCellMor l) h3
  have hsa : s ≫ a = P.ι ≫ cellSect l := by
    rw [← cancel_mono (openCellMor l), Category.assoc, ha]
    simp [s]
  refine bruhatRankOneCore_of_section l n one closed p s ?_
  rw [← cancel_mono P.ι, Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp,
    ← Category.assoc, hsa, Category.assoc, cellSect_cellProj, Category.comp_id]

/-! ### From `k`-points to the open identity (Jacobson) -/

/-- Two opens of a Jacobson space with the same closed points are equal. -/
lemma eq_of_isOpen_of_closedPoints {Y : Type*} [TopologicalSpace Y] [JacobsonSpace Y]
    {A B : Set Y} (hA : IsOpen A) (hB : IsOpen B)
    (h : ∀ y ∈ closedPoints Y, y ∈ A ↔ y ∈ B) : A = B := by
  have hc : Aᶜ ∩ closedPoints Y = Bᶜ ∩ closedPoints Y := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨hy, hc⟩; exact ⟨fun hb => hy ((h y hc).2 hb), hc⟩
    · rintro ⟨hy, hc⟩; exact ⟨fun ha => hy ((h y hc).1 ha), hc⟩
  have := congrArg closure hc
  rw [closure_inter_closedPoints hA.isClosed_compl,
    closure_inter_closedPoints hB.isClosed_compl] at this
  exact compl_injective this

/-- **Rank-one Bruhat on `k`-points** (the named rank-one input, points form). For every
`k`-point `φ = (v, z, u)` of `U(λ⁻) × Z(λ) × U(λ)`: `ω(v, z, u) = v z u ∈ n·Ω ⇔ v ≠ one`.
For `one` the unit of `U(λ⁻)`: `v z u ∈ n·Ω ⇔ v ≠ 1`. True for `SL₂`
(`n·Ω = {c ≠ 0}`, `c(u⁻(x) t(a) u⁺(y)) = x a`). -/
def BruhatPointEq (n : WithConv (H →ₐ[k] k)) (one : Spec (CommRingCat.of (CellV l))) : Prop :=
  ∀ φ : OpenCellRing l →ₐ[k] k,
    (openCellMor l) (AlgHom.kernelPoint φ) ∈ translateOpenCell l n ↔
      (cellProj l) (AlgHom.kernelPoint φ) ≠ one

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma mem_puncturedOpen_iff {Y : Scheme.{u}} {one y : Y} {closed : IsClosed ({one} : Set Y)} :
    y ∈ puncturedOpen one closed ↔ y ≠ one := Iff.rfl

set_option maxHeartbeats 800000 in
/-- The `k`-points form implies the open identity (`k = k̄`; Jacobson + Nullstellensatz). -/
theorem bruhatOpenEq_of_pointEq [IsAlgClosed k] (n : WithConv (H →ₐ[k] k))
    (one : Spec (CommRingCat.of (CellV l)))
    (closed : IsClosed ({one} : Set (Spec (CommRingCat.of (CellV l)))))
    (h : BruhatPointEq l n one) : BruhatOpenEq l n one closed := by
  have : IsJacobsonRing (OpenCellRing l) := isJacobsonRing_of_finiteType (A := k)
  apply TopologicalSpace.Opens.ext
  refine eq_of_isOpen_of_closedPoints (TopologicalSpace.Opens.isOpen _)
    (TopologicalSpace.Opens.isOpen _) ?_
  intro y hy
  rw [← TauCeti.range_kernelPoint_eq_closedPoints (k := k)] at hy
  obtain ⟨φ, rfl⟩ := hy
  have e1 : AlgHom.kernelPoint φ ∈ openCellMor l ⁻¹ᵁ translateOpenCell l n ↔
      (openCellMor l) (AlgHom.kernelPoint φ) ∈ translateOpenCell l n := Scheme.Hom.mem_preimage _
  have e2 : AlgHom.kernelPoint φ ∈ cellProj l ⁻¹ᵁ puncturedOpen one closed ↔
      (cellProj l) (AlgHom.kernelPoint φ) ∈ puncturedOpen one closed := Scheme.Hom.mem_preimage _
  have e3 : (cellProj l) (AlgHom.kernelPoint φ) ∈ puncturedOpen one closed ↔
      (cellProj l) (AlgHom.kernelPoint φ) ≠ one := mem_puncturedOpen_iff
  rw [SetLike.mem_coe, SetLike.mem_coe]
  exact e1.trans ((h φ).trans (e3.symm.trans e2.symm))

/-- **The rank-one Bruhat core from the `k`-point statement.** -/
theorem bruhatRankOneCore_of_pointEq [IsAlgClosed k] (n : WithConv (H →ₐ[k] k))
    (one : Spec (CommRingCat.of (CellV l)))
    (closed : IsClosed ({one} : Set (Spec (CommRingCat.of (CellV l)))))
    (h : BruhatPointEq l n one) : BruhatRankOneCore l n one closed :=
  bruhatRankOneCore_of_openEq l n one closed (bruhatOpenEq_of_pointEq l n one closed h)

/-! ### The `T`-orbit argument on `k`-points (abstract group form)

`Ω(k) = U⁻(k)·P(k)` with `P = Z(λ)U(λ)`. Then `n·Ω(k)` is right `P(k)`-stable, so `v z u ∈ n·Ω`
iff `v ∈ n·Ω`; and it is stable under conjugation by `T(k)` (`T ≤ P`, `n⁻¹Tn = T`, `T`
normalizes `U⁻`). If `T(k)` is transitive on `U⁻(k) ∖ {1}` (`U⁻ ≅ G_a` with a nontrivial weight,
`k = k̄`), `n⁻¹ ∉ Ω(k)` and `U⁻(k) ∩ n·Ω(k) ≠ ∅`, then `v p ∈ n·Ω(k) ⇔ v ≠ 1`. -/

/-- **Rank-one Bruhat on points, `T`-orbit form.** -/
theorem bruhat_rankOne_group {G : Type*} [Group G] (Um P T : Subgroup G) (n : G)
    (hTP : T ≤ P) (hTU : ∀ t ∈ T, ∀ v ∈ Um, t * v * t⁻¹ ∈ Um)
    (hnT : ∀ t ∈ T, n⁻¹ * t * n ∈ T)
    (hn : ∀ v ∈ Um, ∀ p ∈ P, n⁻¹ ≠ v * p)
    (htrans : ∀ v ∈ Um, ∀ w ∈ Um, v ≠ 1 → w ≠ 1 → ∃ t ∈ T, w = t * v * t⁻¹)
    (hne : ∃ v ∈ Um, ∃ v' ∈ Um, ∃ p' ∈ P, v = n * (v' * p'))
    {v : G} (hv : v ∈ Um) {p : G} (hp : p ∈ P) :
    (∃ v' ∈ Um, ∃ p' ∈ P, v * p = n * (v' * p')) ↔ v ≠ 1 := by
  have key : ∀ v' ∈ Um, ∀ p' ∈ P, ∀ q ∈ P, q ≠ n * (v' * p') := by
    intro v' hv' p' hp' q hq hEq
    apply hn v' hv' (p' * q⁻¹) (P.mul_mem hp' (P.inv_mem hq))
    have : n⁻¹ = n⁻¹ * q * q⁻¹ := by group
    rw [this, hEq]; group
  constructor
  · rintro ⟨v', hv', p', hp', hEq⟩ rfl
    exact key v' hv' p' hp' p hp (by simpa using hEq)
  · intro hv1
    obtain ⟨v₀, hv₀, v', hv', p', hp', h₀⟩ := hne
    have hv₀1 : v₀ ≠ 1 := by
      rintro rfl
      exact key v' hv' p' hp' 1 P.one_mem h₀
    obtain ⟨t, ht, rfl⟩ := htrans v₀ hv₀ v hv hv₀1 hv1
    set t' := n⁻¹ * t * n
    have ht' : t' ∈ T := hnT t ht
    refine ⟨t' * v' * t'⁻¹, hTU t' ht' v' hv', t' * p' * t⁻¹ * p,
      P.mul_mem (P.mul_mem (P.mul_mem (hTP ht') hp') (P.inv_mem (hTP ht))) hp, ?_⟩
    rw [h₀]
    simp only [t']
    group

/-! ### Generic plumbing for a `k`-point (group) form of `BruhatPointEq`

Kernel points under `Spec.map`, injectivity, lifting closed points through an open immersion, and
left translation on kernel points (`(translateIso g)(ker ψ) = ker (g * ψ)`). -/

section Plumbing

lemma spec_map_kernelPoint {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (φ : B →ₐ[k] k) :
    Spec.map (CommRingCat.ofHom f.toRingHom) (AlgHom.kernelPoint φ) =
      AlgHom.kernelPoint (φ.comp f) := by
  rw [Spec.map_apply, CommRingCat.hom_ofHom]
  exact AlgHom.comap_kernelPoint φ f

lemma kernelPoint_inj {A : Type u} [CommRing A] [Algebra k A] {φ ψ : A →ₐ[k] k}
    (h : AlgHom.kernelPoint φ = AlgHom.kernelPoint ψ) : φ = ψ := by
  have hk : RingHom.ker (φ : A →+* k) = RingHom.ker (ψ : A →+* k) := by
    rw [← AlgHom.kernelPoint_asIdeal, ← AlgHom.kernelPoint_asIdeal, h]
  ext a
  have h1 : a - algebraMap k A (φ a) ∈ RingHom.ker (φ : A →+* k) := by
    rw [RingHom.mem_ker]; simp
  rw [hk, RingHom.mem_ker] at h1
  have h2 : ψ a - φ a = 0 := by simpa using h1
  exact (sub_eq_zero.mp h2).symm

lemma exists_kernelPoint_of_mem_range [IsAlgClosed k] {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k B]
    (f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion f]
    (φ : A →ₐ[k] k) (h : ∃ y, f y = AlgHom.kernelPoint φ) :
    ∃ ψ : B →ₐ[k] k, f (AlgHom.kernelPoint ψ) = AlgHom.kernelPoint φ := by
  obtain ⟨y, hy⟩ := h
  have hc : IsClosed ({y} : Set (Spec (CommRingCat.of B))) := by
    have : ({y} : Set (Spec (CommRingCat.of B))) = f ⁻¹' {AlgHom.kernelPoint φ} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hy
      · intro hz; exact f.isOpenEmbedding.injective (hz.trans hy.symm)
    rw [this]
    exact (AlgHom.isClosed_singleton_kernelPoint φ).preimage f.continuous
  obtain ⟨ψ, hψ⟩ := PrimeSpectrum.exists_kernelPoint_eq_of_isClosed (k := k) y hc
  exact ⟨ψ, hψ ▸ hy⟩

end Plumbing

section Translate

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma mapValue_ofId_self_bru (g : WithConv (H →ₐ[k] k)) :
    AlgHom.mapValue (H := H) (Algebra.ofId k k) g = g := by
  apply WithConv.ofConv_injective
  ext x
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
  rfl

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma translateIso_kernelPoint (g : WithConv (H →ₐ[k] k)) (ψ : H →ₐ[k] k) :
    (translateIso g).hom (AlgHom.kernelPoint ψ) = AlgHom.kernelPoint (g * toConv ψ).ofConv := by
  have e : (translateIso g).hom = Spec.map (CommRingCat.ofHom
      (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom.toRingHom) := rfl
  rw [e, spec_map_kernelPoint]
  congr 1
  have := HopfAlgebra.toConv_comp_leftTranslationAlgEquiv g (toConv ψ)
  rw [mapValue_ofId_self_bru, ofConv_toConv] at this
  rw [← this, ofConv_toConv]

end Translate

/-! ### The convolution (group) form of `BruhatPointEq`

Note: in `openCellMor_kernelPoint` the annotations `(… : OpenCellRing l)` and `(H := OpenCellRing l)`
are needed: without them the element type is elaborated as the raw `Quot` of the tensor product and
instance search fails / `isDefEq` times out. -/

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- `ω` on kernel points. -/
lemma openCellMor_kernelPoint (χ : OpenCellRing l →ₐ[k] k) :
    (openCellMor l) (AlgHom.kernelPoint χ) = AlgHom.kernelPoint (χ.comp (openCellMap l)) := by
  apply PrimeSpectrum.ext
  rw [AlgHom.kernelPoint_asIdeal]
  ext a
  rw [RingHom.mem_ker]
  have key : a ∈ ((openCellMor l) (AlgHom.kernelPoint χ)).asIdeal ↔
      (openCellMap l a : OpenCellRing l) ∈ (AlgHom.kernelPoint (H := OpenCellRing l) χ).asIdeal :=
      Iff.rfl
  rw [key, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
  rfl

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
/-- `cellProj` on kernel points. -/
lemma cellProj_kernelPoint (φ : OpenCellRing l →ₐ[k] k) :
    (cellProj l) (AlgHom.kernelPoint φ) = AlgHom.kernelPoint (φ.comp (cellIncl l)) := by
  apply PrimeSpectrum.ext
  rw [AlgHom.kernelPoint_asIdeal]
  ext a
  rw [RingHom.mem_ker]
  have key : a ∈ ((cellProj l) (AlgHom.kernelPoint φ)).asIdeal ↔
      (cellIncl l a : OpenCellRing l) ∈ (AlgHom.kernelPoint (H := OpenCellRing l) φ).asIdeal :=
      Iff.rfl
  rw [key, AlgHom.kernelPoint_asIdeal, RingHom.mem_ker]
  rfl

omit [Algebra.FiniteType k H] [Algebra.Smooth k H] in
lemma translateOpenCellMor_kernelPoint (g : WithConv (H →ₐ[k] k))
    (χ : OpenCellRing l →ₐ[k] k) :
    (translateOpenCellMor l g) (AlgHom.kernelPoint χ) =
      AlgHom.kernelPoint (g * toConv (χ.comp (openCellMap l))).ofConv := by
  rw [Scheme.Hom.comp_apply, openCellMor_kernelPoint, translateIso_kernelPoint]

/-- **Rank-one Bruhat in `G(k)`** (named input, convolution form). For every `k`-point
`φ = (v, z, u)` of the open cell: `v z u ∈ n·Ω(k)` (`Ω(k)` = `k`-points of the open cell) iff
`v ≠ 1`. -/
def BruhatConvEq (n : WithConv (H →ₐ[k] k)) : Prop :=
  ∀ φ : OpenCellRing l →ₐ[k] k,
    (∃ χ : OpenCellRing l →ₐ[k] k,
        toConv (φ.comp (openCellMap l)) = n * toConv (χ.comp (openCellMap l))) ↔
      φ.comp (cellIncl l) ≠ Bialgebra.counitAlgHom k (CellV l)

theorem bruhatPointEq_of_convEq [IsAlgClosed k] (n : WithConv (H →ₐ[k] k))
    (h : BruhatConvEq l n) :
    BruhatPointEq l n (TauCeti.Bialgebra.augmentationPoint k (CellV l)) := by
  intro φ
  rw [openCellMor_kernelPoint,
    cellProj_kernelPoint]
  have hiff : AlgHom.kernelPoint (φ.comp (cellIncl l)) ≠
      TauCeti.Bialgebra.augmentationPoint k (CellV l) ↔
      φ.comp (cellIncl l) ≠ Bialgebra.counitAlgHom k (CellV l) :=
    ⟨fun hne he => hne (by rw [he]), fun hne he => hne (kernelPoint_inj he)⟩
  rw [hiff, ← h φ]
  constructor
  · intro hmem
    obtain ⟨χ, hχ⟩ := exists_kernelPoint_of_mem_range (k := k) (translateOpenCellMor l n) _
      (Scheme.Hom.mem_opensRange.1 hmem)
    rw [translateOpenCellMor_kernelPoint] at hχ
    refine ⟨χ, ?_⟩
    have := kernelPoint_inj hχ
    rw [← this, toConv_ofConv]
  · rintro ⟨χ, hχ⟩
    refine Scheme.Hom.mem_opensRange.2 ⟨AlgHom.kernelPoint χ, ?_⟩
    rw [translateOpenCellMor_kernelPoint, ← hχ, ofConv_toConv]

/-! ### Triples: `k`-points of the open cell as `v z u`, and the group form

`openCellMap_point`: `φ ∘ ω = v * z * u` with `v ∈ U(λ⁻)(k)`, `z ∈ Z(λ)(k) ⊆ P(λ)(k)`, `u ∈ U(λ)(k)`.
`bruhatConvEq_of_groupEq`: `BruhatGroupEq` (the conclusion of `bruhat_rankOne_group`) and
`CellPointsSurj` (`U⁻(k)P(k) ⊆ Ω(k)`) give `BruhatConvEq`. -/

section Triples

open BialgHom

/-- The `U(λ⁻)`-coordinate `v` of a `k`-point `φ = (v, z, u)` of the open cell, as a point of `G`. -/
def cellPt1 (φ : OpenCellRing l →ₐ[k] k) : WithConv (H →ₐ[k] k) :=
  toConv (((φ.comp Algebra.TensorProduct.includeLeft).comp Algebra.TensorProduct.includeLeft).comp
    (Ideal.Quotient.mkₐ k _))

/-- The `Z(λ)`-coordinate `z`. -/
def cellPt2 (φ : OpenCellRing l →ₐ[k] k) : WithConv (H →ₐ[k] k) :=
  toConv (((φ.comp Algebra.TensorProduct.includeLeft).comp Algebra.TensorProduct.includeRight).comp
    (Ideal.Quotient.mkₐ k _))

/-- The `U(λ)`-coordinate `u`. -/
def cellPt3 (φ : OpenCellRing l →ₐ[k] k) : WithConv (H →ₐ[k] k) :=
  toConv ((φ.comp Algebra.TensorProduct.includeRight).comp (Ideal.Quotient.mkₐ k _))

lemma cellMap_key (φ : OpenCellRing l →ₐ[k] k) :
    φ.comp (Algebra.TensorProduct.map
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ k _))
      (Ideal.Quotient.mkₐ k _)) =
    (Algebra.TensorProduct.lmul' k).comp (Algebra.TensorProduct.map
      ((Algebra.TensorProduct.lmul' k).comp
        (Algebra.TensorProduct.map (cellPt1 l φ).ofConv (cellPt2 l φ).ofConv))
      (cellPt3 l φ).ofConv) := by
  have h1 : φ 1 = 1 := φ.map_one
  ext a <;> simp [cellPt1, cellPt2, cellPt3, ← Algebra.TensorProduct.one_def] <;>
    first
    | (rw [h1, mul_one, mul_one])
    | (rw [h1, one_mul, mul_one])

/-- **Triples.** `φ ∘ ω = v * z * u` in `G(k)`. -/
theorem openCellMap_point (φ : OpenCellRing l →ₐ[k] k) :
    toConv (φ.comp (openCellMap l)) = cellPt1 l φ * cellPt2 l φ * cellPt3 l φ := by
  rw [AlgHom.convMul_def, AlgHom.convMul_def, ofConv_toConv]
  congr 1
  have e : φ.comp (openCellMap l) = (φ.comp (Algebra.TensorProduct.map
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ k _))
      (Ideal.Quotient.mkₐ k _))).comp ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom k H)
        (AlgHom.id k H)).comp (Bialgebra.comulAlgHom k H)) := rfl
  rw [e, cellMap_key]
  ext x
  simp only [AlgHom.comp_apply]
  congr 1
  rw [← AlgHom.comp_apply (Algebra.TensorProduct.map _ _)]
  congr 1
  ext y <;> simp

lemma cellPt1_mem (φ : OpenCellRing l →ₐ[k] k) :
    cellPt1 l φ ∈ unipotent k l.oppositeCocharacter := by
  rw [← BialgHom.unipotentCoefficientIdeal_le_ker_iff]
  intro a ha
  rw [RingHom.mem_ker, cellPt1, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2
      (show a ∈ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal from ha)]
  exact map_zero _

lemma cellPt3_mem (φ : OpenCellRing l →ₐ[k] k) : cellPt3 l φ ∈ unipotent k l := by
  rw [← BialgHom.unipotentCoefficientIdeal_le_ker_iff]
  intro a ha
  rw [RingHom.mem_ker, cellPt3, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2
      (show a ∈ l.unipotentDefiningHopfIdeal.toIdeal from ha)]
  exact map_zero _

lemma cellPt2_mem (φ : OpenCellRing l →ₐ[k] k) : cellPt2 l φ ∈ parabolic k l := by
  rw [← negativeCoefficientIdeal_le_ker_iff]
  intro a ha
  have hle : (parabolicDefiningHopfIdeal l).toIdeal ≤ (leviDefiningHopfIdeal l).toIdeal :=
    HopfIdeal.toIdeal_le_toIdeal.mpr le_sup_left
  rw [RingHom.mem_ker, cellPt2, ofConv_toConv, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 (hle ha)]
  exact map_zero _

lemma counit_cellV_comp_mk :
    (Bialgebra.counitAlgHom k (CellV l)).comp
        (Ideal.Quotient.mkₐ k l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) =
      Bialgebra.counitAlgHom k H := by
  ext a
  rfl

lemma cellPt1_eq_one_iff (φ : OpenCellRing l →ₐ[k] k) :
    cellPt1 l φ = 1 ↔ φ.comp (cellIncl l) = Bialgebra.counitAlgHom k (CellV l) := by
  have hε := counit_cellV_comp_mk l
  have hid : (Algebra.ofId k k).comp (Bialgebra.counitAlgHom k H) =
      Bialgebra.counitAlgHom k H := by ext; rfl
  have hc : ((φ.comp Algebra.TensorProduct.includeLeft).comp Algebra.TensorProduct.includeLeft).comp
      (Ideal.Quotient.mkₐ k l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) =
      (φ.comp (cellIncl l)).comp
        (Ideal.Quotient.mkₐ k l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal) := by
    simp only [cellIncl, AlgHom.comp_assoc]
  rw [AlgHom.convOne_def, hid, cellPt1, hc]
  constructor
  · intro h1
    apply Ideal.Quotient.algHom_ext k
    rw [hε]
    have := congrArg ofConv h1
    rwa [ofConv_toConv, ofConv_toConv] at this
  · intro h1
    rw [h1, hε]

/-- **Rank-one Bruhat in `G(k)`, group form** (the named input `bruhat_rankOne_group` proves). -/
def BruhatGroupEq (n : WithConv (H →ₐ[k] k)) : Prop :=
  ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ p ∈ parabolic k l,
    (∃ v' ∈ unipotent k l.oppositeCocharacter, ∃ p' ∈ parabolic k l, v * p = n * (v' * p')) ↔
      v ≠ 1

/-- `U(λ⁻)(k)·P(λ)(k) ⊆ Ω(k)`: every product lifts to a `k`-point of the open cell (named). -/
def CellPointsSurj : Prop :=
  ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ p ∈ parabolic k l,
    ∃ χ : OpenCellRing l →ₐ[k] k, toConv (χ.comp (openCellMap l)) = v * p

theorem bruhatConvEq_of_groupEq (n : WithConv (H →ₐ[k] k)) (h : BruhatGroupEq l n)
    (hsurj : CellPointsSurj l) : BruhatConvEq l n := by
  intro φ
  have hdec := openCellMap_point l φ
  have hv := cellPt1_mem l φ
  have hp : cellPt2 l φ * cellPt3 l φ ∈ parabolic k l :=
    mul_mem (cellPt2_mem l φ) (unipotent_le_parabolic (cellPt3_mem l φ))
  rw [ne_eq, ← cellPt1_eq_one_iff, ← ne_eq, ← h _ hv _ hp]
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨cellPt1 l χ, cellPt1_mem l χ, cellPt2 l χ * cellPt3 l χ,
      mul_mem (cellPt2_mem l χ) (unipotent_le_parabolic (cellPt3_mem l χ)), ?_⟩
    rw [← mul_assoc (cellPt1 l φ), ← mul_assoc (cellPt1 l χ), ← openCellMap_point,
      ← openCellMap_point]
    exact hχ
  · rintro ⟨v', hv', p', hp', hEq⟩
    obtain ⟨χ, hχ⟩ := hsurj v' hv' p' hp'
    refine ⟨χ, ?_⟩
    rw [hdec, hχ, mul_assoc]
    exact hEq

end Triples

section Surj

open BialgHom

/-- The `k`-point of the open cell with coordinates `(v, z, u)`. -/
def cellOfPts (v z u : WithConv (H →ₐ[k] k))
    (hv : v ∈ unipotent k l.oppositeCocharacter) (hz : z ∈ levi k l) (hu : u ∈ unipotent k l) :
    OpenCellRing l →ₐ[k] k :=
  have hzP : z ∈ parabolic k l := by rw [← parabolic_inf_oppositeCocharacter] at hz; exact hz.1
  have hzP' : z ∈ parabolic k l.oppositeCocharacter := by
    rw [← parabolic_inf_oppositeCocharacter] at hz; exact hz.2
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.lift
      (Ideal.Quotient.liftₐ l.oppositeCocharacter.unipotentDefiningHopfIdeal.toIdeal v.ofConv
        (fun a ha => (unipotentCoefficientIdeal_le_ker_iff _ v).2 hv ha))
      (Ideal.Quotient.liftₐ (leviDefiningHopfIdeal l).toIdeal z.ofConv (fun a ha => by
        rw [leviDefiningHopfIdeal_def, HopfIdeal.sup_toIdeal] at ha
        exact (sup_le ((negativeCoefficientIdeal_le_ker_iff l z).2 hzP)
          ((negativeCoefficientIdeal_le_ker_iff _ z).2 hzP')) ha))
      (fun _ _ => Commute.all _ _))
    (Ideal.Quotient.liftₐ l.unipotentDefiningHopfIdeal.toIdeal u.ofConv
        (fun a ha => (unipotentCoefficientIdeal_le_ker_iff _ u).2 hu ha))
    (fun _ _ => Commute.all _ _)

lemma cellOfPts_point (v z u : WithConv (H →ₐ[k] k))
    (hv : v ∈ unipotent k l.oppositeCocharacter) (hz : z ∈ levi k l) (hu : u ∈ unipotent k l) :
    toConv ((cellOfPts l v z u hv hz hu).comp (openCellMap l)) = v * z * u := by
  rw [openCellMap_point]
  congr 2 <;> apply WithConv.ofConv_injective <;> ext a <;>
    simp [cellPt1, cellPt2, cellPt3, cellOfPts] <;> rfl

theorem cellPointsSurj : CellPointsSurj l := by
  intro v hv p hp
  set z := limit k l ⟨p, hp⟩ with hzdef
  have hz : z ∈ levi k l := limit_mem_levi ⟨p, hp⟩
  have hzP : z ∈ parabolic k l := by
    have := hz; rw [← parabolic_inf_oppositeCocharacter] at this; exact this.1
  have hw : p * z⁻¹ ∈ unipotent k l := by
    have h := coe_leviDecompositionMulEquiv_symm_apply_left k l ⟨p, hp⟩
    rw [← hzdef] at h
    rw [← h]
    exact ((leviDecompositionMulEquiv k l).symm ⟨p, hp⟩).left.2
  have hu : z⁻¹ * p ∈ unipotent k l := by
    have := conj_mem_unipotent (inv_mem hzP) hw
    have e : z⁻¹ * p = z⁻¹ * (p * z⁻¹) * z⁻¹⁻¹ := by group
    rw [e]; exact this
  refine ⟨cellOfPts l v z (z⁻¹ * p) hv hz hu, ?_⟩
  rw [cellOfPts_point]
  group

end Surj

/-! ### Assembly: the core from the `T`-orbit inputs -/

/-- **The rank-one Bruhat core from the group form** (`k = k̄`, `one` = the unit of `U(λ⁻)`). -/
theorem bruhatRankOneCore_of_groupEq [IsAlgClosed k] (n : WithConv (H →ₐ[k] k))
    (h : BruhatGroupEq l n) :
    BruhatRankOneCore l n (TauCeti.Bialgebra.augmentationPoint k (CellV l))
      (AlgHom.isClosed_singleton_kernelPoint _) :=
  bruhatRankOneCore_of_pointEq l n _ _
    (bruhatPointEq_of_convEq l n (bruhatConvEq_of_groupEq l n h (cellPointsSurj l)))

/-- **The rank-one Bruhat core from the `T`-orbit data.** `U⁻ = U(λ⁻)(k)`, `P = P(λ)(k)`;
inputs: a subgroup `T ≤ P` normalizing `U⁻`, with `n⁻¹ T n ⊆ T`, `n⁻¹ ∉ U⁻P`, `T` transitive on
`U⁻ ∖ {1}`, and `U⁻ ∩ n U⁻ P ≠ ∅`. -/
theorem bruhatRankOneCore_of_orbit [IsAlgClosed k] (n : WithConv (H →ₐ[k] k))
    (T : Subgroup (WithConv (H →ₐ[k] k))) (hTP : T ≤ parabolic k l)
    (hTU : ∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter,
      t * v * t⁻¹ ∈ unipotent k l.oppositeCocharacter)
    (hnT : ∀ t ∈ T, n⁻¹ * t * n ∈ T)
    (hn : ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ p ∈ parabolic k l, n⁻¹ ≠ v * p)
    (htrans : ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ w ∈ unipotent k l.oppositeCocharacter,
      v ≠ 1 → w ≠ 1 → ∃ t ∈ T, w = t * v * t⁻¹)
    (hne : ∃ v ∈ unipotent k l.oppositeCocharacter, ∃ v' ∈ unipotent k l.oppositeCocharacter,
      ∃ p' ∈ parabolic k l, v = n * (v' * p')) :
    BruhatRankOneCore l n (TauCeti.Bialgebra.augmentationPoint k (CellV l))
      (AlgHom.isClosed_singleton_kernelPoint _) :=
  bruhatRankOneCore_of_groupEq l n fun _ hv _ hp =>
    bruhat_rankOne_group _ _ T n hTP hTU hnT hn htrans hne hv hp

/-! ### Inputs (c): `hn` from the Weyl property, `hne` from irreducibility -/

section Inputs

/-- **`n⁻¹ ∉ U(λ⁻)(k)·P(λ)(k)`** from the Weyl property `n⁻¹ P(λ) n ⊆ P(λ⁻)` and `U(λ)(k) ≠ 1`
(group form of `DynamicTransport.not_mem_openCell`, with the satisfiable hypothesis stated
directly on `P(λ)`). -/
theorem inv_not_mem_cell {n : WithConv (H →ₐ[k] k)}
    (hconj : ∀ x ∈ parabolic k l, n⁻¹ * x * n ∈ parabolic k l.oppositeCocharacter)
    (hU : ∃ u ∈ unipotent k l, u ≠ 1) :
    ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ b ∈ parabolic k l, n⁻¹ ≠ v * b := by
  intro v hv b hb hEq
  obtain ⟨u, hu, hu1⟩ := hU
  have h1 := hconj _ (unipotent_le_parabolic hu)
  have h2 : b * u * b⁻¹ ∈ unipotent k l := conj_mem_unipotent hb hu
  have hv' := unipotent_le_parabolic hv
  have h3 : b * u * b⁻¹ ∈ parabolic k l.oppositeCocharacter := by
    have hb' : b = v⁻¹ * n⁻¹ := by rw [hEq]; group
    have : b * u * b⁻¹ = v⁻¹ * (n⁻¹ * u * n) * v := by rw [hb']; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hv') h1) hv'
  have hbot := unipotent_opposite_inf_parabolic (A := k) l.oppositeCocharacter
  rw [BialgHom.oppositeCocharacter_oppositeCocharacter] at hbot
  have hmem : b * u * b⁻¹ ∈ (⊥ : Subgroup _) := hbot ▸ ⟨h2, h3⟩
  rw [Subgroup.mem_bot] at hmem
  apply hu1
  have : u = b⁻¹ * (b * u * b⁻¹) * b := by group
  rw [this, hmem]; group

/-- **`U(λ⁻)(k) ∩ n·Ω(k) ≠ ∅`** for `G` irreducible: `Ω ∩ nΩ` is a nonempty open, so it has a
closed (= `k`-)point `g = v z u = n v' z' u'`, and `v = n · v' · (z' u' (z u)⁻¹)`. -/
theorem hne_of_irreducible [IsAlgClosed k]
    [IrreducibleSpace (Spec (CommRingCat.of H))] (n : WithConv (H →ₐ[k] k)) :
    ∃ v ∈ unipotent k l.oppositeCocharacter, ∃ v' ∈ unipotent k l.oppositeCocharacter,
      ∃ p' ∈ parabolic k l, v = n * (v' * p') := by
  let e := cellOfPts l 1 1 1 (one_mem _) (one_mem _) (one_mem _)
  have h1 : ((openCellOpens l : Set (Spec (CommRingCat.of H))) ∩ translateOpenCell l n).Nonempty := by
    apply nonempty_preirreducible_inter (openCellOpens l).isOpen (translateOpenCell l n).isOpen
    · exact ⟨_, Scheme.Hom.mem_opensRange.2 ⟨AlgHom.kernelPoint e, rfl⟩⟩
    · exact ⟨_, Scheme.Hom.mem_opensRange.2 ⟨AlgHom.kernelPoint e, rfl⟩⟩
  have hlc : IsLocallyClosed ((openCellOpens l : Set (Spec (CommRingCat.of H))) ∩
      translateOpenCell l n) :=
    ((openCellOpens l).isOpen.inter (translateOpenCell l n).isOpen).isLocallyClosed
  have : IsJacobsonRing H := isJacobsonRing_of_finiteType (A := k)
  obtain ⟨x, ⟨hxΩ, hxn⟩, hxc⟩ := nonempty_inter_closedPoints h1 hlc
  rw [← TauCeti.range_kernelPoint_eq_closedPoints (k := k)] at hxc
  obtain ⟨g, rfl⟩ := hxc
  obtain ⟨χ, hχ⟩ := exists_kernelPoint_of_mem_range (k := k) (openCellMor l) g
    (Scheme.Hom.mem_opensRange.1 hxΩ)
  obtain ⟨χ', hχ'⟩ := exists_kernelPoint_of_mem_range (k := k) (translateOpenCellMor l n) g
    (Scheme.Hom.mem_opensRange.1 hxn)
  rw [openCellMor_kernelPoint] at hχ
  rw [translateOpenCellMor_kernelPoint] at hχ'
  have e1 := kernelPoint_inj hχ
  have e2 := kernelPoint_inj hχ'
  have key : toConv (χ.comp (openCellMap l)) = n * toConv (χ'.comp (openCellMap l)) := by
    rw [e1, ← e2, toConv_ofConv]
  rw [openCellMap_point, openCellMap_point] at key
  refine ⟨cellPt1 l χ, cellPt1_mem l χ, cellPt1 l χ', cellPt1_mem l χ',
    cellPt2 l χ' * cellPt3 l χ' * (cellPt2 l χ * cellPt3 l χ)⁻¹,
    mul_mem (mul_mem (cellPt2_mem l χ') (unipotent_le_parabolic (cellPt3_mem l χ')))
      (inv_mem (mul_mem (cellPt2_mem l χ) (unipotent_le_parabolic (cellPt3_mem l χ)))), ?_⟩
  have h : cellPt1 l χ = cellPt1 l χ * cellPt2 l χ * cellPt3 l χ *
      (cellPt2 l χ * cellPt3 l χ)⁻¹ := by group
  rw [h, key]
  group

/-- **Transitivity from a `G_a`-coordinate** (the shape RayGa gives: `O(U(λ⁻)) = k[y]`, `y` of
weight `γ`). If `e : U⁻ → K` is injective with `e v = 0 ⇔ v = 1`, `T` acts by
`e(t v t⁻¹) = χ(t) e(v)`, and `χ` hits every nonzero scalar, then `T` is transitive on
`U⁻ ∖ {1}`. -/
theorem htrans_of_coordinate {G : Type*} [Group G] (Um T : Subgroup G) {K : Type*} [Field K]
    (e : G → K) (he0 : ∀ v ∈ Um, e v = 0 ↔ v = 1)
    (hinj : ∀ v ∈ Um, ∀ w ∈ Um, e v = e w → v = w)
    (χ : G → K) (hχ : ∀ c : K, c ≠ 0 → ∃ t ∈ T, χ t = c)
    (hact : ∀ t ∈ T, ∀ v ∈ Um, e (t * v * t⁻¹) = χ t * e v)
    (hTU : ∀ t ∈ T, ∀ v ∈ Um, t * v * t⁻¹ ∈ Um) :
    ∀ v ∈ Um, ∀ w ∈ Um, v ≠ 1 → w ≠ 1 → ∃ t ∈ T, w = t * v * t⁻¹ := by
  intro v hv w hw hv1 hw1
  have hev : e v ≠ 0 := fun h => hv1 ((he0 v hv).1 h)
  have hew : e w ≠ 0 := fun h => hw1 ((he0 w hw).1 h)
  obtain ⟨t, ht, hχt⟩ := hχ (e w / e v) (div_ne_zero hew hev)
  refine ⟨t, ht, hinj w hw _ (hTU t ht v hv) ?_⟩
  rw [hact t ht v hv, hχt, div_mul_cancel₀ _ hev]

/-- **The rank-one Bruhat core, final form.** `k = k̄`, `G` irreducible; `n` with
`n⁻¹ P(λ) n ⊆ P(λ⁻)` (Weyl property, `σλ = −λ`) and `U(λ)(k) ≠ 1`; a subgroup `T ≤ P(λ)(k)`
normalizing `U(λ⁻)(k)` with `n⁻¹ T n ⊆ T`, transitive by conjugation on `U(λ⁻)(k) ∖ {1}`. -/
theorem bruhatRankOneCore_of_rankOne [IsAlgClosed k]
    [IrreducibleSpace (Spec (CommRingCat.of H))] (n : WithConv (H →ₐ[k] k))
    (hconj : ∀ x ∈ parabolic k l, n⁻¹ * x * n ∈ parabolic k l.oppositeCocharacter)
    (hU : ∃ u ∈ unipotent k l, u ≠ 1)
    (T : Subgroup (WithConv (H →ₐ[k] k))) (hTP : T ≤ parabolic k l)
    (hTU : ∀ t ∈ T, ∀ v ∈ unipotent k l.oppositeCocharacter,
      t * v * t⁻¹ ∈ unipotent k l.oppositeCocharacter)
    (hnT : ∀ t ∈ T, n⁻¹ * t * n ∈ T)
    (htrans : ∀ v ∈ unipotent k l.oppositeCocharacter, ∀ w ∈ unipotent k l.oppositeCocharacter,
      v ≠ 1 → w ≠ 1 → ∃ t ∈ T, w = t * v * t⁻¹) :
    BruhatRankOneCore l n (TauCeti.Bialgebra.augmentationPoint k (CellV l))
      (AlgHom.isClosed_singleton_kernelPoint _) :=
  bruhatRankOneCore_of_orbit l n T hTP hTU hnT (inv_not_mem_cell l hconj hU) htrans
    (hne_of_irreducible l n)

end Inputs

end AlgMag.Reductive
