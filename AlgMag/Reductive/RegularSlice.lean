/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RootGroups
import AlgMag.Reductive.IdentityComponentRoots
import AlgMag.Reductive.PushCocharacter
import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Connected
import Mathlib.GroupTheory.CosetCover

/-!
# The regular slice `U⁻ × U⁺ × T → K` (step C2(d), part (i))

`G = Spec H` over a field `k`, `T = D(X)` acting through `π`, `Φ = roots π`, `N` a magnet,
`K = (G^N)°`. For a cocharacter `ψ : X → ℤ` (the magnet map `⟨-, λ⟩`):

* `sliceRoots π N ψ = {α ∈ Φ ∩ N | ⟨α, λ⟩ > 0}`, `sliceMagnet` the magnet it generates
  (pointed: `sliceMagnet_pointed`);
* `sliceIdeal π N ψ`: `U⁺ = G^{[R ∩ λ>0⟩}_e`, the attractor with prescribed limit `e`
  (`prescribedUnitHopfIdeal`); `U⁻` is `sliceIdeal π N ψ⁻¹` (`pairingHom_inv`);
* `mem_lieSubalgebra_sliceIdeal_iff`: `Lie(U⁺) = ⊕_{α ∈ sliceRoots} 𝔤_α`;
* `unipotentDefiningHopfIdeal_le_sliceIdeal`, `isCocharacterStable_sliceIdeal`: `U⁺ ⊆ U(λ)` is
  `λ`-stable, hence connected (`connectedSpace_slice`), hence `U⁺ ⊆ K` (`compIdeal_le_sliceIdeal`);
* `sliceMap`: the `k`-algebra map `O(K) → O(U⁻) ⊗ O(U⁺) ⊗ O(T)` of
  `μ(u, v, t) = (u v) t (u v)⁻¹`, with `sliceMap_comp_compMk` (it is the conjugation formula on
  `O(G)`), given `T ⊆ K` (`hT`);
* `exists_generic_cocharacter`: for `X` free and `R` finite without `0`, some `λ` has
  `⟨α, λ⟩ ≠ 0` on `R`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

@[simp] lemma pairingHom_inv (ψ : X →* Multiplicative ℤ) (χ : Additive X) :
    pairingHom ψ⁻¹ χ = - pairingHom ψ χ := rfl

section Slice

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

/-- `R ∩ {λ > 0}`, `R = N ∩ Φ`. -/
def sliceRoots : Set (Additive X) := {α | α ∈ roots π ∧ α ∈ N ∧ 0 < pairingHom ψ α}

/-- The magnet `[R ∩ λ>0⟩`. -/
def sliceMagnet : Magnet (Additive X) := AddSubmonoid.closure (sliceRoots π N ψ)

variable {π N ψ} in
lemma eq_zero_or_pos_of_mem_sliceMagnet {χ : Additive X} (h : χ ∈ sliceMagnet π N ψ) :
    χ = 0 ∨ 0 < pairingHom ψ χ := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx => exact Or.inr hx.2.2
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | hx
    · simpa using hy
    · rcases hy with rfl | hy
      · simpa using Or.inr hx
      · exact Or.inr (by rw [map_add]; omega)

lemma sliceMagnet_pointed :
    ∀ a ∈ sliceMagnet π N ψ, ∀ b ∈ sliceMagnet π N ψ, a + b = 0 → a = 0 := by
  intro a ha b hb hab
  rcases eq_zero_or_pos_of_mem_sliceMagnet ha with h | ha'
  · exact h
  rcases eq_zero_or_pos_of_mem_sliceMagnet hb with rfl | hb'
  · simpa using hab
  · have := congrArg (pairingHom ψ) hab
    rw [map_add, map_zero] at this
    omega

lemma sliceMagnet_le : sliceMagnet π N ψ ≤ N :=
  AddSubmonoid.closure_le.2 fun _ h => h.2.1

lemma sliceMagnet_le_nat : sliceMagnet π N ψ ≤ natMagnet.comap (pairingHom ψ) := by
  intro χ h
  rw [AddSubmonoid.mem_comap]
  rcases eq_zero_or_pos_of_mem_sliceMagnet h with rfl | h
  · simpa using (natMagnet).zero_mem
  · exact (mem_natMagnet).2 h.le

/-- **`U⁺ = G^{[R ∩ λ>0⟩}_e`** (and `U⁻ = sliceIdeal π N ψ⁻¹`). -/
def sliceIdeal : HopfIdeal k H :=
  prescribedUnitHopfIdeal π (sliceMagnet π N ψ) (sliceMagnet_pointed π N ψ)

lemma sliceIdeal_toIdeal :
    (sliceIdeal π N ψ).toIdeal = prescribedUnitIdeal π (sliceMagnet π N ψ) :=
  prescribedUnitHopfIdeal_toIdeal _ _ _

/-- `U⁺` is `T`-stable. -/
theorem isHomogeneous_sliceIdeal :
    (sliceIdeal π N ψ).toIdeal.IsHomogeneous (torusGrading π) := by
  rw [sliceIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal, ← Ideal.span_union]
  refine Ideal.homogeneous_span _ _ ?_
  rintro x (hx | ⟨x, hx, rfl⟩)
  · obtain ⟨χ, -, hx⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨χ, hx⟩
  · refine ⟨0, Submodule.sub_mem _ hx ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem

/-- **`Lie(U⁺) = ⊕_{α ∈ R, ⟨α,λ⟩ > 0} 𝔤_α`**: a tangent vector at `e` lies in `Lie(U⁺)` iff it
vanishes on every weight space `H_χ` with `χ ∉ R ∩ {λ > 0}`. -/
theorem mem_lieSubalgebra_sliceIdeal_iff (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) :
    d ∈ (sliceIdeal π N ψ).lieSubalgebra (B := k) ↔
      ∀ χ, χ ∉ sliceRoots π N ψ → ∀ h ∈ torusGrading π χ, d h = 0 := by
  have hspan : (sliceIdeal π N ψ).toIdeal = Ideal.span
      ((⋃ (m : Additive X) (_ : m ∉ sliceMagnet π N ψ), (torusGrading π m : Set H)) ∪
        {y | ∃ x ∈ torusGrading π 0, x - algebraMap k H (Coalgebra.counit (R := k) x) = y}) := by
    rw [sliceIdeal_toIdeal, prescribedUnitIdeal, magnetIdeal, Ideal.span_union]
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan]
  constructor
  · intro hd χ hχ h hh
    by_cases hM : χ ∈ sliceMagnet π N ψ
    · by_cases h0 : χ = 0
      · subst h0
        have := hd _ (Or.inr ⟨h, hh, rfl⟩)
        simpa only [map_sub, d.map_algebraMap, sub_zero] using this
      · by_contra hne
        have hW : χ ∈ tangentWeights π k := ⟨d, h, hh, hne⟩
        rcases tangentWeights_subset_insert_roots hW with h' | h'
        · exact h0 h'
        · refine hχ ⟨h', sliceMagnet_le π N ψ hM, ?_⟩
          rcases eq_zero_or_pos_of_mem_sliceMagnet hM with h'' | h''
          · exact absurd h'' h0
          · exact h''
    · exact hd h (Or.inl (Set.mem_iUnion₂.2 ⟨χ, hM, hh⟩))
  · intro hd x hx
    rcases hx with hx | ⟨x, hx, rfl⟩
    · obtain ⟨χ, hχ, hx⟩ := Set.mem_iUnion₂.1 hx
      exact hd χ (fun h => hχ (AddSubmonoid.subset_closure h)) x hx
    · have h0 : (0 : Additive X) ∉ sliceRoots π N ψ := fun h => by
        have := h.2.2; simp at this
      simpa only [map_sub, d.map_algebraMap, sub_zero] using hd 0 h0 x hx

/-- `U⁺ ⊆ U(λ)`. -/
theorem unipotentDefiningHopfIdeal_le_sliceIdeal :
    (π.cocharacter ψ).unipotentDefiningHopfIdeal ≤ sliceIdeal π N ψ := by
  rw [BialgHom.unipotentDefiningHopfIdeal_le_iff]
  refine ⟨?_, fun h => ?_⟩
  · rw [← HopfIdeal.toIdeal_le_toIdeal, sliceIdeal_toIdeal, prescribedUnitIdeal,
      ← magnetIdeal_torusGrading_comap_nat]
    exact le_sup_of_le_left (magnetIdeal_anti _ (sliceMagnet_le_nat π N ψ))
  · rw [← HopfIdeal.mem_toIdeal, sliceIdeal_toIdeal, prescribedUnitIdeal]
    induction h using induction_torusGrading (π := π) with
    | h0 => simp
    | hadd x y hx hy =>
      have e : (conjugationAlgHom (π.cocharacter ψ) (x + y)).coeff 0 -
          algebraMap k H (Coalgebra.counit (R := k) (x + y)) =
          ((conjugationAlgHom (π.cocharacter ψ) x).coeff 0 -
            algebraMap k H (Coalgebra.counit (R := k) x)) +
          ((conjugationAlgHom (π.cocharacter ψ) y).coeff 0 -
            algebraMap k H (Coalgebra.counit (R := k) y)) := by
        have hc : (conjugationAlgHom (π.cocharacter ψ) (x + y)).coeff 0 =
            (conjugationAlgHom (π.cocharacter ψ) x).coeff 0 +
              (conjugationAlgHom (π.cocharacter ψ) y).coeff 0 := by
          rw [map_add]; rfl
        rw [hc, map_add, map_add]; abel
      rw [e]; exact add_mem hx hy
    | hmem χ x hx =>
      rw [coeff_of_mem_lineGrading (torusGrading_le_lineGrading (ψ := ψ) χ hx)]
      by_cases hχ : χ = 0
      · subst hχ
        rw [if_pos (by simp)]
        exact Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, rfl⟩)
      · rw [counit_eq_zero_of_mem hχ hx, map_zero, sub_zero]
        split_ifs with hp
        · refine Ideal.mem_sup_left (mem_magnetIdeal_of_notMem (m := χ) (fun hM => ?_) hx)
          rcases eq_zero_or_pos_of_mem_sliceMagnet hM with h' | h'
          · exact hχ h'
          · rw [pairingHom_apply] at h'; omega
        · exact zero_mem _

/-- `U⁺` is stable under conjugation by `λ`. -/
theorem isCocharacterStable_sliceIdeal :
    (sliceIdeal π N ψ).IsCocharacterStable (π.cocharacter ψ) := by
  classical
  intro x hx n
  have hx' : x ∈ (sliceIdeal π N ψ).toIdeal := HopfIdeal.mem_toIdeal.2 hx
  rw [← HopfIdeal.mem_toIdeal]
  have hsum := DirectSum.sum_support_decompose (torusGrading π) x
  rw [← hsum, map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Ideal.sum_mem _ fun χ _ => ?_
  rw [coeff_of_mem_lineGrading (torusGrading_le_lineGrading (ψ := ψ) χ (SetLike.coe_mem _))]
  split_ifs
  · exact isHomogeneous_sliceIdeal π N ψ χ hx'
  · exact zero_mem _

end Slice

section AlgClosed

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [IsAlgClosed k] [Algebra.FiniteType k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

instance finiteType_slice : Algebra.FiniteType k (H ⧸ (sliceIdeal π N ψ).toIdeal) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)

/-- **`U⁺` is connected** (contracted to `e` by `λ`). -/
theorem connectedSpace_slice :
    ConnectedSpace (PrimeSpectrum (H ⧸ (sliceIdeal π N ψ).toIdeal)) :=
  (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1
    (geometricallyConnectedCommHopfAlgProperty_quotient_of_isCocharacterStable
      (unipotentDefiningHopfIdeal_le_sliceIdeal π N ψ) (isCocharacterStable_sliceIdeal π N ψ))

/-- **`U⁺ ⊆ K = (G^N)°`.** -/
theorem compIdeal_le_sliceIdeal : compIdeal π N ≤ (sliceIdeal π N ψ).toIdeal := by
  have hJ : (magnetHopfIdeal π N).toIdeal ≤ RingHom.ker
      (Bialgebra.Quotient.mkBialgHom (R := k) (A := H) (sliceIdeal π N ψ).toIdeal).toAlgHom.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, sliceIdeal_toIdeal, prescribedUnitIdeal]
    rw [magnetHopfIdeal_toIdeal] at hx
    exact Ideal.mem_sup_left (magnetIdeal_anti _ (sliceMagnet_le π N ψ) hx)
  let g := Bialgebra.Quotient.liftBialgHom _
    (Bialgebra.Quotient.mkBialgHom (R := k) (A := H) (sliceIdeal π N ψ).toIdeal) hJ
  have := connectedSpace_slice π N ψ
  have hI : (attrComp π N).toIdeal ≤ RingHom.ker g.toAlgHom.toRingHom :=
    CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected
      (H := _root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π N).toIdeal))
      (K := _root_.CommHopfAlgCat.of k (H ⧸ (sliceIdeal π N ψ).toIdeal))
      (_root_.CommHopfAlgCat.ofHom g)
  intro x hx
  have hx' : Ideal.Quotient.mk _ x ∈ (attrComp π N).toIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.1 (show compMk π N x = 0 from hx)
  have h2 := hI hx'
  rw [RingHom.mem_ker] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.1 h2

/-- `O(K)`. -/
abbrev compAlg := (H ⧸ (magnetHopfIdeal π N).toIdeal) ⧸ (attrComp π N).toIdeal

variable {π N} in
/-- A map `O(G) → B` killing the ideal of `K` factors through `O(K)`. -/
def compFactor {B : Type u} [CommRing B] [Algebra k B] (f : H →ₐ[k] B)
    (hf : compIdeal π N ≤ RingHom.ker f) : compAlg π N →ₐ[k] B :=
  (Ideal.Quotient.liftₐ (RingHom.ker (compMk π N).toAlgHom) f (fun a ha => hf ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (compMk π N).toAlgHom)
      (compMk_surjective π N)).symm.toAlgHom

variable {π N} in
@[simp] lemma compFactor_compMk {B : Type u} [CommRing B] [Algebra k B] (f : H →ₐ[k] B)
    (hf : compIdeal π N ≤ RingHom.ker f) (x : H) : compFactor f hf (compMk π N x) = f x := by
  have e : Ideal.quotientKerAlgEquivOfSurjective (f := (compMk π N).toAlgHom)
      (compMk_surjective π N) (Ideal.Quotient.mk _ x) = compMk π N x := rfl
  rw [compFactor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← e,
    AlgEquiv.symm_apply_apply]
  rfl

/-- `(u v) t (u v)⁻¹` in a group of points. -/
def conjFormula {C B : Type u} [CommRing C] [HopfAlgebra k C] [CommRing B] [Algebra k B]
    (u v t : WithConv (C →ₐ[k] B)) : WithConv (C →ₐ[k] B) :=
  (u * v) * t * (u * v)⁻¹

lemma mapDomain_conjFormula {C C' B : Type u} [CommRing C] [HopfAlgebra k C] [CommRing C']
    [HopfAlgebra k C'] [CommRing B] [Algebra k B] (f : C →ₐc[k] C')
    (u v t : WithConv (C' →ₐ[k] B)) :
    BialgHom.mapDomain f (conjFormula u v t) =
      conjFormula (BialgHom.mapDomain f u) (BialgHom.mapDomain f v) (BialgHom.mapDomain f t) := by
  simp only [conjFormula, map_mul, map_inv]

/-- `O(U⁻) ⊗ O(U⁺) ⊗ O(T)`. -/
def sliceSource : Type u :=
  ((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k] (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k]
    MonoidAlgebra k X

instance : CommRing (sliceSource π N ψ) :=
  inferInstanceAs (CommRing (((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k]
    (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))

instance : Algebra k (sliceSource π N ψ) :=
  inferInstanceAs (Algebra k (((H ⧸ (sliceIdeal π N ψ⁻¹).toIdeal) ⊗[k]
    (H ⧸ (sliceIdeal π N ψ).toIdeal)) ⊗[k] MonoidAlgebra k X))

/-- The universal point `u ∈ U⁻`. -/
def slicePtMinus : WithConv (H →ₐ[k] sliceSource π N ψ) :=
  toConv (Algebra.TensorProduct.includeLeft.comp
    (Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ k _)))

/-- The universal point `v ∈ U⁺`. -/
def slicePtPlus : WithConv (H →ₐ[k] sliceSource π N ψ) :=
  toConv (Algebra.TensorProduct.includeLeft.comp
    (Algebra.TensorProduct.includeRight.comp (Ideal.Quotient.mkₐ k _)))

/-- The universal point `t ∈ T`. -/
def slicePtTorus : WithConv (H →ₐ[k] sliceSource π N ψ) :=
  toConv (Algebra.TensorProduct.includeRight.comp π.toAlgHom)

/-- `μ(u, v, t) = (u v) t (u v)⁻¹` as a point of `G`. -/
def sliceConj : WithConv (H →ₐ[k] sliceSource π N ψ) :=
  conjFormula (slicePtMinus π N ψ) (slicePtPlus π N ψ) (slicePtTorus π N ψ)

variable (hT : compIdeal π N ≤ RingHom.ker π.toAlgHom)

/-- The `K`-point `u`. -/
def sliceKMinus : WithConv (compAlg π N →ₐ[k] sliceSource π N ψ) :=
  toConv (compFactor (slicePtMinus π N ψ).ofConv (fun x hx => by
    have := compIdeal_le_sliceIdeal π N ψ⁻¹ hx
    rw [RingHom.mem_ker, slicePtMinus, ofConv_toConv]
    change Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeLeft (S := k)
      (Ideal.Quotient.mk (sliceIdeal π N ψ⁻¹).toIdeal x)) = (0 : sliceSource π N ψ)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 this, map_zero, map_zero] <;> rfl))

/-- The `K`-point `v`. -/
def sliceKPlus : WithConv (compAlg π N →ₐ[k] sliceSource π N ψ) :=
  toConv (compFactor (slicePtPlus π N ψ).ofConv (fun x hx => by
    have := compIdeal_le_sliceIdeal π N ψ hx
    rw [RingHom.mem_ker, slicePtPlus, ofConv_toConv]
    change Algebra.TensorProduct.includeLeft (S := k) (Algebra.TensorProduct.includeRight
      (Ideal.Quotient.mk (sliceIdeal π N ψ).toIdeal x)) = (0 : sliceSource π N ψ)
    rw [Ideal.Quotient.eq_zero_iff_mem.2 this, map_zero, map_zero] <;> rfl))

/-- The `K`-point `t`. -/
def sliceKTorus : WithConv (compAlg π N →ₐ[k] sliceSource π N ψ) :=
  toConv (compFactor (slicePtTorus π N ψ).ofConv (fun x hx => by
    have : π.toAlgHom x = 0 := hT hx
    rw [RingHom.mem_ker, slicePtTorus, ofConv_toConv]
    change Algebra.TensorProduct.includeRight (π.toAlgHom x) = (0 : sliceSource π N ψ)
    rw [this, map_zero] <;> rfl))

/-- **The slice map** `μ^* : O(K) → O(U⁻) ⊗ O(U⁺) ⊗ O(T)`,
`μ(u, v, t) = (u v) t (u v)⁻¹`. -/
def sliceMap : compAlg π N →ₐ[k] sliceSource π N ψ :=
  (conjFormula (sliceKMinus π N ψ) (sliceKPlus π N ψ) (sliceKTorus π N ψ hT)).ofConv

/-- `μ^*` composed with `O(G) → O(K)` is the conjugation formula on `O(G)`. -/
theorem sliceMap_comp_compMk :
    (sliceMap π N ψ hT).comp (compMk π N : H →ₐ[k] compAlg π N) = (sliceConj π N ψ).ofConv := by
  have hm : BialgHom.mapDomain (A := sliceSource π N ψ) (compMk π N) (sliceKMinus π N ψ) = slicePtMinus π N ψ := by
    apply WithConv.ofConv_injective; ext x
    rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    exact compFactor_compMk _ _ x
  have hp : BialgHom.mapDomain (A := sliceSource π N ψ) (compMk π N) (sliceKPlus π N ψ) = slicePtPlus π N ψ := by
    apply WithConv.ofConv_injective; ext x
    rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    exact compFactor_compMk _ _ x
  have ht : BialgHom.mapDomain (A := sliceSource π N ψ) (compMk π N) (sliceKTorus π N ψ hT) = slicePtTorus π N ψ := by
    apply WithConv.ofConv_injective; ext x
    rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    exact compFactor_compMk _ _ x
  rw [sliceMap, sliceConj, ← hm, ← hp, ← ht, ← mapDomain_conjFormula]
  rfl

lemma sliceMap_compMk (x : H) :
    sliceMap π N ψ hT (compMk π N x) = (sliceConj π N ψ).ofConv x :=
  AlgHom.congr_fun (sliceMap_comp_compMk π N ψ hT) x

end AlgClosed

/-- **Existence of a generic cocharacter.** For `X` free and `R` finite not containing `0`,
there is `λ` with `⟨α, λ⟩ ≠ 0` for all `α ∈ R`. -/
theorem exists_generic_cocharacter [Module.Free ℤ (Additive X)] (R : Set (Additive X))
    (hR : R.Finite) (h0 : ∀ α ∈ R, α ≠ 0) :
    ∃ ψ : X →* Multiplicative ℤ, ∀ α ∈ R, pairingHom ψ α ≠ 0 := by
  classical
  let M := Module.Dual ℤ (Additive X)
  let p : Additive X → Submodule ℤ M := fun α => LinearMap.ker (Module.Dual.eval ℤ _ α)
  by_contra hne
  push Not at hne
  have hcov : ⋃ α ∈ hR.toFinset, (p α : Set M) = Set.univ := by
    refine Set.eq_univ_of_forall fun φ => ?_
    obtain ⟨α, hα, hφ⟩ := hne
      { toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul x))
        map_one' := by simp
        map_mul' := by simp }
    refine Set.mem_iUnion₂.2 ⟨α, hR.mem_toFinset.2 hα, ?_⟩
    refine LinearMap.mem_ker.2 ?_
    change φ α = 0
    simpa using hφ
  obtain ⟨α, hα, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcov
  have hα0 := h0 α (hR.mem_toFinset.1 hα)
  obtain ⟨φ0, hφ0⟩ : ∃ φ : M, φ α ≠ 0 := by
    by_contra h; push Not at h
    exact hα0 ((Module.forall_dual_apply_eq_zero_iff ℤ α).1 h)
  have : Finite (M ⧸ p α) := AddSubgroup.finite_quotient_of_finiteIndex
  have hinj : Function.Injective fun n : ℕ => Submodule.Quotient.mk (p := p α) ((n : ℤ) • φ0) := by
    intro n m h
    have h' := (Submodule.Quotient.eq _).1 h
    change ((n : ℤ) • φ0 - (m : ℤ) • φ0) α = 0 at h'
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← sub_mul] at h'
    have := (mul_eq_zero.1 h').resolve_right hφ0
    omega
  exact not_injective_infinite_finite _ hinj

end AlgMag.Reductive
