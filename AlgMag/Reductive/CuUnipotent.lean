/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.CuCentralizes
import AlgMag.Reductive.CuCandidate
import AlgMag.Reductive.UnipotentGroupLike
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality

/-!
# `hunip`: conjugation by a point of `C_u` is locally unipotent

* (a) points of `V(CuIdeal π)` are unipotent points of `G` (`H ⧸ C_u ≅ (H ⧸ C) ⧸ R_u(C)` is
  smooth unipotent, `cuQuotientIso`);
* (b) the conjugation coaction `h ↦ (g ↦ h(g⁻¹ x g))` makes (a type synonym of) `H` a right
  `H`-comodule, whose action of a `k`-point `g` is `Ad g⁻¹`; a unipotent point acts locally
  unipotently on every finite subcomodule.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Comodule WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

local notation "Ad" => HopfAlgebra.pointConjugationAlgHom

section Conj

variable {k : Type u} {H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- Type synonym of `H` carrying the conjugation comodule. -/
def ConjH (H : Type u) : Type u := H

instance : AddCommGroup (ConjH H) := inferInstanceAs (AddCommGroup H)
instance : Module k (ConjH H) := inferInstanceAs (Module k H)

/-- The two universal points of `G(H ⊗ H)`. -/
abbrev i₁ : WithConv (H →ₐ[k] H ⊗[k] H) := toConv Algebra.TensorProduct.includeLeft
abbrev i₂ : WithConv (H →ₐ[k] H ⊗[k] H) := toConv Algebra.TensorProduct.includeRight

/-- The conjugation coaction `(x, g) ↦ g⁻¹ x g`. -/
def conjCoact : H →ₐ[k] H ⊗[k] H :=
  ((i₂ (k := k) (H := H))⁻¹ * i₁ * i₂).ofConv

lemma toConv_comp_eq_mapValue {B B' : Type u} [CommRing B] [Algebra k B] [CommRing B']
    [Algebra k B'] (F : B →ₐ[k] B') (p : H →ₐ[k] B) :
    toConv (F.comp p) = AlgHom.mapValue F (toConv p) := by
  rw [AlgHom.mapValue_apply, ofConv_toConv]

lemma mapValue_conjCoact {B : Type u} [CommRing B] [Algebra k B] (F : H ⊗[k] H →ₐ[k] B) :
    toConv (F.comp conjCoact) = (toConv (F.comp Algebra.TensorProduct.includeRight))⁻¹ *
      toConv (F.comp Algebra.TensorProduct.includeLeft) *
        toConv (F.comp Algebra.TensorProduct.includeRight) := by
  rw [toConv_comp_eq_mapValue, conjCoact, toConv_ofConv, map_mul, map_mul, map_inv,
    ← toConv_comp_eq_mapValue, ← toConv_comp_eq_mapValue]

lemma conjCoact_coassoc :
    (Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
        ((Algebra.TensorProduct.map (conjCoact (k := k) (H := H)) (AlgHom.id k H)).comp
          conjCoact) =
      (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.comulAlgHom k H)).comp
        conjCoact := by
  apply WithConv.toConv_injective
  rw [← AlgHom.comp_assoc, mapValue_conjCoact, mapValue_conjCoact]
  have e1 : ((Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
      (Algebra.TensorProduct.map (conjCoact (k := k) (H := H)) (AlgHom.id k H))).comp
        Algebra.TensorProduct.includeLeft =
      ((Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
        Algebra.TensorProduct.includeLeft).comp conjCoact := by
    ext x; simp [Algebra.TensorProduct.one_def]
  have e2 : ((Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
      (Algebra.TensorProduct.map (conjCoact (k := k) (H := H)) (AlgHom.id k H))).comp
        Algebra.TensorProduct.includeRight =
      (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight :
        H →ₐ[k] H ⊗[k] (H ⊗[k] H)) := by
    ext x; simp [Algebra.TensorProduct.one_def]
  rw [e1, e2, mapValue_conjCoact]
  have f1 : ((Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
      Algebra.TensorProduct.includeLeft).comp (Algebra.TensorProduct.includeLeft (S := k)
        (B := H)) = (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⊗[k] H)) := by
    ext x; simp [Algebra.TensorProduct.one_def]
  have f2 : ((Algebra.TensorProduct.assoc k k k H H H).toAlgHom.comp
      Algebra.TensorProduct.includeLeft).comp (Algebra.TensorProduct.includeRight (R := k)
        (A := H)) = (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft :
          H →ₐ[k] H ⊗[k] (H ⊗[k] H)) := by
    ext x; simp [Algebra.TensorProduct.one_def]
  have g1 : (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.comulAlgHom k H)).comp
      Algebra.TensorProduct.includeLeft =
        (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⊗[k] H)) := by
    ext x; simp [Algebra.TensorProduct.one_def]
  have g2 : (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.comulAlgHom k H)).comp
      Algebra.TensorProduct.includeRight =
        (Algebra.TensorProduct.includeRight.comp (Bialgebra.comulAlgHom k H) :
          H →ₐ[k] H ⊗[k] (H ⊗[k] H)) := by
    ext x; simp [Algebra.TensorProduct.one_def]
  rw [f1, f2, g1, g2]
  simp only [toConv_comp_eq_mapValue]
  rw [Bialgebra.comulPoint_eq_include_mul, map_mul]
  have key : ∀ {G : Type u} [Group G] (a b x : G),
      a⁻¹ * (b⁻¹ * x * b) * a = (b * a)⁻¹ * x * (b * a) := by intros; group
  exact key (G := WithConv (H →ₐ[k] H ⊗[k] (H ⊗[k] H))) _ _ _

lemma conjCoact_counit :
    (Algebra.TensorProduct.rid k k H).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H)).comp
          (conjCoact (k := k) (H := H))) = AlgHom.id k H := by
  apply WithConv.toConv_injective
  rw [← AlgHom.comp_assoc, mapValue_conjCoact]
  have e1 : ((Algebra.TensorProduct.rid k k H).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H))).comp
        Algebra.TensorProduct.includeLeft = AlgHom.id k H := by
    ext x; simp [Algebra.TensorProduct.one_def]
  have e2 : toConv (((Algebra.TensorProduct.rid k k H).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.counitAlgHom k H))).comp
        Algebra.TensorProduct.includeRight) = (1 : WithConv (H →ₐ[k] H)) := by
    rw [AlgHom.convOne_def]
    congr 1
    ext x; simp [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  rw [e1, e2]
  simp

instance conjComodule : Comodule k H (ConjH H) where
  coact := (conjCoact (k := k) (H := H)).toLinearMap
  coassoc := by
    have h := congrArg AlgHom.toLinearMap (conjCoact_coassoc (k := k) (H := H))
    exact h
  lTensor_counit_comp_coact := by
    have h := congrArg AlgHom.toLinearMap (conjCoact_counit (k := k) (H := H))
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h x
    apply (TensorProduct.rid k (ConjH H)).injective
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.flip_apply, TensorProduct.rid_tmul, one_smul]
    exact hx

/-- The coaction followed by a `k`-point `g` is `Ad g⁻¹`. -/
lemma productMap_comp_conjCoact (g : WithConv (H →ₐ[k] k)) :
    (Algebra.TensorProduct.productMap (AlgHom.id k H) ((Algebra.ofId k H).comp g.ofConv)).comp
      (conjCoact (k := k) (H := H)) = Ad g⁻¹ := by
  apply WithConv.toConv_injective
  rw [mapValue_conjCoact, Algebra.TensorProduct.productMap_left,
    Algebra.TensorProduct.productMap_right, HopfAlgebra.toConv_pointConjugationAlgHom, map_inv,
    inv_inv, toConv_comp_eq_mapValue, toConv_ofConv]

/-- **(b)** A unipotent `k`-point `g` makes `Ad g⁻¹ - 1` locally nilpotent. -/
theorem exists_pow_Ad_sub_one_eq_zero (g : WithConv (H →ₐ[k] k))
    (hg : HopfAlgebra.IsUnipotentPoint g) (y : H) :
    ∃ n : ℕ, (((Ad g⁻¹).toLinearMap - 1) ^ n) y = 0 := by
  obtain ⟨N, hNf, hyN⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H)
    (M := ConjH H) (y : ConjH H)
  have : Module.Finite k N := hNf
  obtain ⟨n, hn⟩ := (HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one _).1
    hg (FGComoduleCat.of (R := k) (C := H) N)
  refine ⟨n, ?_⟩
  let T : ConjH H →ₗ[k] ConjH H := (Ad g⁻¹).toLinearMap
  let EN : k ⊗[k] N →ₗ[k] k ⊗[k] N := endOfPoint N g.ofConv
  let EV : k ⊗[k] ConjH H →ₗ[k] k ⊗[k] ConjH H := endOfPoint (ConjH H) g.ofConv
  let ι : k ⊗[k] N →ₗ[k] k ⊗[k] ConjH H := (SMulMemClass.subtype N).baseChange k
  have h1 : ι ∘ₗ EN = EV ∘ₗ ι := baseChange_comp_endOfPoint (Subcomodule.subtype N) g.ofConv
  have L1 : ∀ t : H ⊗[k] H, TensorProduct.rid k H (LinearMap.lTensor H g.ofConv.toLinearMap t) =
      (Algebra.TensorProduct.productMap (AlgHom.id k H) ((Algebra.ofId k H).comp g.ofConv)) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.rid_tmul,
        Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, AlgHom.comp_apply,
        Algebra.ofId_apply]
      rw [Algebra.smul_def, Algebra.commutes]
  have key : ∀ t : ConjH H ⊗[k] k,
      TensorProduct.comm k (ConjH H) k t = 1 ⊗ₜ[k] (TensorProduct.rid k (ConjH H) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, TensorProduct.tmul_add]
    | tmul a b =>
      rw [TensorProduct.comm_tmul, TensorProduct.rid_tmul, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hEV : ∀ v : ConjH H, EV (1 ⊗ₜ v) = 1 ⊗ₜ[k] T v := by
    intro v
    simp only [EV, endOfPoint_tmul, one_smul]
    rw [key]
    congr 1
    have hT : T v = (Algebra.TensorProduct.productMap (AlgHom.id k H)
        ((Algebra.ofId k H).comp g.ofConv)) (conjCoact (k := k) (H := H) (show H from v)) := by
      rw [← AlgHom.comp_apply, productMap_comp_conjCoact]; rfl
    rw [hT]
    exact L1 _
  have hpowV : ∀ j : ℕ, ∀ v : ConjH H, ((EV - 1) ^ j) (1 ⊗ₜ v) =
      1 ⊗ₜ[k] (((T - 1) ^ j) v) := by
    intro j
    induction j with
    | zero => intro v; simp only [pow_zero, Module.End.one_apply]
    | succ j ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hEV,
        ← TensorProduct.tmul_sub, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply,
        Module.End.one_apply]
  have hΦ : ∀ m : ℕ, ι ∘ₗ ((EN - 1) ^ m) = ((EV - 1) ^ m) ∘ₗ ι := by
    intro m
    induction m with
    | zero => simp [Module.End.one_eq_id]
    | succ m ih =>
      have hs : ι ∘ₗ (EN - 1) = (EV - 1) ∘ₗ ι := by
        rw [LinearMap.comp_sub, LinearMap.sub_comp, h1, Module.End.one_eq_id,
          Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hs, ← LinearMap.comp_assoc]
  have hEN : (EN - 1) ^ n = 0 := hn
  have hz := congrArg (fun F => F ((1 : k) ⊗ₜ[k] (⟨y, hyN⟩ : N))) (hΦ n)
  simp only [hEN, LinearMap.comp_zero, LinearMap.zero_apply] at hz
  rw [LinearMap.comp_apply] at hz
  have hι : ι ((1 : k) ⊗ₜ[k] (⟨y, hyN⟩ : N)) = (1 : k) ⊗ₜ[k] (show ConjH H from y) := rfl
  rw [hι, hpowV] at hz
  have := congrArg (TensorProduct.lid k (ConjH H)) hz
  rw [map_zero, TensorProduct.lid_tmul, one_smul] at this
  exact this.symm

end Conj

section Cu

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Algebra.FiniteType k H]

/-- **(a)** Points of `C_u` are unipotent. -/
theorem isUnipotentPoint_of_kills_Cu (c : WithConv (H →ₐ[k] k))
    (hc : ∀ y ∈ CuIdeal π, c.ofConv y = 0) : HopfAlgebra.IsUnipotentPoint c := by
  obtain ⟨-, -, hsu⟩ :=
    FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
  have h := (smoothUnipotentCommHopfAlgProperty k).prop_of_iso (cuQuotientIso π).symm hsu
  have hpts := ((smoothUnipotentCommHopfAlgProperty_iff k _).1 h).2
  set J := (RuC π).comapOfSurjective (cMk π) (cMk_surjective π)
  have hcJ : ∀ y ∈ J, c.ofConv y = 0 := by
    intro y hy; apply hc; rw [CuIdeal_eq_comapOfSurjective]; exact hy
  let cbar : (H ⧸ J.toIdeal) →ₐ[k] k :=
    Ideal.Quotient.liftₐ J.toIdeal c.ofConv (fun a ha => hcJ a (HopfIdeal.mem_toIdeal.1 ha))
  have hg := hpts (toConv ((Algebra.ofId k (AlgebraicClosure k)).comp cbar))
  have hm := hg.mapDomain (CommHopfAlgCat.mkQuotient (CommHopfAlgCat.of k H) J).hom
  rw [← HopfAlgebra.isUnipotentPoint_mapValue_iff_of_injective c
    (Algebra.ofId k (AlgebraicClosure k)) (RingHom.injective _)]
  convert hm using 1
  apply WithConv.ofConv_injective
  ext x
  rfl

/-- **`hunip` for `C_u`.** -/
theorem hunip_CuIdeal : ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
    ∀ h : H, ∃ n : ℕ, (((Ad c).toLinearMap - 1) ^ n) h = 0 := by
  intro c hc h
  have hu := (isUnipotentPoint_of_kills_Cu π c hc).inv
  have := exists_pow_Ad_sub_one_eq_zero c⁻¹ hu h
  rwa [inv_inv] at this

/-- **`hcent` for `C_u`**, with only T4 (`hGa`) named. -/
theorem hcent_CuIdeal' [IsAlgClosed k] {ψ : X →* Multiplicative ℤ}
    (hGa : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      (∀ r ∈ rayPoints π φ α, r = 1) ∨ ∃ γ : Additive X, pairingHom φ γ ≠ 0 ∧
      ∃ y ∈ torusGrading π γ, Function.Bijective (Polynomial.aeval (R := k)
        (Ideal.Quotient.mk (rootGroupIdeal π α.1 (PosRay.torsionFree φ α)).toIdeal y))) :
    ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
        c * r = r * c :=
  hcent_CuIdeal π hGa (hunip_CuIdeal π)

end Cu

end AlgMag.Reductive
