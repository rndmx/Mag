/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSlice
import AlgMag.Reductive.PointDerivationsSlice
import AlgMag.Reductive.RootGroupGaLie
import AlgMag.Reductive.RegularSliceDifferential
import TauCeti.Algebra.AlgebraicGroup.Tangent.Conjugation

/-!
# The hypotheses of `sliceTangentMap_bijective` in the actual setting (C2(d), part (a))

`V = Lie K = Lie G^N`, `f = Ad(t₀⁻¹)` (restricted), `W α = 𝔤_α ∩ Lie K`, `c α = α(t₀)⁻¹`,
`R = Φ ∩ N`, `U^± = Lie U^±`, `L₀ = 𝔤_0`. Main: `sliceTangentMap_bijective_K`.
-/

suppress_compilation

open Magnetism TauCeti TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable {π : H →ₐc[k] MonoidAlgebra k X}

local notation "LieG" => Derivation k H (Bialgebra.CounitAlgebra k H k)
local notation "ev" => Bialgebra.CounitAlgebra.algEquivSelf k H k

section Generic

variable (π) in
/-- Tangent vectors agreeing on every weight space are equal. -/
lemma der_ext_graded {d e : LieG} (h : ∀ χ, ∀ x ∈ torusGrading π χ, d x = e x) : d = e := by
  ext x
  have hx : x ∈ ⨆ χ, torusGrading π χ := by
    rw [(isInternal_torusGrading π).submodule_iSup_eq_top]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem χ y hy => exact h χ y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]

variable {τ : MonoidAlgebra k X →ₐ[k] k} {g : WithConv (H →ₐ[k] Bialgebra.CounitAlgebra k H k)}

omit [DecidableEq X] in
/-- **`Ad(t)` on a weight vector of `O(G)`**: `(Ad t d)(h) = χ(t) d(h)` for `h ∈ H_χ`. -/
lemma adDerivation_apply_of_mem (hg : ∀ x, ev (g.ofConv x) = τ (π x)) (d : LieG) {χ : Additive X}
    {x : H} (hx : x ∈ torusGrading π χ) :
    ev (Derivation.adDerivation k g d x) = τ (MonoidAlgebra.single (Additive.toMul χ) 1) * ev (d x) := by
  rw [Derivation.adDerivation_eq_lift_conjugationAlgHom]
  have hlift : ∀ z : H ⊗[k] H,
      TensorProduct.lift ((LinearMap.mul k (Bialgebra.CounitAlgebra k H k)).compl₁₂
        g.ofConv.toLinearMap d.toLinearMap) z =
      TensorProduct.lift ((LinearMap.mul k (Bialgebra.CounitAlgebra k H k)).compl₁₂
        (((ev).symm.toAlgHom.comp τ).toLinearMap) d.toLinearMap)
        (Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | tmul a b =>
      simp only [TensorProduct.lift.tmul, Algebra.TensorProduct.map_tmul,
        LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply, AlgHom.comp_apply,
        LinearMap.mul_apply']
      congr 1
      apply (ev).injective
      rw [hg, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      rfl
  have hc : Algebra.TensorProduct.map π.toAlgHom (AlgHom.id k H)
      (HopfAlgebra.conjugationAlgHom (R := k) (H := H) x) = torusCoactLeft π x := rfl
  rw [hlift, hc, torusCoactLeft_of_mem hx, TensorProduct.lift.tmul]
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, map_mul, AlgEquiv.apply_symm_apply]
  rfl

omit [DecidableEq X] in
lemma torus_single_ne_zero (χ : Additive X) : τ (MonoidAlgebra.single (Additive.toMul χ) 1) ≠ 0 := by
  intro h0
  have h1 : τ (MonoidAlgebra.single (Additive.toMul χ) 1 *
      MonoidAlgebra.single (Additive.toMul χ)⁻¹ 1) = 1 := by
    rw [MonoidAlgebra.single_mul_single, mul_inv_cancel, one_mul, ← MonoidAlgebra.one_def, map_one]
  rw [map_mul, h0, zero_mul] at h1
  exact zero_ne_one h1

/-- **`Ad(t⁻¹)` on a weight vector**: `(Ad t⁻¹ d)(h) = χ(t)⁻¹ d(h)` for `h ∈ H_χ`. -/
lemma adRepresentation_inv_apply_of_mem (hg : ∀ x, ev (g.ofConv x) = τ (π x)) (d : LieG)
    {χ : Additive X} {x : H} (hx : x ∈ torusGrading π χ) :
    ev (Derivation.adRepresentation k g⁻¹ d x) =
      (τ (MonoidAlgebra.single (Additive.toMul χ) 1))⁻¹ * ev (d x) := by
  have hd : Derivation.adRepresentation k g (Derivation.adRepresentation k g⁻¹ d) = d := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := adDerivation_apply_of_mem hg (Derivation.adRepresentation k g⁻¹ d) hx
  rw [← Derivation.adRepresentation_apply, hd] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ (torus_single_ne_zero χ), one_mul]

end Generic

section Decomp

variable (π) in
/-- Tangent vectors vanishing on every `H_χ`, `χ ∉ S`. -/
def vanishOff (S : Set (Additive X)) : Submodule k LieG where
  carrier := {d | ∀ χ ∉ S, ∀ x ∈ torusGrading π χ, d x = 0}
  add_mem' {d e} hd he χ hχ x hx := by
    rw [Derivation.add_apply, hd χ hχ x hx, he χ hχ x hx, add_zero]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c d hd χ hχ x hx := by rw [Derivation.smul_apply, hd χ hχ x hx]; exact smul_zero c

lemma rootSpace_eq_vanishOff (α : Additive X) : rootSpace π α = vanishOff π {α} := by
  ext d; exact ⟨fun h χ hχ => h χ hχ, fun h χ hχ => h χ hχ⟩

lemma vanishOff_mono {S T : Set (Additive X)} (h : S ⊆ T) : vanishOff π S ≤ vanishOff π T :=
  fun _ hd χ hχ => hd χ (fun h' => hχ (h h'))

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule in
variable (π) in
lemma iSup_rootSpace : ⨆ α, rootSpace π α = ⊤ := by
  rw [eq_top_iff]
  rintro d -
  obtain ⟨x, rfl⟩ := (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).surjective d
  have htop : ⨆ β, Derivation.adjointWeightSpace π β = ⊤ := by
    letI : DecidableEq X := Classical.decEq X
    exact (Derivation.isInternal_adjointWeightSpace π).submodule_iSup_eq_top
  have hx : x ∈ ⨆ β, Derivation.adjointWeightSpace π β := by rw [htop]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem β y hy =>
    exact Submodule.mem_iSup_of_mem (Additive.ofMul β) (fun χ hχ h hh =>
      cotangentLinearEquiv_eq_zero_of_mem_adjointWeightSpace hy
        (fun e => hχ (by rw [← e]; rfl)) hh)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz

variable (π) in
/-- **Weight decomposition of `Lie G`**: `⊕_{α ∈ S} 𝔤_α` = vectors vanishing off `S`. -/
theorem iSup_rootSpace_eq (S : Set (Additive X)) :
    (⨆ α ∈ S, rootSpace π α) = vanishOff π S := by
  classical
  apply le_antisymm
  · exact iSup₂_le fun α hα d hd χ hχ x hx => hd χ (fun e => hχ (e ▸ hα)) x hx
  intro d hS
  have hd : d ∈ ⨆ α, rootSpace π α := by rw [iSup_rootSpace]; trivial
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ d).1 hd
  have heval : ∀ χ, ∀ x ∈ torusGrading π χ, d x = f χ x := by
    intro χ x hx
    let E : LieG →ₗ[k] Bialgebra.CounitAlgebra k H k :=
      { toFun := fun d => d x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    change E d = E (f χ)
    rw [← hsum, Finsupp.sum, map_sum]
    refine Finset.sum_eq_single χ (fun b _ hb => hf b χ (Ne.symm hb) x hx) (fun h => ?_)
    rw [Finsupp.notMem_support_iff.1 h, map_zero]
  rw [← hsum]
  refine Submodule.sum_mem _ fun α _ => ?_
  by_cases hα : α ∈ S
  · exact Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hα (hf α))
  · have h0 : f α = 0 := der_ext_graded π fun χ x hx => by
      by_cases hχ : χ = α
      · subst hχ; rw [← heval _ _ hx, hS _ hα _ hx]; rfl
      · rw [hf α χ hχ x hx]; rfl
    rw [h0]; exact zero_mem _

end Decomp

section SliceK

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable (π) (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)

/-- `Lie K = Lie G^N` as a submodule of `Lie G`. -/
abbrev LK : Submodule k LieG := ((magnetHopfIdeal π N).lieSubalgebra (B := k)).toSubmodule

/-- `W α = 𝔤_α ∩ Lie K`. -/
abbrev WK (α : Additive X) : Submodule k (LK π N) := (rootSpace π α).comap (LK π N).subtype

/-- `R = Φ ∩ N`. -/
def RK : Set (Additive X) := {α | α ∈ roots π ∧ α ∈ N}

/-- `Lie U^±` inside `Lie K` (`U⁺ = UK ψ`, `U⁻ = UK ψ⁻¹`). -/
abbrev UK : Submodule k (LK π N) :=
  ((sliceIdeal π N ψ).lieSubalgebra (B := k)).toSubmodule.comap (LK π N).subtype

/-- `L₀ = 𝔤_0 ∩ Lie K`. -/
abbrev L0K : Submodule k (LK π N) := WK π N 0

/-- `c α = α(t₀)⁻¹`. -/
def cK (τ : MonoidAlgebra k X →ₐ[k] k) (α : Additive X) : k :=
  (τ (MonoidAlgebra.single (Additive.toMul α) 1))⁻¹

variable {π N ψ}

lemma LK_eq : LK π N = vanishOff π N := by
  ext d; exact mem_lieSubalgebra_magnetHopfIdeal_iff (B := k) N d

lemma UK_val_eq (ψ : X →* Multiplicative ℤ) :
    ((sliceIdeal π N ψ).lieSubalgebra (B := k)).toSubmodule =
      vanishOff π (sliceRoots π N ψ) := by
  ext d; exact mem_lieSubalgebra_sliceIdeal_iff π N ψ d

lemma mem_V_iff (P : Submodule k (LK π N)) (v : LK π N) :
    v ∈ P ↔ (v : LieG) ∈ P.map (LK π N).subtype :=
  ⟨fun h => ⟨v, h, rfl⟩, fun ⟨y, hy, e⟩ => (Subtype.ext e : y = v) ▸ hy⟩

lemma map_comap_LK {P : Submodule k LieG} (h : P ≤ LK π N) :
    (P.comap (LK π N).subtype).map (LK π N).subtype = P := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr h]

lemma roots_ne_zero {α : Additive X} (h : α ∈ roots π) : α ≠ 0 :=
  fun e => h.1 (by rw [e]; rfl)

lemma map_rootSpan_WK :
    (rootSpan (WK π N) (RK π N)).map (LK π N).subtype = vanishOff π (RK π N) := by
  rw [rootSpan, Submodule.map_iSup]
  simp_rw [Submodule.map_iSup]
  rw [← iSup_rootSpace_eq]
  refine iSup_congr fun α => iSup_congr fun hα => map_comap_LK ?_
  rw [LK_eq, rootSpace_eq_vanishOff]
  exact vanishOff_mono (Set.singleton_subset_iff.2 hα.2)

variable {τ : MonoidAlgebra k X →ₐ[k] k} {g : WithConv (H →ₐ[k] Bialgebra.CounitAlgebra k H k)}

lemma adInv_mem_vanishOff (hg : ∀ x, ev (g.ofConv x) = τ (π x)) {S : Set (Additive X)}
    {d : LieG} (hd : d ∈ vanishOff π S) :
    Derivation.adRepresentation k g⁻¹ d ∈ vanishOff π S := by
  intro χ hχ x hx
  apply (ev).injective
  rw [adRepresentation_inv_apply_of_mem hg d hx, hd χ hχ x hx, map_zero, mul_zero]

variable (N) in
/-- `Ad(t₀⁻¹)` restricted to `Lie K`. -/
def adInvK (hg : ∀ x, ev (g.ofConv x) = τ (π x)) : Module.End k (LK π N) :=
  (Derivation.adRepresentation k g⁻¹).restrict (p := LK π N) (q := LK π N) fun d hd => by
    rw [LK_eq] at hd ⊢; exact adInv_mem_vanishOff hg hd

theorem hW_K (hg : ∀ x, ev (g.ofConv x) = τ (π x)) :
    ∀ α, ∀ v ∈ WK π N α, adInvK N hg v = cK τ α • v := by
  intro α v hv
  apply Subtype.ext
  change Derivation.adRepresentation k g⁻¹ (v : LieG) = cK τ α • (v : LieG)
  refine der_ext_graded π fun χ x hx => (ev).injective ?_
  rw [adRepresentation_inv_apply_of_mem hg _ hx]
  change _ = cK τ α * ev ((v : LieG) x)
  by_cases hχ : χ = α
  · subst hχ; rfl
  · rw [show (v : LieG) x = 0 from hv χ hχ x hx, map_zero, mul_zero, mul_zero]

theorem hc_K (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1) :
    ∀ α ∈ RK π N, cK τ α ≠ 1 :=
  fun α hα h => hτ α hα.1 hα.2 (inv_eq_one.mp h)

theorem hU_K (hψ : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0) :
    UK π N ψ⁻¹ ⊔ UK π N ψ = rootSpan (WK π N) (RK π N) := by
  apply Submodule.map_injective_of_injective (LK π N).injective_subtype
  have hle : ∀ ψ' : X →* Multiplicative ℤ,
      ((sliceIdeal π N ψ').lieSubalgebra (B := k)).toSubmodule ≤ LK π N := fun ψ' => by
    rw [UK_val_eq, LK_eq]; exact vanishOff_mono fun α h => h.2.1
  have hset : sliceRoots π N ψ⁻¹ ∪ sliceRoots π N ψ = RK π N := by
    ext α
    simp only [Set.mem_union, sliceRoots, RK, Set.mem_ofPred_eq, pairingHom_inv]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne (hψ α ⟨h1, h2⟩) with h | h
      · exact Or.inl ⟨h1, h2, by omega⟩
      · exact Or.inr ⟨h1, h2, h⟩
  rw [Submodule.map_sup, map_comap_LK (hle _), map_comap_LK (hle _), map_rootSpan_WK,
    UK_val_eq, UK_val_eq, ← hset, ← iSup_rootSpace_eq, ← iSup_rootSpace_eq, ← iSup_rootSpace_eq,
    iSup_union]

theorem hUd_K : Disjoint (UK π N ψ⁻¹) (UK π N ψ) := by
  rw [Submodule.disjoint_def]
  intro v h1 h2
  have h1' : (v : LieG) ∈ vanishOff π (sliceRoots π N ψ⁻¹) := by rw [← UK_val_eq]; exact h1
  have h2' : (v : LieG) ∈ vanishOff π (sliceRoots π N ψ) := by rw [← UK_val_eq]; exact h2
  refine Subtype.ext (der_ext_graded π fun χ x hx => ?_)
  by_cases h : χ ∈ sliceRoots π N ψ
  · refine (h1' χ (fun h' => ?_) x hx).trans rfl
    have a1 := h.2.2
    have a2 := h'.2.2
    simp only [pairingHom_inv] at a2
    omega
  · exact (h2' χ h x hx).trans rfl

theorem hL_K : IsCompl (rootSpan (WK π N) (RK π N)) (L0K π N) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [mem_V_iff, map_rootSpan_WK] at h1
    refine Subtype.ext (der_ext_graded π fun χ x hx => ?_)
    by_cases h : χ = 0
    · subst h; exact (h1 0 (fun h' => roots_ne_zero h'.1 rfl) x hx).trans rfl
    · exact (h2 χ h x hx).trans rfl
  · rw [codisjoint_iff, eq_top_iff]
    rintro v -
    have hvN : (v : LieG) ∈ vanishOff π N := by rw [← LK_eq]; exact v.2
    have hv : (v : LieG) ∈ vanishOff π (RK π N ∪ {0}) := by
      intro χ hχ x hx
      by_cases hN : χ ∈ N
      · by_contra hne
        have hW : χ ∈ tangentWeights π k := ⟨v, x, hx, hne⟩
        rcases tangentWeights_subset_insert_roots hW with h0 | hr
        · exact hχ (Or.inr h0)
        · exact hχ (Or.inl ⟨hr, hN⟩)
      · exact hvN χ hN x hx
    rw [← iSup_rootSpace_eq, iSup_union, iSup_rootSpace_eq, iSup_singleton] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv
    have haK : a ∈ LK π N := by
      rw [LK_eq]; exact vanishOff_mono (fun α h => h.2) ha
    have hbK : b ∈ LK π N := by
      rw [LK_eq]
      rw [rootSpace_eq_vanishOff] at hb
      exact vanishOff_mono (Set.singleton_subset_iff.2 N.zero_mem) hb
    have hv' : v = ⟨a, haK⟩ + ⟨b, hbK⟩ := Subtype.ext hab.symm
    rw [hv']
    refine Submodule.add_mem_sup ?_ hb
    rw [mem_V_iff, map_rootSpan_WK]; exact ha

/-- **The slice differential is bijective** in the actual setting (`t₀ = τ ∘ π` regular, `ψ`
generic on `Φ ∩ N`). -/
theorem sliceTangentMap_bijective_K (hg : ∀ x, ev (g.ofConv x) = τ (π x))
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1)
    (hψ : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0) :
    Function.Bijective (sliceTangentMap (adInvK N hg) (UK π N ψ⁻¹) (UK π N ψ) (L0K π N)) :=
  sliceTangentMap_bijective (hW_K hg) (hc_K hτ) (hU_K hψ) hUd_K hL_K

end SliceK

section SliceG

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {N : Magnet (Additive X)} {ψ : X →* Multiplicative ℤ}
variable {τ : MonoidAlgebra k X →ₐ[k] k} {g : WithConv (H →ₐ[k] Bialgebra.CounitAlgebra k H k)}

lemma sliceLie_le_LK (ψ' : X →* Multiplicative ℤ) :
    ((sliceIdeal π N ψ').lieSubalgebra (B := k)).toSubmodule ≤ LK π N := by
  rw [UK_val_eq, LK_eq]; exact vanishOff_mono fun α h => h.2.1

lemma rootSpace_zero_le_LK : rootSpace π 0 ≤ LK π N := by
  rw [LK_eq, rootSpace_eq_vanishOff]
  exact vanishOff_mono (Set.singleton_subset_iff.2 N.zero_mem)

variable (π N) in
/-- `Lie U^±` as a submodule of `Lie G` (= `lieSlice`). -/
abbrev USub (ψ' : X →* Multiplicative ℤ) : Submodule k LieG :=
  ((sliceIdeal π N ψ').lieSubalgebra (B := k)).toSubmodule

/-- A point of `Lie U⁻ × Lie U⁺ × 𝔤_0` seen inside `Lie K`. -/
def toK (p : ((USub π N ψ⁻¹) × (USub π N ψ)) × rootSpace π 0) : (UK π N ψ⁻¹ × UK π N ψ) × L0K π N :=
  ((⟨⟨p.1.1, sliceLie_le_LK _ p.1.1.2⟩, p.1.1.2⟩, ⟨⟨p.1.2, sliceLie_le_LK _ p.1.2.2⟩, p.1.2.2⟩),
    ⟨⟨p.2, rootSpace_zero_le_LK p.2.2⟩, p.2.2⟩)

lemma sliceTangentMap_eq_K (hg : ∀ x, ev (g.ofConv x) = τ (π x))
    (p : ((USub π N ψ⁻¹) × (USub π N ψ)) × rootSpace π 0) :
    sliceTangentMap (Derivation.adRepresentation k g⁻¹) (USub π N ψ⁻¹) (USub π N ψ) (rootSpace π 0) p =
      (sliceTangentMap (adInvK N hg) (UK π N ψ⁻¹) (UK π N ψ) (L0K π N) (toK p) : LieG) := by
  simp only [sliceTangentMap_apply, toK, Submodule.coe_add, LinearMap.sub_apply,
    Module.End.one_apply, adInvK, LinearMap.restrict_apply, Submodule.coe_sub]

/-- **Injectivity on `Lie G`.** -/
theorem sliceTangentMap_injective_G (hg : ∀ x, ev (g.ofConv x) = τ (π x))
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1)
    (hψ : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0) :
    Function.Injective
      (sliceTangentMap (Derivation.adRepresentation k g⁻¹) (USub π N ψ⁻¹) (USub π N ψ) (rootSpace π 0)) := by
  intro p q hpq
  rw [sliceTangentMap_eq_K hg, sliceTangentMap_eq_K hg] at hpq
  have h := (sliceTangentMap_bijective_K hg hτ hψ).1 (Subtype.ext hpq)
  simp only [toK, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Prod.ext (Prod.ext (Subtype.ext (congrArg (fun z => z.1.1) h1))
    (Subtype.ext (congrArg (fun z => z.1.1) h2))) (Subtype.ext (congrArg (fun z => z.1.1) h3))

/-- **Range on `Lie G` is `Lie K`.** -/
theorem range_sliceTangentMap_G (hg : ∀ x, ev (g.ofConv x) = τ (π x))
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1)
    (hψ : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0) :
    LinearMap.range (sliceTangentMap (Derivation.adRepresentation k g⁻¹) (USub π N ψ⁻¹) (USub π N ψ) (rootSpace π 0)) =
      LK π N := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    rw [sliceTangentMap_eq_K hg]; exact Subtype.property _
  · intro v hv
    obtain ⟨q, hq⟩ := (sliceTangentMap_bijective_K hg hτ hψ).2 ⟨v, hv⟩
    refine ⟨((⟨q.1.1.1, q.1.1.2⟩, ⟨q.1.2.1, q.1.2.2⟩), ⟨q.2.1, q.2.2⟩), ?_⟩
    rw [sliceTangentMap_eq_K hg]
    exact congrArg Subtype.val hq

end SliceG

section CompIdeal

variable [IsAlgClosed k] [Algebra.FiniteType k H]

variable (π) in
/-- `Lie (G^N)° = Lie G^N`: derivations vanishing on `compIdeal π N`. -/
theorem vanishingDer_compIdeal (N : Magnet (Additive X)) :
    vanishingDer k H (compIdeal π N) = LK π N := by
  ext d
  constructor
  · intro hd
    change d ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k)
    rw [HopfIdeal.mem_lieSubalgebra_iff]
    intro x hx
    apply hd
    rw [compIdeal, RingHom.mem_ker]
    change Ideal.Quotient.mk (attrComp π N).toIdeal (Ideal.Quotient.mk _ x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  · intro hd x hx
    have hd' : d ∈ (derivationCompLieHom (B := k) (compMk π N)).range := by
      rw [range_derivationComp_compMk]; exact hd
    obtain ⟨e, rfl⟩ := hd'
    apply (ev).injective
    show ev (derivationComp (B := k) (compMk π N) e x) = _
    rw [algEquivSelf_derivationComp_apply]
    have hx0 : (compMk π N : H →ₐ[k] compAlg π N) x = 0 := hx
    rw [hx0, map_zero, map_zero, map_zero]

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable {N : Magnet (Additive X)} {ψ : X →* Multiplicative ℤ}
variable {τ : MonoidAlgebra k X →ₐ[k] k} {g : WithConv (H →ₐ[k] Bialgebra.CounitAlgebra k H k)}

/-- **Range on `Lie G` = `Lie K` = `vanishingDer (compIdeal π N)`.** -/
theorem range_sliceTangentMap_G_eq_vanishingDer (hg : ∀ x, ev (g.ofConv x) = τ (π x))
    (hτ : ∀ α ∈ roots π, α ∈ N → τ (MonoidAlgebra.single (Additive.toMul α) 1) ≠ 1)
    (hψ : ∀ α ∈ RK π N, pairingHom ψ α ≠ 0) :
    LinearMap.range (sliceTangentMap (Derivation.adRepresentation k g⁻¹)
      ((sliceIdeal π N ψ⁻¹).lieSubalgebra (B := k)).toSubmodule
      ((sliceIdeal π N ψ).lieSubalgebra (B := k)).toSubmodule (rootSpace π 0)) =
      vanishingDer k H (compIdeal π N) := by
  rw [vanishingDer_compIdeal]; exact range_sliceTangentMap_G hg hτ hψ

end CompIdeal

end AlgMag.Reductive
