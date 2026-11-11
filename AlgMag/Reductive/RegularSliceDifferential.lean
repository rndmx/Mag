/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The differential of the regular slice map at `(e, e, t)`

Linear algebra for C2(d) (`exists_open_regularConjugates`), part (ii).

`V = Lie K`, `f = Ad(t⁻¹)`, `W i = g_{α_i}` weight spaces on which `f` acts by the scalar
`c i = α_i(t)⁻¹`. Regularity of `t` is `c i ≠ 1` for every root `i ∈ R`. With
`A = ⨆_{i ∈ R} W i = g_R`, `Lie U⁻ ⊕ Lie U⁺ = A` (disjoint, sum `A`) and `Lie T = L₀` a
complement of `A`, the differential of `μ (u, v, s) = (uv) s (uv)⁻¹` at `(e, e, t)` (left
translated to `e`) is `(X, Y, H) ↦ (f - 1)(X + Y) + H`; it is bijective
(`sliceTangentMap_bijective`), hence so is its dual, the map on cotangent spaces
(`sliceCotangentMap_bijective`).

No independence of the `W i` is needed: `f - 1` is injective on `g_R` because `g_R` lies in the
sum of the eigenspaces of `f` with eigenvalue `≠ 1`, which is disjoint from the `1`-eigenspace.
-/

namespace AlgMag.Reductive

open Module

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]

section

variable (f : End k V) (W : ι → Submodule k V) (c : ι → k) (R : Set ι)

/-- The span of the root spaces, `g_R = ⨆_{i ∈ R} W i`. -/
def rootSpan : Submodule k V := ⨆ i ∈ R, W i

variable {f W c R}

lemma rootSpan_le_comap (hW : ∀ i, ∀ v ∈ W i, f v = c i • v) :
    rootSpan W R ≤ (rootSpan W R).comap (f - 1) := by
  refine iSup₂_le fun i hi v hv => ?_
  have hmem : v ∈ rootSpan W R := (le_iSup₂ (f := fun j (_ : j ∈ R) => W j) i hi) hv
  simp only [Submodule.mem_comap, LinearMap.sub_apply, End.one_apply, hW i v hv]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hmem) hmem

/-- `f - 1` maps `g_R` onto `g_R` (regularity). -/
lemma rootSpan_le_map (hW : ∀ i, ∀ v ∈ W i, f v = c i • v) (hc : ∀ i ∈ R, c i ≠ 1) :
    rootSpan W R ≤ (rootSpan W R).map (f - 1) := by
  refine iSup₂_le fun i hi v hv => ?_
  have hne : c i - 1 ≠ 0 := sub_ne_zero.mpr (hc i hi)
  refine ⟨(c i - 1)⁻¹ • v,
    (le_iSup₂ (f := fun j (_ : j ∈ R) => W j) i hi) (Submodule.smul_mem _ _ hv), ?_⟩
  have hv' : (c i - 1)⁻¹ • v ∈ W i := Submodule.smul_mem _ _ hv
  simp only [LinearMap.sub_apply, End.one_apply, hW i _ hv', smul_smul]
  rw [← sub_smul, ← sub_one_mul, mul_inv_cancel₀ hne, one_smul]

/-- `f - 1` is injective on `g_R` (regularity). -/
lemma eq_zero_of_mem_rootSpan (hW : ∀ i, ∀ v ∈ W i, f v = c i • v) (hc : ∀ i ∈ R, c i ≠ 1)
    {x : V} (hx : x ∈ rootSpan W R) (h0 : (f - 1) x = 0) : x = 0 := by
  have h1 : x ∈ f.eigenspace 1 := by
    rw [End.mem_eigenspace_iff, one_smul]
    simpa [sub_eq_zero] using h0
  have h2 : x ∈ ⨆ μ, ⨆ (_ : μ ≠ (1 : k)), f.eigenspace μ := by
    refine (iSup₂_le fun i hi => ?_ : rootSpan W R ≤ _) hx
    intro v hv
    refine Submodule.mem_iSup_of_mem (c i) (Submodule.mem_iSup_of_mem (hc i hi) ?_)
    rw [End.mem_eigenspace_iff]
    exact hW i v hv
  exact (Module.End.eigenspaces_iSupIndep f 1).le_bot ⟨h1, h2⟩

end

variable (f : End k V) (Um Up L₀ : Submodule k V)

/-- The differential at `(e, e, t)` of the slice map `(u, v, s) ↦ (uv) s (uv)⁻¹`:
`(X, Y, H) ↦ (Ad(t⁻¹) - 1)(X + Y) + H`. -/
noncomputable def sliceTangentMap : (Um × Up) × L₀ →ₗ[k] V :=
  ((f - 1) ∘ₗ Um.subtype.coprod Up.subtype).coprod L₀.subtype

@[simp] lemma sliceTangentMap_apply (p : (Um × Up) × L₀) :
    sliceTangentMap f Um Up L₀ p = (f - 1) ((p.1.1 : V) + p.1.2) + p.2 := rfl

variable {f Um Up L₀} {W : ι → Submodule k V} {c : ι → k} {R : Set ι}

/-- **Part (ii) of C2(d).** For `t` regular, `Lie U⁻ ⊕ Lie U⁺ ⊕ Lie T → Lie K`,
`(X, Y, H) ↦ (Ad(t⁻¹) - 1)(X + Y) + H`, is bijective. -/
theorem sliceTangentMap_bijective (hW : ∀ i, ∀ v ∈ W i, f v = c i • v)
    (hc : ∀ i ∈ R, c i ≠ 1) (hU : Um ⊔ Up = rootSpan W R) (hUd : Disjoint Um Up)
    (hL : IsCompl (rootSpan W R) L₀) :
    Function.Bijective (sliceTangentMap f Um Up L₀) := by
  have hUmA : Um ≤ rootSpan W R := hU ▸ le_sup_left
  have hUpA : Up ≤ rootSpan W R := hU ▸ le_sup_right
  have hmap := rootSpan_le_comap hW (R := R)
  constructor
  · intro p q hpq
    simp only [sliceTangentMap_apply] at hpq
    set a : V := ((p.1.1 : V) + p.1.2) - ((q.1.1 : V) + q.1.2) with ha_def
    have ha : a ∈ rootSpan W R :=
      Submodule.sub_mem _ (Submodule.add_mem _ (hUmA p.1.1.2) (hUpA p.1.2.2))
        (Submodule.add_mem _ (hUmA q.1.1.2) (hUpA q.1.2.2))
    have hfa : (f - 1) a ∈ rootSpan W R := hmap ha
    have heq : (f - 1) a = (q.2 : V) - p.2 := by
      rw [ha_def, map_sub, sub_eq_sub_iff_add_eq_add, hpq, add_comm]
    have hb : (q.2 : V) - p.2 ∈ L₀ := Submodule.sub_mem _ q.2.2 p.2.2
    have hz : (f - 1) a = 0 := hL.disjoint.le_bot ⟨hfa, heq ▸ hb⟩
    have ha0 : a = 0 := eq_zero_of_mem_rootSpan hW hc ha hz
    have h2 : (p.2 : V) = q.2 := by
      rw [hz] at heq; exact (sub_eq_zero.mp heq.symm).symm
    have hx : (p.1.1 : V) - q.1.1 = (q.1.2 : V) - p.1.2 := by
      have h := ha0
      rw [ha_def, sub_eq_zero] at h
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    have hx0 : (p.1.1 : V) - q.1.1 = 0 :=
      hUd.le_bot ⟨Submodule.sub_mem _ p.1.1.2 q.1.1.2,
        hx ▸ Submodule.sub_mem _ q.1.2.2 p.1.2.2⟩
    have hy0 : (q.1.2 : V) - p.1.2 = 0 := hx ▸ hx0
    refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext h2)
    · exact Subtype.ext (sub_eq_zero.mp hx0)
    · exact Subtype.ext (sub_eq_zero.mp hy0).symm
  · intro v
    have hv : v ∈ rootSpan W R ⊔ L₀ := hL.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨a₀, ha₀, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, ha, hfa⟩ := rootSpan_le_map hW hc ha₀
    rw [← hU] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
    exact ⟨((⟨x, hx⟩, ⟨y, hy⟩), ⟨b, hb⟩), by simp [hfa]⟩

/-- **Cotangent form.** The induced map on cotangent spaces (the dual of the differential)
`Lie K* → (Lie U⁻ ⊕ Lie U⁺ ⊕ Lie T)*` is bijective. -/
theorem sliceCotangentMap_bijective (hW : ∀ i, ∀ v ∈ W i, f v = c i • v)
    (hc : ∀ i ∈ R, c i ≠ 1) (hU : Um ⊔ Up = rootSpan W R) (hUd : Disjoint Um Up)
    (hL : IsCompl (rootSpan W R) L₀) :
    Function.Bijective (sliceTangentMap f Um Up L₀).dualMap :=
  (LinearEquiv.ofBijective _ (sliceTangentMap_bijective hW hc hU hUd hL)).dualMap.bijective

end AlgMag.Reductive
