/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Conj69DoubledAlg

set_option linter.style.haveILetI false

/-!
# The scheme step for the plane with doubled origin

`ι₁ : A² → S` an open immersion, `O` an affine open of `S` meeting the chart exactly in the punctured plane. A flat
`g : W → A²` with `W → S` affine misses the origin.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace

universe u

namespace AlgMag.Conj69

variable {k : Type u} [Field k]

/-- The plane over `k`. -/
noncomputable abbrev Pl (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of (A2 k))

/-- A point of the plane at which `x`, `y` vanish. -/
def VanishesXY (z : Pl k) : Prop := X 0 ∈ z.asIdeal ∧ X 1 ∈ z.asIdeal

lemma mem_basicOpen_appTop {W : Scheme.{u}} (g : W ⟶ Pl k) (a : A2 k) (v : W) :
    v ∈ W.basicOpen (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (A2 k))).inv a)) ↔
      a ∉ (g v).asIdeal := by
  have h := Scheme.preimage_basicOpen g ((Scheme.ΓSpecIso (CommRingCat.of (A2 k))).inv a)
  have h2 : v ∈ g ⁻¹ᵁ (Pl k).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (A2 k))).inv a) ↔
      a ∉ (g v).asIdeal := by
    rw [basicOpen_eq_of_affine]; exact Iff.rfl
  rw [← h2, h]; rfl

/-- Restriction of sections. -/
noncomputable def rr {W : Scheme.{u}} {U V : W.Opens} (h : V ≤ U) : Γ(W, U) →+* Γ(W, V) :=
  (W.presheaf.map (homOfLE h).op).hom

lemma rr_rr {W : Scheme.{u}} {U V D : W.Opens} (h : V ≤ U) (h' : D ≤ V) (s : Γ(W, U)) :
    rr h' (rr h s) = rr (h'.trans h) s := by
  simp only [rr, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Let `ι₁ : 𝔸² → S` be an open immersion and `O` an affine open of `S` whose preimage is the punctured plane. A flat
`g : W → 𝔸²` with `g ≫ ι₁` affine has no point over the origin. -/
theorem no_chart_core {S : Scheme.{u}} (ι₁ : Pl k ⟶ S) [IsOpenImmersion ι₁]
    (O : S.Opens) (hO : IsAffineOpen O) (hι : ∀ z : Pl k, ι₁ z ∈ O ↔ ¬ VanishesXY z)
    {W : Scheme.{u}} (g : W ⟶ Pl k) [Flat g] [IsAffineHom (g ≫ ι₁)] (w : W)
    (hw : VanishesXY (g w)) : False := by
  have hrange : IsAffineOpen ι₁.opensRange := isAffineOpen_opensRange ι₁
  have htop : (g ≫ ι₁) ⁻¹ᵁ ι₁.opensRange = ⊤ := by
    ext v; simp
  have hWtop : IsAffineOpen (⊤ : W.Opens) := by
    have := IsAffineHom.isAffine_preimage (f := g ≫ ι₁) _ hrange
    rwa [htop] at this
  haveI : IsAffine (⊤ : W.Opens).toScheme := hWtop
  haveI : IsAffine W := IsAffine.of_isIso W.topIso.inv
  have hW' : IsAffineOpen ((g ≫ ι₁) ⁻¹ᵁ O) := IsAffineHom.isAffine_preimage _ hO
  let φ : A2 k →+* Γ(W, ⊤) :=
    g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (A2 k))).inv.hom
  have hφ : φ.Flat := by
    have h1 : g.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 inferInstance
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (A2 k))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact RingHom.Flat.comp h2 h1
  have hb : ∀ (a : A2 k) (v : W), v ∈ W.basicOpen (φ a) ↔ a ∉ (g v).asIdeal :=
    mem_basicOpen_appTop g
  set xx := φ (X 0) with hxx
  set yy := φ (X 1) with hyy
  set W' := (g ≫ ι₁) ⁻¹ᵁ O with hW'd
  have hcov : ∀ v, v ∈ W' ↔ v ∈ W.basicOpen xx ∨ v ∈ W.basicOpen yy := by
    intro v
    have : v ∈ W' ↔ ι₁ (g v) ∈ O := by simp [W']
    rw [this, hι, hb, hb, VanishesXY]
    tauto
  have hxW : W.basicOpen xx ≤ W' := fun v hv => (hcov v).2 (Or.inl hv)
  have hyW : W.basicOpen yy ≤ W' := fun v hv => (hcov v).2 (Or.inr hv)
  have htW : W' ≤ ⊤ := le_top
  -- `x, y` generate the unit ideal on the affine `W'`
  have hspan : Ideal.span ({rr htW xx, rr htW yy} : Set Γ(W, W')) = ⊤ := by
    refine hW'.self_le_iSup_basicOpen_iff.1 fun v hv => ?_
    have hres : ∀ s : Γ(W, ⊤), v ∈ W.basicOpen s → v ∈ W.basicOpen (rr htW s) := fun s hs => by
      have : W.basicOpen (rr htW s) = W' ⊓ W.basicOpen s := Scheme.basicOpen_res W s (homOfLE htW).op
      rw [this]; exact ⟨hv, hs⟩
    rcases (hcov v).1 hv with h | h
    · exact Opens.mem_iSup.2 ⟨⟨_, Set.mem_insert _ _⟩, hres _ h⟩
    · exact Opens.mem_iSup.2 ⟨⟨_, Set.mem_insert_of_mem _ rfl⟩, hres _ h⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (hspan ▸ Submodule.mem_top : (1 : Γ(W, W')) ∈ _)
  obtain ⟨m, b, hbm⟩ := exists_eq_pow_mul_of_isAffineOpen W ⊤ hWtop yy (rr hyW α)
  obtain ⟨n, a, han⟩ := exists_eq_pow_mul_of_isAffineOpen W ⊤ hWtop xx (rr hxW β)
  have hbm' : rr (W.basicOpen_le yy) b = rr (W.basicOpen_le yy) yy ^ m * rr hyW α := hbm
  have han' : rr (W.basicOpen_le xx) a = rr (W.basicOpen_le xx) xx ^ n * rr hxW β := han
  have hDx : W.basicOpen (xx * yy) ≤ W.basicOpen xx := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hDy : W.basicOpen (xx * yy) ≤ W.basicOpen yy := by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  have hDW := hDx.trans hxW
  have hDt : W.basicOpen (xx * yy) ≤ ⊤ := le_top
  have rb := congrArg (rr hDy) hbm'
  have ra := congrArg (rr hDx) han'
  simp only [map_mul, map_pow, rr_rr] at rb ra
  have r1 := congrArg (rr hDW) hαβ
  simp only [map_add, map_mul, map_one, rr_rr] at r1
  have key : (xx ^ n * yy ^ m - xx ^ (n + 1) * b - yy ^ (m + 1) * a) |_ W.basicOpen (xx * yy) = 0 := by
    change rr hDt _ = 0
    simp only [map_sub, map_mul, map_pow]
    rw [ra, rb]
    linear_combination (-(rr hDt xx ^ n * rr hDt yy ^ m)) * r1
  obtain ⟨K, hK⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen W hWtop _ _ key
  let q : Ideal Γ(W, ⊤) :=
    (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).comap (W.presheaf.germ ⊤ w trivial).hom
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  have hq : ∀ c : A2 k, c ∈ (g w).asIdeal → φ c ∈ q := fun c hc => by
    have h1 : w ∉ W.basicOpen (φ c) := fun h => (hb c w).1 h hc
    rw [Scheme.mem_basicOpen_top] at h1
    exact h1
  exact no_relation φ hφ q (hq _ hw.1) (hq _ hw.2) hK

end AlgMag.Conj69
