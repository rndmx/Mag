/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Loc

/-!
# Lemma D, final bridge: helpers for the assembly

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-3. The field `κ'` as the sections of
`V'`, the point `q₀` of `𝔸(P₀)_T`, and the open `Vo` of `Z` containing the image of the closed orbit.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-- A map to an affine scheme from `Spec` of a ring is read on sections. -/
lemma SDR4_spec_ext {K₁ K₂ : Type u} [CommRing K₁] [CommRing K₂] (g : Spec (.of K₁) ⟶ Spec (.of K₂)) (ψ : K₂ →+* K₁)
    (h : ∀ a, (Scheme.ΓSpecIso (.of K₁)).hom.hom (g.appTop.hom ((Scheme.ΓSpecIso (.of K₂)).inv.hom a)) = ψ a) : g = sp ψ := by
  obtain ⟨ψ', rfl⟩ := Spec.map_surjective g
  congr 1
  ext a
  refine Eq.trans ?_ (h a)
  exact (SDR4_iso_app _ _).symm.trans (congrArg _ (appTop_sp_inv ψ'.hom a).symm)

/-- The ring map of a morphism `Spec K₁ → Spec K₂` is recovered from it. -/
lemma SDR4_sp_inj {K₁ K₂ : Type u} [CommRing K₁] [CommRing K₂] {ψ ψ' : K₂ →+* K₁} (h : sp ψ = sp ψ') : ψ = ψ' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section E

variable {Y : Scheme.{u}} {κ : Type u} [CommRing κ] (i : Y ≅ Spec (.of κ))

/-- `Γ(V') = κ'`. -/
noncomputable def SDR4_E : Γ(Y, ⊤) ≃+* κ where
  toFun x := (Scheme.ΓSpecIso (.of κ)).hom.hom (i.inv.appTop.hom x)
  invFun k := i.hom.appTop.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom k)
  left_inv x := by
    simp only []
    rw [SDR4_iso_app' κ]
    have h := congrArg (fun m : Y ⟶ Y => m.appTop.hom x) i.hom_inv_id
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
    exact h
  right_inv k := by
    simp only []
    have h := congrArg (fun m : Spec (.of κ) ⟶ Spec (.of κ) => m.appTop.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom k)) i.inv_hom_id
    simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
    have h2 : i.inv.appTop.hom (i.hom.appTop.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom k)) = (Scheme.ΓSpecIso (.of κ)).inv.hom k := h
    rw [h2]
    exact SDR4_iso_app κ k
  map_mul' x y := by simp
  map_add' x y := by simp

lemma SDR4_E_apply (x : Γ(Y, ⊤)) : SDR4_E i x = (Scheme.ΓSpecIso (.of κ)).hom.hom (i.inv.appTop.hom x) := rfl

lemma SDR4_E_symm (k : κ) : (SDR4_E i).symm k = i.hom.appTop.hom ((Scheme.ΓSpecIso (.of κ)).inv.hom k) := rfl

end E

lemma SDR4_isoSpec_inv (Y : Scheme.{u}) [IsAffine Y] (x : Γ(Y, ⊤)) :
    Y.isoSpec.inv.appTop.hom x = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv.hom x := by
  have hk : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
    have h := congrArg (fun k => k.appTop) (Scheme.toSpecΓ_isoSpec_inv Y)
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h
    exact (Iso.comp_hom_eq_id _).mp h
  rw [hk]

section Opening

/-- A compact subset of a scheme lies in a quasi-compact open. -/
lemma SDR4_exists_qc {Y : Scheme.{u}} {K : Set Y} (hK : IsCompact K) :
    ∃ O : Y.Opens, IsCompact (O : Set Y) ∧ K ⊆ O := by
  have hx : ∀ y : Y, ∃ O : Y.Opens, y ∈ O ∧ IsAffineOpen O := fun y => by
    obtain ⟨O, hO, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
    exact ⟨O, hy, hO⟩
  choose Ox hy hO using hx
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover (fun y => (Ox y : Set Y)) fun y _ => (Ox y).2.mem_nhds (hy y)
  refine ⟨⨆ y ∈ t, Ox y, ?_, ?_⟩
  · have : ((⨆ y ∈ t, Ox y : Y.Opens) : Set Y) = ⋃ y ∈ t, (Ox y : Set Y) := by
      simp
    rw [this]
    exact t.finite_toSet.isCompact_biUnion fun y _ => (hO y).isCompact
  · intro z hz
    obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.1 (ht.2 hz)
    have : ((⨆ y ∈ t, Ox y : Y.Opens) : Set Y) = ⋃ y ∈ t, (Ox y : Set Y) := by
      simp
    rw [this]
    exact Set.mem_iUnion₂.2 ⟨y, hyt, hzy⟩

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] [AddGroup.FG Λ] {W Z Orb : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- `SDR3Coact_main`, with `Vo` containing the image of a map from a quasi-compact `Orb`. -/
theorem SDR4_opening (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W) [CompactSpace ((SCH).obj Orb)]
    (lo : Orb ⟶ Z) :
    ∃ (Vo : BigFppfOver B S hS) (k : Vo ⟶ Z) (actV : AAction (fppfO B S hS) Λ (yoneda.obj Vo)) (so : Orb ⟶ Vo),
      IsOpenImmersion ((SCH).map k) ∧ so ≫ k = lo ∧
      (∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (t : T ⟶ Vo),
        actV.smul (U := op T) g t ≫ k = actZ.smul (U := op T) g (t ≫ k)) ∧
      CompactSpace ((SCH).obj Vo) ∧
      ∃ c : Coact Γ((SCH).obj Vo, ⊤) Λ, ∀ y,
        SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ (k ≫ r))).appTop.hom
            (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) (k ≫ r))) (c.σ y) =
          ((SCH).map (SDR3Coact_a actV (k ≫ r))).appTop.hom y := by
  have hK : IsCompact (Set.range ((SCH).map lo)) := isCompact_range ((SCH).map lo).continuous
  obtain ⟨U₀, hU₀, hsub⟩ := SDR4_exists_qc hK
  obtain ⟨Vo, k, actV, hk, hr, heq, hcomp, c, hc⟩ := SDR3Coact_main actZ r U₀ hU₀
  obtain ⟨so, hso⟩ := SDR4_lift k lo (hsub.trans hr)
  exact ⟨Vo, k, actV, so, hk, hso, heq, hcomp, c, hc⟩

end Opening

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_opening
#print axioms AlgMag.SD.SDR4_E
