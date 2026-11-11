/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputA

/-!
# Chart lemma, Artin approximation step (étaleness): `eA` for all `j`, and compatibility modulo `𝔫²`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V T P : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Rings with a unit ideal to the power `0`. -/
noncomputable def zeroEquiv {R C : Type*} [CommRing R] [CommRing C] (I : Ideal R) (J : Ideal C) :
    (R ⧸ I ^ 0) ≃+* (C ⧸ J ^ 0) :=
  haveI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
  haveI : Subsingleton (C ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
  { toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => Subsingleton.elim _ _
    map_add' := fun _ _ => Subsingleton.elim _ _ }

lemma kill_pow {P T : BigFppfOver B S hS} (u : P ⟶ T) (j : ℕ) (hj : 1 ≤ j) (c) (hc : c ∈ kerI u ^ j) :
    ((SCH).map u).appTop.hom c = 0 :=
  Ideal.pow_le_self (by omega) hc

section Pkg

variable {e : yoneda.obj V ⟶ X} (he : EtP e) (φ : yoneda.obj T ⟶ X) {k : Type u} [Field k]
  (iso : (BigFppfOver.toScheme B S hS).obj P ≅ Spec (.of k))
  (u : P ⟶ T) (v : P ⟶ V) (hw : yoneda.map u ≫ φ = yoneda.map v ≫ e)
  (hus : Function.Surjective ((BigFppfOver.toScheme B S hS).map u).appTop.hom)
  (hvs : Function.Surjective ((BigFppfOver.toScheme B S hS).map v).appTop.hom)

include he iso hus hvs in
lemma exists_c (I : Ideal (RT T)) (hI : ∀ c ∈ I, ((SCH).map u).appTop.hom c = 0)
    (ho : ChartMain.ClosedP (yoneda.map (Zi T I) ≫ φ)) (j : ℕ) (y) :
    ∃ c, rV ho y - cV ho (rZ T I c) ∈ bI φ u v hw I hI ho ^ j := by
  obtain ⟨hA, het, -, -, -⟩ := etale_base_change_ideal ho he
  haveI := bI_max φ iso u v hw hvs I hI ho
  obtain ⟨-, h2⟩ := c0_trunc (cV ho) het (bI φ u v hw I hI ho) (bI_res φ u v hw hus I hI ho) j
  obtain ⟨z, hz⟩ := h2 (Ideal.Quotient.mk _ (rV ho y))
  obtain ⟨c, rfl⟩ := rZ_surjective T I z
  exact ⟨c, Ideal.Quotient.eq.1 hz.symm⟩

include he iso hw hus hvs in
/-- **Artin approximation step, formal étaleness**: `eA` for all `j`, and `a₁`. -/
theorem exists_eA_pkg (m : Ideal (RT T)) (hum : ∀ c ∈ m, ((SCH).map u).appTop.hom c = 0)
    (hth : ∀ j, 1 ≤ j → ∃ ho : ChartMain.ClosedP (yoneda.map (Zi T (m ^ j)) ≫ φ),
      (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ kerI v ^ j)
    {Ξ : Type u} [CommRing Ξ] (J : ℕ → Ideal Ξ) (eC : ∀ j, (RT T ⧸ kerI u ^ j) ≃+* Ξ ⧸ J j) :
    ∃ (eA : ∀ j, (Γ((SCH).obj V, ⊤) ⧸ kerI v ^ j) ≃+* Ξ ⧸ J j) (a₁ : Zc T (kerI u ^ 2) ⟶ V),
      yoneda.map a₁ ≫ e = yoneda.map (Zi T (kerI u ^ 2)) ≫ φ ∧
      (∀ a c, eA 2 (Ideal.Quotient.mk _ a) = eC 2 (Ideal.Quotient.mk _ c) →
        ((SCH).map a₁).appTop.hom a = rZ T (kerI u ^ 2) c) ∧
      ∀ y, ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom
        (((SCH).map a₁).appTop.hom y) = ((SCH).map v).appTop.hom y := by
  have hmu : m ≤ kerI u := hum
  have hI : ∀ j, 1 ≤ j → ∀ c ∈ m ^ j, ((SCH).map u).appTop.hom c = 0 := fun j hj c hc =>
    hum c (Ideal.pow_le_self (by omega) hc)
  have step : ∀ j, ∃ E : (Γ((SCH).obj V, ⊤) ⧸ kerI v ^ j) ≃+* (RT T ⧸ kerI u ^ j),
      ∀ (hj : 1 ≤ j) (ho : ChartMain.ClosedP (yoneda.map (Zi T (m ^ j)) ≫ φ)) (a c),
        rV ho a - cV ho (rZ T (m ^ j) c) ∈ bI φ u v hw (m ^ j) (hI j hj) ho ^ j →
        E (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ c := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨zeroEquiv _ _, fun h => absurd h (by omega)⟩
    · obtain ⟨ho, hk⟩ := hth j hj
      obtain ⟨E, hE⟩ := eA_step he φ iso u v hw hus hvs (m ^ j) (hI j hj) ho j hk
        (Ideal.pow_right_mono hmu j)
      exact ⟨E, fun _ _ a c h => hE a c h⟩
  choose E hE using step
  obtain ⟨ho, -⟩ := hth 2 (by omega)
  have h12 : (1 : ℕ) ≤ 2 := by omega
  obtain ⟨a₁, hsq, hf⟩ := exists_a1 he φ iso u v hw hus hvs (m ^ 2) (hI 2 h12) ho 2
    (Ideal.pow_right_mono hmu 2) h12
  refine ⟨fun j => (E j).trans (eC j), a₁, hsq, fun a c h => ?_, fun y => ?_⟩
  · obtain ⟨c', hc'⟩ := exists_c he φ iso u v hw hus hvs (m ^ 2) (hI 2 h12) ho 2 a
    have h1 := hE 2 h12 ho a c' hc'
    have h2 : E 2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ c := (eC 2).injective h
    have h3 : c' - c ∈ kerI u ^ 2 := Ideal.Quotient.eq.1 (h1.symm.trans h2)
    rw [hf a c' hc']
    have h4 := (rZ_eq_zero_iff T _ _).2 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  · obtain ⟨c, hc⟩ := exists_c he φ iso u v hw hus hvs (m ^ 2) (hI 2 h12) ho 2 y
    rw [hf y c hc, zLift_appTop, ← kappa_c_rZ φ u v hw (m ^ 2) (hI 2 h12) ho c,
      ← kappa_r φ u v hw (m ^ 2) (hI 2 h12) ho y]
    have h5 : rV ho y - cV ho (rZ T (m ^ 2) c) ∈ bI φ u v hw (m ^ 2) (hI 2 h12) ho :=
      Ideal.pow_le_self (by omega) hc
    have h6 : _ = (0 : Γ((SCH).obj P, ⊤)) := h5
    rw [map_sub] at h6
    exact (sub_eq_zero.1 h6).symm

end Pkg

section HC

variable {W : BigFppfOver B S hS} {e : yoneda.obj V ⟶ X} {f : yoneda.obj W ⟶ X} {he : EtP e}
  {u₀ : P ⟶ W} {v : P ⟶ V} {hw : yoneda.map u₀ ≫ f = yoneda.map v ≫ e}
  (c : ChartPiece he f u₀ v hw) (u : P ⟶ T) {Ξ : Type u} [CommRing Ξ] {J J' : Ideal Ξ} (hJ : J' = J)
  (eC2 : (RT T ⧸ kerI u ^ 2) ≃+* Ξ ⧸ J)
  (eB2 : (Γ((BigFppfOver.toScheme B S hS).obj c.Sobj, ⊤) ⧸ (RingHom.ker c.ringP) ^ 2) ≃+* Ξ ⧸ J')

/-- `S → S/q² ≃ Ξ/(f', 𝔫²) = Ξ/(f, 𝔫²) ≃ C/𝔲² = Γ(V(𝔲²))`. -/
noncomputable def gTwo : Γ((SCH).obj c.Sobj, ⊤) →+* Γ((SCH).obj (Zc T (kerI u ^ 2)), ⊤) :=
  (zE T (kerI u ^ 2)).toRingHom.comp (eC2.symm.toRingHom.comp
    ((Ideal.quotEquivOfEq hJ).toRingHom.comp (eB2.toRingHom.comp (Ideal.Quotient.mk _))))

/-- **Artin approximation step, étaleness: compatibility modulo `𝔫²`** (`eq_of_agree_on_closedPoint`). -/
theorem hc_of_a1 (φ : yoneda.obj T ⟶ X) {k : Type u} [Field k]
    (iso : (SCH).obj P ≅ Spec (.of k))
    (hus : Function.Surjective ((SCH).map u).appTop.hom)
    (eA2 : (Γ((SCH).obj V, ⊤) ⧸ kerI v ^ 2) ≃+* Ξ ⧸ J)
    (a₁ : Zc T (kerI u ^ 2) ⟶ V)
    (hsq : yoneda.map a₁ ≫ e = yoneda.map (Zi T (kerI u ^ 2)) ≫ φ)
    (hform : ∀ a c', eA2 (Ideal.Quotient.mk _ a) = eC2 (Ideal.Quotient.mk _ c') →
      ((SCH).map a₁).appTop.hom a = rZ T (kerI u ^ 2) c')
    (hres : ∀ y, ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom
        (((SCH).map a₁).appTop.hom y) = ((SCH).map v).appTop.hom y)
    (hS2 : ∀ s, gTwo c u hJ eC2 eB2 (((SCH).map (toTop' c.Sobj)).appTop.hom s) =
      ((SCH).map (toTop' (Zc T (kerI u ^ 2)))).appTop.hom s)
    (hW : yoneda.map (siteOfRing (gTwo c u hJ eC2 eB2) hS2 ≫ c.toW) ≫ f =
      yoneda.map (Zi T (kerI u ^ 2)) ≫ φ)
    (hlamR : ∀ x, ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom
      (gTwo c u hJ eC2 eB2 x) = c.ringP x)
    (a) (ξ : Ξ) (h : eA2 (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ξ) :
    eB2 (Ideal.Quotient.mk _ (c.ringV a)) = Ideal.Quotient.mk _ ξ := by
  let b₂ := siteOfRing (gTwo c u hJ eC2 eB2) hS2
  have hb : ((SCH).map b₂).appTop.hom = gTwo c u hJ eC2 eB2 := siteOfRing_appTop _ hS2
  let a₂ := b₂ ≫ c.toV
  have ha₂ : ∀ y, ((SCH).map a₂).appTop.hom y = gTwo c u hJ eC2 eB2 (c.ringV y) := fun y => by
    rw [← hb]
    simp only [a₂, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  let lam := ((SCH).map (zLift (kerI u ^ 2) u (kill_pow u 2 (by omega)))).appTop.hom
  have hlam : ∀ c', lam (rZ T (kerI u ^ 2) c') = ((SCH).map u).appTop.hom c' := zLift_appTop _ _ _
  have hmax : (RingHom.ker lam).IsMaximal := by
    letI := (isField_of_iso iso).toField
    refine RingHom.ker_isMaximal_of_surjective _ fun y => ?_
    obtain ⟨c', rfl⟩ := hus y
    exact ⟨_, hlam c'⟩
  have hnil : ∀ x ∈ RingHom.ker lam, IsNilpotent x := fun x hx => by
    obtain ⟨c', rfl⟩ := rZ_surjective T _ x
    have h1 : c' ∈ kerI u := by
      have h2 : lam (rZ T (kerI u ^ 2) c') = 0 := hx
      rw [hlam] at h2
      exact h2
    refine ⟨2, ?_⟩
    rw [← map_pow]
    exact (rZ_eq_zero_iff T _ _).2 (Ideal.pow_mem_pow h1 2)
  haveI hloc := isLocalRing_of_maximal_nil (RingHom.ker lam) hnil
  have hme : RingHom.ker lam = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hmax
  have heq : a₁ = a₂ := eq_of_agree_on_closedPoint he (Z := Zc T (kerI u ^ 2))
    (fun x hx => hnil x (hme ▸ hx)) a₁ a₂ (by
      rw [hsq, ← hW]
      simp only [a₂, Functor.map_comp, Category.assoc, c.toW_comm]; rfl) (fun y => by
      rw [← hme]
      change lam _ = 0
      rw [map_sub, sub_eq_zero]
      refine (hres y).trans ?_
      rw [ha₂]
      change _ = lam _
      refine Eq.trans ?_ (hlamR (c.ringV y)).symm
      exact (c.ringP_ringV y).symm)
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (eC2.symm (eA2 (Ideal.Quotient.mk _ a)))
  have h1 : eA2 (Ideal.Quotient.mk _ a) = eC2 (Ideal.Quotient.mk _ c') := by
    rw [hc', RingEquiv.apply_symm_apply]
  have h2 := hform a c' h1
  rw [heq, ha₂] at h2
  have h3 : eC2.symm ((Ideal.quotEquivOfEq hJ) (eB2 (Ideal.Quotient.mk _ (c.ringV a)))) =
      Ideal.Quotient.mk _ c' := (zE T (kerI u ^ 2)).injective h2
  have h4 : (Ideal.quotEquivOfEq hJ) (eB2 (Ideal.Quotient.mk _ (c.ringV a))) = Ideal.Quotient.mk _ ξ := by
    rw [(RingEquiv.symm_apply_eq _).1 h3, ← h1, h]
  refine (Ideal.quotEquivOfEq hJ).injective (h4.trans ?_)
  rfl

end HC

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_eA_pkg
#print axioms AlgMag.ChartS5.hc_of_a1
