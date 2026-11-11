/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5InputE
import AlgMag.ChartS5InputF

/-!
# Chart lemma, Artin approximation and shrinking: `section5Output_of_input`

Part of the proof of the equivariant étale chart lemma for `D(M)`-actions at a closed point (local
structure in the sense of Alper–Hall–Rydh), used for **Theorem 6.8** of Algebraic Magnetism.

From `(T, m, φ)`, an étale chart `(V, v)` of `X` at the point, and the thickening hypothesis,
`Section5Output`. Artin approximation is the named hypothesis `ArtinApproxFP`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartS5

open ChartAlg

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [hSa : IsAffine S]
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T)) [GradedRing (ChartMain.homog actT)]
  {m : Ideal (RT T)} {ι : Type u} [Finite ι] {w : ι → M} {x : ι → RT T}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `𝔭₀` is maximal with finite residue ring, by `hOfC`: it is the kernel of `P₀ → Γ(P)`. -/
theorem p0_facts {P : BigFppfOver B S hS} {k : Type u} [Field k] [Finite k]
    (iso : (SCH).obj P ≅ Spec (.of k)) (u : P ⟶ T)
    (hum : ∀ c ∈ m, ((SCH).map u).appTop.hom c = 0)
    (hx : ∀ i, x i ∈ ChartMain.homog actT (w i))
    (hOfC : ∀ d, ∀ c ∈ ChartMain.homog actT d, c ∉ m → ∃ c', c * c' - 1 ∈ m) :
    (p0 w x m).IsMaximal ∧ Finite (P0 w ℤ ⧸ p0 w x m) := by
  letI := (isField_of_iso iso).toField
  let e1 : Γ((SCH).obj P, ⊤) ≃+* Γ(Spec (.of k), ⊤) := (Scheme.Γ.mapIso iso.symm.op).commRingCatIsoToRingEquiv
  let e2 : Γ(Spec (.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  haveI hfin : Finite Γ((SCH).obj P, ⊤) := Finite.of_equiv k (e1.trans e2).symm.toEquiv
  have hk : ∀ a, ((SCH).map u).appTop.hom (phi0 w x a) = 0 → a ∈ p0 w x m := by
    intro a ha
    by_contra hn
    obtain ⟨c', hc'⟩ := hOfC 0 _ (phi0_mem hx a) hn
    have h1 := hum _ hc'
    rw [map_sub, map_mul, ha, zero_mul, map_one] at h1
    simp only [sub_zero, zero_sub, neg_eq_zero] at h1
    exact one_ne_zero h1
  let g : (P0 w ℤ ⧸ p0 w x m) →+* Γ((SCH).obj P, ⊤) :=
    Ideal.Quotient.lift _ (((SCH).map u).appTop.hom.comp (phi0 w x)) fun a ha => hum _ ha
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hk a hy)
  haveI hf : Finite (P0 w ℤ ⧸ p0 w x m) := Finite.of_injective g hg
  haveI : Nontrivial (P0 w ℤ ⧸ p0 w x m) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun h => ?_
    have h1 : (1 : P0 w ℤ) ∈ p0 w x m := h ▸ trivial
    have h2 := hum _ h1
    rw [map_one, map_one] at h2
    exact one_ne_zero h2
  haveI : IsDomain (P0 w ℤ ⧸ p0 w x m) := hg.isDomain g
  exact ⟨Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _), hf⟩

/-- `Γ(S) → Q_{A'}/(f̃)` is of finite presentation. -/
theorem rho2_fp [Algebra.FiniteType ℤ (RT (siteTop (B := B) (S := S) (hS := hS)))]
    {A' : Type u} [CommRing A'] [Algebra (P0 w ℤ) A'] [Algebra.FiniteType (P0 w ℤ) A'] {s₁ : ℕ}
    (F : Fin s₁ → QR w A') (ρ : RT (siteTop (B := B) (S := S) (hS := hS)) →+* Dq F) :
    ρ.FinitePresentation := by
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType ℤ (QR w A') := finiteType_QR_int w _
  haveI : Algebra.FiniteType ℤ (Dq F) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ (Ideal.span (Set.range F)))
      Ideal.Quotient.mk_surjective
  haveI : Algebra.FiniteType (RT (siteTop (B := B) (S := S) (hS := hS))) (Dq F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  haveI : IsNoetherianRing (RT (siteTop (B := B) (S := S) (hS := hS))) :=
    Algebra.FiniteType.isNoetherianRing ℤ _
  exact (RingHom.finitePresentation_algebraMap).2 (Algebra.FinitePresentation.of_finiteType.1 inferInstance)

open ChartMain in
/-- The structure map from `S` is in degree `0` (the argument of `ChartAssembly.toTop_mem_homog_zero`,
which is not imported here). -/
theorem toTop_homog_zero (a : RT (siteTop (B := B) (S := S) (hS := hS))) :
    ((SCH).map (toTop' T)).appTop.hom a ∈ ChartMain.homog actT 0 := by
  change ChartMain.coact actT _ = _
  apply (spSec_bijective T (ι1 T (M := M)) contains1).1
  rw [spSec_coact]
  have e : (SCH).map (univMap actT) ≫ (SCH).map (toTop' T) =
      (SCH).map (spToT T (ι1 T (M := M)) contains1) ≫ (SCH).map (toTop' T) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Over.mkIdTerminal.hom_ext _ _)
  have e₂ := congrArg (fun z => z.appTop.hom a) e
  simp only [Scheme.Hom.comp_appTop] at e₂
  refine e₂.trans ?_
  change ((SCH).map (spToT T (ι1 T (M := M)) contains1)).appTop.hom _ = _
  rw [spToT_appTop]
  rfl

set_option maxHeartbeats 40000000 in
/-- **Artin approximation and shrinking.** `Section5Output` from `(T, m, φ)`, the chart `(V, e, v)` and the thickening
hypothesis `hth`. Artin approximation is the hypothesis `hArt`. -/
theorem section5Output_of_input (hArt : ChartConclude.ArtinApproxFP.{u})
    [IsNoetherianRing (RT T)] (hC : CompletePair (ChartMain.homog actT) m)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X)
    (hX : IsAlgebraicSpace B S hS X) (hXft : Space.IsLocallyOfFiniteType B S hS (toBase X))
    (hl : LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X)
    [Algebra.FiniteType ℤ (RT (siteTop (B := B) (S := S) (hS := hS)))]
    (φ : yoneda.obj T ⟶ X) (hφ : IsEquivariant actT actX φ)
    (p : ChartPoint X) [Finite p.k] (u : p.P ⟶ T) (hu : yoneda.map u ≫ φ = p.x)
    (hum : ∀ c ∈ m, ((SCH).map u).appTop.hom c = 0)
    (hus : Function.Surjective ((SCH).map u).appTop.hom)
    (Tg : Finset (RT T)) (hTg : ∀ t ∈ Tg, ∃ d, t ∈ ChartMain.homog actT d)
    (hgen : ∀ c : RT T, ∃ q ∈ Algebra.adjoin ℤ (Tg : Set (RT T)), c - q ∈ m)
    (hOfC : ∀ d, ∀ c ∈ ChartMain.homog actT d, c ∉ m → ∃ c', c * c' - 1 ∈ m)
    (hMono : ∀ {T' : BigFppfOver B S hS} (a b : T' ⟶ T),
      (∀ c ∈ m, ((SCH).map a).appTop.hom c = 0) →
      (∀ c ∈ m, ((SCH).map b).appTop.hom c = 0) →
      φ.app (op T') a = φ.app (op T') b → a = b)
    {V : BigFppfOver B S hS} [IsAffine ((SCH).obj V)] [IsNoetherianRing Γ((SCH).obj V, ⊤)]
    {e : yoneda.obj V ⟶ X} (he : EtP e) (v : p.P ⟶ V) (hve : yoneda.map v ≫ e = p.x)
    (hvs : Function.Surjective ((SCH).map v).appTop.hom)
    (hth : ∀ j, 1 ≤ j → ∃ ho : ChartMain.ClosedP (yoneda.map (Zi T (m ^ j)) ≫ φ),
      (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤ kerI v ^ j) :
    ChartConclude.Section5Output actX p := by
  classical
  letI := p.field
  obtain ⟨n, x, w, hx, happ⟩ := exists_coordinates hC.hom Tg hTg hgen
  obtain ⟨hpm, hpf⟩ := p0_facts actT p.iso u hum hx hOfC
  haveI := hpm
  haveI := hpf
  have hsurj := Qmap_surjective hx hC happ
  obtain ⟨s₁, t₁, F, deg, r, hF, hd, hr⟩ := exists_presentation hx hC
  haveI h𝔫 : (nI actT hx hC u : Ideal (Qring w x m)).IsMaximal := by
    letI := (isField_of_iso p.iso).toField
    refine RingHom.ker_isMaximal_of_surjective _ fun y => ?_
    obtain ⟨c, rfl⟩ := hus y
    obtain ⟨q, rfl⟩ := hsurj c
    exact ⟨q, rfl⟩
  haveI : IsNoetherianRing (Qring w x m) := isNoetherianRing_Qring w x m
  obtain ⟨Ξ, _, _, 𝔪, _, toQ, eCf, hE, hpow, hEB, N₀, hN₀⟩ :=
    exists_Xi (P := MvPolynomial (ULift.{u} (Fin n)) ℤ) (P₀ := P0 w ℤ) (Rh := P0hat w x m)
      (Qmap hx hC) hsurj F hF r hr (kerI u) (nI actT hx hC u) rfl
  let N := N₀ + 2
  have hs : ∀ j, ∑ ℓ, r j ℓ * F ℓ = 0 := fun j => by
    have h1 : r j ∈ LinearMap.ker (Fintype.linearCombination (Qring w x m) F) := by
      rw [← hr]; exact Submodule.subset_span ⟨j, rfl⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at h1
    simpa using h1
  obtain ⟨t, F₁, r₁, hFI, hrI, hs₁, hm, ρ, hCt, h0, hv, hψ, xt, hxt, hxφ⟩ :=
    exists_finite_level actT hx hC actX hl (toTop_homog_zero actT) hsurj F hF deg hd r hs φ hφ
  obtain ⟨A', _, _, _, σ, θ, hθ⟩ := exists_artin_level hArt t (N + 1)
  have hN1 : 1 ≤ N + 1 := by omega
  obtain ⟨θh, hθh⟩ := exists_lift_completion (p0 w x m) hN1 σ
  haveI : Algebra.FiniteType (P0 w ℤ) A' := inferInstance
  let ρ₂ := rho2 F₁ θ ρ
  have hC₂ : B.Contains (Spec (.of (Dq (F2 F₁ θ)))) := contains_Dq (F2 F₁ θ) ρ₂
  have hcong : ∀ q : QR w (Rs w t), QRmap w θh (QRmap w θ q) - QRmap w (RsI w t) q ∈
      (nI actT hx hC u : Ideal (Qring w x m)) ^ (N + 1) := fun q => by
    have h1 := QRmap_congr_n actT hx hC u hum (θh.comp θ) (RsI w t) (N + 1) (fun b => by
      change AdicCompletion.evalₐ (p0 w x m) (N + 1) (θh (θ b)) = _
      rw [hθh, hθ]) q
    rwa [← QRmap_comp] at h1
  have hc2 : ∀ z, toQ (QRmap w θh (QRmap w θ z)) - toQ (QRmap w (RsI w t) z) ∈ 𝔪 ^ (N + 1) := fun z => by
    rw [← map_sub]
    exact hpow (N + 1) _ (hcong z)
  have hff : ∀ ℓ, toQ (QRmap w θh (F2 F₁ θ ℓ)) - toQ (F ℓ) ∈ 𝔪 ^ (N + 1) := fun ℓ => by
    have h := hc2 (F₁ ℓ)
    rwa [hFI ℓ] at h
  have hrr : ∀ j ℓ, toQ (QRmap w θh (QRmap w θ (r₁ j ℓ))) - toQ (r j ℓ) ∈ 𝔪 ^ (N + 1) := fun j ℓ => by
    have h := hc2 (r₁ j ℓ)
    rwa [hrI j ℓ] at h
  have hsum : ∀ j, ∑ ℓ, toQ (QRmap w θh (QRmap w θ (r₁ j ℓ))) * toQ (QRmap w θh (F2 F₁ θ ℓ)) = 0 := fun j => by
    have h1 := congrArg (fun z => toQ (QRmap w θh (QRmap w θ z))) (hs₁ j)
    simpa only [map_sum, map_mul, map_zero] using h1
  have hfp : LFPP (fW F₁ θ ρ hCt hC₂ xt) :=
    lfpp_of_cancellation hX hXft (lfp_rObj ρ₂ hC₂ (rho2_fp _ ρ₂)) _
  obtain ⟨hmaxn, hT⟩ := QA_trunc (P := MvPolynomial (ULift.{u} (Fin n)) ℤ) (p0 w x m) θh
    (hA_of_etale (p0 w x m) θh) (nI actT hx hC u) (ph_map_le actT hx hC u hum)
  have hhEB : ∀ (S' : Type u) [CommRing S'] (ι' : Dq (F2 F₁ θ) →+* S') (_ : ι'.Etale) (q' : Ideal S')
      [q'.IsMaximal] (_ : q'.comap ι' = wIdeal θh (nI actT hx hC u) (F2 F₁ θ))
      (_ : Function.Surjective ((Ideal.Quotient.mk q').comp ι')),
      ∃ eB : ∀ j, (S' ⧸ q' ^ j) ≃+* Ξ ⧸
          (Ideal.span (Set.range fun ℓ => toQ (QRmap w θh (F2 F₁ θ ℓ))) ⊔ 𝔪 ^ j),
        ∀ j y, eB j (Ideal.Quotient.mk _ (ι' (Ideal.Quotient.mk _ y))) =
          Ideal.Quotient.mk _ (toQ (QRmap w θh y)) := by
    intro S' _ ι' hι q' _ hq hres
    haveI : (nI actT hx hC u : Ideal (Qring w x m)).comap (gQ θh) |>.IsMaximal := hmaxn
    haveI : (wIdeal θh (nI actT hx hC u) (F2 F₁ θ)).IsMaximal :=
      isMaximal_map_quot _ _ fun ℓ => F2_mem actT hx hC F₁ hv hN1 σ θ hθ θh hθh ρ hC₂ p u hum hψ ℓ
    exact hEB θh (F2 F₁ θ) S' ι' hι q' hq hres hT
  obtain ⟨g₀, hg₀, hg₀u⟩ := exists_g0 actT hx hC F₁ hv hN1 σ θ hθ θh hθh ρ hCt hC₂ p u hum hψ hsurj F hF
    (by omega) happ hus φ xt hxφ hfp he v (hu.trans hve.symm) hvs hth 𝔪 toQ eCf (hE 2) hhEB
    (fun ℓ => Ideal.pow_le_pow_right (by omega) (hff ℓ))
    (fun 𝔭 _ q _ hq eA eB hc => hN₀ N (by omega) _ _ hff hrr hsum 𝔭 q hq eA eB hc)
  exact section5Output_of_etale actT hx hC F₁ hv hN1 σ θ hθ hm ρ hCt hC₂ h0 actX p u hum hψ hX happ hOfC
    xt hxt φ hxφ hu hMono hfp g₀ hg₀ hg₀u

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.section5Output_of_input
