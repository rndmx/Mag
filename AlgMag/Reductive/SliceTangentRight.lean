/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.RegularSliceTangent
import AlgMag.Reductive.LieIdentityComponent
import AlgMag.Reductive.PointDerivationsBridge
import AlgMag.Reductive.EtaleSliceAssembly

/-!
# Bijectivity of the tangent map of `μ` at `(e, e, t₀)`, right-translation form (C2(d), htan)

Derivations of `O(K)` at `t₀` are read in `Lie K` by `derAtCompEquiv` (right translation by
`t₀⁻¹`). The tangent map of `μ` at `(e, e, t₀)`, read this way, is `Ad(t₀) ∘ sliceTangentMap`
(`derAtCompEquiv_sliceDer`). Given injectivity of `sliceTangentMap` with range `Lie K`, and
`Ad(t₀⁻¹) Lie K ⊆ Lie K`, the tangent map `pointDerComp (sliceMap π N ψ hT) y₀` is bijective
(`pointDerComp_sliceMap_bijective`).
-/

suppress_compilation

open Magnetism TauCeti WithConv TrivSqZeroExt
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]

local notation "Cv" => Bialgebra.CounitAlgebra k H k
local notation "ev" => Bialgebra.CounitAlgebra.algEquivSelf k H k

/-- Constant dual-number points from `k`-points, on any algebra. -/
def kPt : WithConv (H →ₐ[k] k) → WithConv (H →ₐ[k] DualNumber Cv) :=
  fun s => toConv ((Algebra.ofId k (DualNumber Cv)).comp s.ofConv)

lemma kPt_mul (s s' : WithConv (H →ₐ[k] k)) :
    kPt (s * s') = kPt s * kPt s' := by
  simp only [kPt]
  exact map_mul (AlgHom.mapValue (H := H) (Algebra.ofId k (DualNumber Cv))) s s'

lemma kPt_inv (s : WithConv (H →ₐ[k] k)) :
    kPt s⁻¹ = (kPt s)⁻¹ := by
  simp only [kPt]
  exact map_inv (AlgHom.mapValue (H := H) (Algebra.ofId k (DualNumber Cv))) s

/-- **`F ∘ R_s = F * s`** for dual-number valued `F`. -/
lemma comp_rightTranslation_dual (F : H →ₐ[k] DualNumber Cv) (s : WithConv (H →ₐ[k] k)) :
    toConv (F.comp (HopfAlgebra.rightTranslationAlgHom s)) = toConv F * kPt s := by
  rw [HopfAlgebra.rightTranslationAlgHom, AlgHom.comp_convMul_distrib, toConv_ofConv,
    ofConv_toConv, ofConv_toConv, AlgHom.comp_id, ← AlgHom.comp_assoc, Algebra.comp_ofId]
  rfl

/-- The infinitesimal part of a dual-number lift of a point, as a point derivation. -/
def sndDer {B : Type u} [CommRing B] [Algebra k B] (e : B →ₐ[k] k) (Q : B →ₐ[k] DualNumber Cv)
    (hQ : ∀ b, ev (fst (Q b)) = e b) : pointDer e :=
  ⟨((Bialgebra.CounitAlgebra.algEquivSelf k H k).toLinearMap.comp
    ((sndHom Cv Cv).restrictScalars k)).comp Q.toLinearMap, fun a b => by
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      LinearMap.coe_restrictScalars, sndHom_apply, AlgEquiv.toLinearMap_apply, map_mul, snd_mul,
      ← hQ]
    rw [map_add]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_mul]
    ring⟩

lemma sndDer_apply {B : Type u} [CommRing B] [Algebra k B] (e : B →ₐ[k] k)
    (Q : B →ₐ[k] DualNumber Cv) (hQ : ∀ b, ev (fst (Q b)) = e b) (b : B) :
    (sndDer e Q hQ).1 b = ev (snd (Q b)) := rfl

lemma snd_tanPt (d : Derivation k H Cv) (x : H) : snd ((tanPt d).ofConv x) = d x :=
  derivationMulEquivTangentKer_apply_snd (Multiplicative.ofAdd d) x

lemma dualNumberReduction_constPt (g : WithConv (H →ₐ[k] Cv)) :
    dualNumberReduction k H k (constPt g) = g := by
  apply ofConv_injective; ext x
  rw [dualNumberReduction_apply]; rfl

lemma dualNumberReduction_tanPt (d : Derivation k H Cv) :
    dualNumberReduction k H k (tanPt d) = 1 :=
  (derivationMulEquivTangentKer k H k (Multiplicative.ofAdd d)).2

lemma kPt_eq_constPt (g : WithConv (H →ₐ[k] Cv)) (s : WithConv (H →ₐ[k] k))
    (h : ∀ x, s.ofConv x = ev (g.ofConv x)) : kPt s = constPt g := by
  apply ofConv_injective; ext x
  · show fst (algebraMap k (DualNumber Cv) (s.ofConv x)) = fst (inl (g.ofConv x))
    rw [h, TrivSqZeroExt.algebraMap_eq_inl', fst_inl, fst_inl]; rfl
  · show snd (algebraMap k (DualNumber Cv) (s.ofConv x)) = snd (inl (g.ofConv x))
    rw [TrivSqZeroExt.algebraMap_eq_inl', snd_inl, snd_inl]

variable (π : H →ₐc[k] MonoidAlgebra k X)
variable [Module.Finite k (Bialgebra.CotangentSpace k H)]
variable [IsAlgClosed k] [Algebra.FiniteType k H]
variable (N : Magnet (Additive X)) (ψ : X →* Multiplicative ℤ)
variable (hT : compIdeal π N ≤ RingHom.ker π.toAlgHom)

local notation "LieG" => Derivation k H Cv

/-- **The core identity.** For the dual-number point `Q = (e+εX, e+εY, pt)` lifting `y₀`,
the derivation `μ^*`-pulled back and read in `Lie K` by right translation is
`Ad(t₀)((Ad(t₀⁻¹) - 1)(X + Y) + H)`. -/
theorem derAtCompEquiv_sliceDer (g : WithConv (H →ₐ[k] Cv)) (L₀ : Submodule k LieG)
    (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀)
    (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
    (hpt : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG))
    (y₀ : sliceSource π N ψ →ₐ[k] k)
    (hQ : ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = y₀ b) (h : H) :
    ev (((derAtCompEquiv π (toConv (y₀.comp (sliceMap π N ψ hT)))
      (pointDerComp (sliceMap π N ψ hT) y₀ (sndDer y₀ _ hQ)) :
        (magnetHopfIdeal π N).lieSubalgebra (B := k)) : LieG) h) =
      ev ((Derivation.adDerivation k g (sliceTangentMap (Derivation.adRepresentation k g⁻¹)
        (lieSlice π N ψ⁻¹) (lieSlice π N ψ) L₀ p)) h) := by
  set Q := slicePoint π N ψ p.1.1 p.1.2 pt
  set M : H →ₐ[k] compAlg π N := (compMk π N : H →ₐ[k] compAlg π N)
  set S := sliceTangentMap (Derivation.adRepresentation k g⁻¹) (lieSlice π N ψ⁻¹)
    (lieSlice π N ψ) L₀ p
  set t₀ : WithConv (compAlg π N →ₐ[k] k) := toConv (y₀.comp (sliceMap π N ψ hT))
  have htan := sliceMap_tangent π N ψ hT g L₀ p pt hpt
  have hQM : toConv (Q.comp ((sliceMap π N ψ hT).comp M)) = constPt g * tanPt S := by
    rw [← htan, mul_inv_cancel_left]
  -- the base point of `G` is `g`
  have hbase : ∀ x, (BialgHom.mapDomain (compMk π N) t₀).ofConv x = ev (g.ofConv x) := by
    intro x
    have h1 := congrArg (fun F => (dualNumberReduction k H k F).ofConv x) hQM
    simp only [map_mul, dualNumberReduction_constPt, dualNumberReduction_tanPt, mul_one,
      dualNumberReduction_apply] at h1
    rw [BialgHom.mapDomain_apply_apply]
    show y₀ (sliceMap π N ψ hT (M x)) = _
    rw [← hQ]
    exact congrArg ev h1
  refine (derAtCompEquiv_apply π _ _ h).trans ?_
  have hR := congrArg (fun F : H →ₐ[k] compAlg π N => F h)
    (BialgHom.comp_rightTranslationAlgHom (compMk π N) t₀⁻¹)
  simp only [AlgHom.comp_apply] at hR
  have hR' : HopfAlgebra.rightTranslationAlgHom t₀⁻¹ ((compMk π N) h) =
      M (HopfAlgebra.rightTranslationAlgHom (BialgHom.mapDomain (compMk π N) t₀⁻¹) h) := hR.symm
  rw [pointDerComp_apply, sndDer_apply, hR']
  have hF := comp_rightTranslation_dual (Q.comp ((sliceMap π N ψ hT).comp M))
    (BialgHom.mapDomain (compMk π N) t₀⁻¹)
  have h2 := congrArg (fun F : WithConv (H →ₐ[k] DualNumber Cv) => snd (F.ofConv h)) hF
  simp only [ofConv_toConv, AlgHom.comp_apply] at h2
  change ev (snd (Q (sliceMap π N ψ hT (M (HopfAlgebra.rightTranslationAlgHom
    (BialgHom.mapDomain (compMk π N) t₀⁻¹) h))))) = _
  rw [h2, hQM, map_inv, kPt_inv, kPt_eq_constPt g _ hbase, constPt_conj_tanPt, snd_tanPt]


lemma ad_ad_inv (g : WithConv (H →ₐ[k] Cv)) (v : LieG) :
    Derivation.adDerivation k g (Derivation.adDerivation k g⁻¹ v) = v := by
  rw [← Derivation.adRepresentation_apply, ← Derivation.adRepresentation_apply,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma ad_inv_ad (g : WithConv (H →ₐ[k] Cv)) (v : LieG) :
    Derivation.adDerivation k g⁻¹ (Derivation.adDerivation k g v) = v := by
  rw [← Derivation.adRepresentation_apply, ← Derivation.adRepresentation_apply,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- **Bijectivity of the tangent map of `μ`** at `y₀`, from the source parametrisation
(`hsrc`, `hpar`) and the target identity `derAtCompEquiv_sliceDer`, given injectivity of
`sliceTangentMap` with range `Lie K` and `Ad(t₀⁻¹) Lie K ⊆ Lie K`. -/
theorem pointDerComp_sliceMap_bijective (g : WithConv (H →ₐ[k] Cv)) (L₀ : Submodule k LieG)
    (y₀ : sliceSource π N ψ →ₐ[k] k) (hπ : Function.Surjective π)
    (hsrc : ∀ Dd : pointDer y₀, ∃ (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀)
      (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
      (_ : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG))
      (hQ : ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = y₀ b), Dd = sndDer y₀ _ hQ)
    (hpar : ∀ p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀,
      ∃ (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
        (_ : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG)),
        ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = y₀ b)
    (hinj : Function.Injective (sliceTangentMap (Derivation.adRepresentation k g⁻¹)
      (lieSlice π N ψ⁻¹) (lieSlice π N ψ) L₀))
    (hrange : ∀ v ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k), ∃ p,
      sliceTangentMap (Derivation.adRepresentation k g⁻¹) (lieSlice π N ψ⁻¹) (lieSlice π N ψ) L₀ p
        = v)
    (hAd : ∀ v ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k),
      Derivation.adDerivation k g⁻¹ v ∈ (magnetHopfIdeal π N).lieSubalgebra (B := k)) :
    Function.Bijective (pointDerComp (sliceMap π N ψ hT) y₀) := by
  set S := sliceTangentMap (Derivation.adRepresentation k g⁻¹) (lieSlice π N ψ⁻¹)
    (lieSlice π N ψ) L₀
  set t₀ : WithConv (compAlg π N →ₐ[k] k) := toConv (y₀.comp (sliceMap π N ψ hT))
  have key : ∀ (p : (lieSlice π N ψ⁻¹ × lieSlice π N ψ) × L₀)
      (pt : MonoidAlgebra k X →ₐ[k] DualNumber Cv)
      (hpt : toConv (pt.comp π.toAlgHom) = constPt g * tanPt (p.2 : LieG))
      (hQ : ∀ b, ev (fst (slicePoint π N ψ p.1.1 p.1.2 pt b)) = y₀ b),
      ((derAtCompEquiv π t₀ (pointDerComp (sliceMap π N ψ hT) y₀ (sndDer y₀ _ hQ)) :
        (magnetHopfIdeal π N).lieSubalgebra (B := k)) : LieG) =
        Derivation.adDerivation k g (S p) := fun p pt hpt hQ =>
    Derivation.ext fun h => (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
      (derAtCompEquiv_sliceDer π N ψ hT g L₀ p pt hpt y₀ hQ h)
  constructor
  · intro D1 D2 h12
    obtain ⟨p1, pt1, hpt1, hQ1, rfl⟩ := hsrc D1
    obtain ⟨p2, pt2, hpt2, hQ2, rfl⟩ := hsrc D2
    have hΦ := congrArg (fun E => ((derAtCompEquiv π t₀ E :
      (magnetHopfIdeal π N).lieSubalgebra (B := k)) : LieG)) h12
    rw [key p1 pt1 hpt1 hQ1, key p2 pt2 hpt2 hQ2] at hΦ
    have hS : S p1 = S p2 := by
      have := congrArg (Derivation.adDerivation k g⁻¹) hΦ
      rwa [ad_inv_ad, ad_inv_ad] at this
    obtain rfl := hinj hS
    have hpt : pt1 = pt2 := by
      have h' : pt1.comp π.toAlgHom = pt2.comp π.toAlgHom := toConv_injective (hpt1.trans hpt2.symm)
      refine AlgHom.ext fun m => ?_
      obtain ⟨x, rfl⟩ := hπ m
      exact AlgHom.congr_fun h' x
    subst hpt
    rfl
  · intro E
    obtain ⟨p, hp⟩ := hrange _ (hAd _ (derAtCompEquiv π t₀ E).2)
    obtain ⟨pt, hpt, hQ⟩ := hpar p
    refine ⟨sndDer y₀ _ hQ, (derAtCompEquiv π t₀).injective (Subtype.ext ?_)⟩
    rw [key p pt hpt hQ, hp, ad_ad_inv]

/-- The same, in the `SliceTangentBijective` form of `EtaleSliceAssembly`. -/
theorem sliceTangentBijective_of_pointDerComp [Algebra.Smooth k H]
    (y₀ : sliceSource π N ψ →ₐ[k] k) (h : Function.Bijective (pointDerComp (sliceMap π N ψ hT) y₀)) :
    SliceTangentBijective π N ψ hT y₀ := by
  letI := sliceAlgebra π N ψ hT
  letI : Algebra (sliceSource π N ψ) k := y₀.toRingHom.toAlgebra
  letI : Algebra (compAlg π N) k := (y₀.comp (sliceMap π N ψ hT)).toRingHom.toAlgebra
  haveI : IsScalarTower k (compAlg π N) (sliceSource π N ψ) :=
    IsScalarTower.of_algebraMap_eq (fun c => ((sliceMap π N ψ hT).commutes c).symm)
  haveI : IsScalarTower (compAlg π N) (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k (sliceSource π N ψ) k :=
    IsScalarTower.of_algebraMap_eq (fun c => (y₀.commutes c).symm)
  haveI : IsScalarTower k (compAlg π N) k :=
    IsScalarTower.of_algebraMap_eq (fun c => ((y₀.comp (sliceMap π N ψ hT)).commutes c).symm)
  exact (bijective_tangentPullback_iff k).2 h

end AlgMag.Reductive
