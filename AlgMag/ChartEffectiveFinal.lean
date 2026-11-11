/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveInduct
import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
import StacksFrontier.AlgebraicGeometry.Size.Cutoff
import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Theorem 4.1 of the chart-lemma proof: the inductive step and the noetherian induction

* `AlgMag.ChartMain.complObj`: `Spec Ĉ` as an object of the site (the cutoff of the site is a strong
  limit), with the properties of `§4 Glue`.
* `AlgMag.ChartMain.OpenStratumMap`: Lemma 4.3 as a named proposition.
* `AlgMag.ChartMain.effective_of_stratum`: Theorem 4.1 for `X`, from a stratum and the induction
  hypothesis on the closed strata.
* `AlgMag.ChartMain.effective_of_noetherian`: the noetherian induction.

The statements of Lemma 4.2 (`AffineStratum`), of the tower `Z^(k) = V(J^k)` and of Lemma 4.3 are
hypotheses here. `NoetherianAlgebraization` is discharged in `ChartEffectiveAlg.lean`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space
open scoped Cardinal

universe u

namespace AlgMag.ChartMain

/-! ### The completion: commutative algebra -/

section Ring

set_option linter.unusedSectionVars false

variable {C : Type u} [CommRing C] [IsNoetherianRing C] (a : Ideal C)

local notation "Ĉ" => AdicCompletion a C

lemma compl_ker_eval (k : ℕ) {r : Ĉ} (h : AdicCompletion.eval a C k r = 0) :
    r ∈ (a ^ k).map (algebraMap C Ĉ) := by
  have h1 : r ∈ (a ^ k • ⊤ : Submodule C Ĉ) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian a)]
    exact h
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

/-- `Ĉ = C + aᵏĈ`. -/
lemma compl_surj (k : ℕ) (r : Ĉ) : ∃ c : C, r - algebraMap C Ĉ c ∈ (a ^ k).map (algebraMap C Ĉ) := by
  obtain ⟨c, hc⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval a C k r)
  refine ⟨c, compl_ker_eval a k ?_⟩
  rw [map_sub, sub_eq_zero, ← hc]
  rfl

/-- `C ∩ aᵏĈ = aᵏ`. -/
lemma compl_inj (k : ℕ) (c : C) (h : algebraMap C Ĉ c ∈ (a ^ k).map (algebraMap C Ĉ)) :
    c ∈ a ^ k := by
  have h1 : algebraMap C Ĉ c ∈ (a ^ k • ⊤ : Submodule C Ĉ) := by
    rw [Ideal.smul_top_eq_map]
    exact h
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian a)] at h1
  have h2 : AdicCompletion.eval a C k (algebraMap C Ĉ c) = 0 := h1
  have h3 : (Submodule.mkQ (a ^ k • ⊤ : Submodule C C)) c = 0 := h2
  have h4 : c ∈ (a ^ k • ⊤ : Submodule C C) := (Submodule.Quotient.mk_eq_zero _).1 h3
  simpa [smul_eq_mul, Ideal.mul_top] using h4

/-- A prime containing `a` comes from `Ĉ`. -/
lemma compl_prime (P : Ideal C) [hP : P.IsPrime] (ha : a ≤ P) :
    ∃ Q : Ideal Ĉ, Q.IsPrime ∧ Q.comap (algebraMap C Ĉ) = P := by
  have hle : a ^ 1 ≤ P := by simpa using ha
  let q := Ideal.Quotient.mk (a ^ 1)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker q ≤ P := by rwa [Ideal.mk_ker]
  have hprime : (P.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  have hcm : (P.map q).comap q = P := by
    rw [Ideal.comap_map_of_surjective _ hq, ← RingHom.ker_eq_comap_bot, sup_eq_left]
    exact hker
  refine ⟨(P.map q).comap (AdicCompletion.evalₐ a 1).toRingHom, Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap]
  have : ((AdicCompletion.evalₐ a 1).toRingHom).comp (algebraMap C Ĉ) = q := by
    ext c
    exact AdicCompletion.evalₐ_of a 1 c
  rw [this, hcm]

/-- The size of the completion. -/
lemma compl_card_le : #Ĉ ≤ (max ℵ₀ #C) ^ ℵ₀ := by
  have h1 : #Ĉ ≤ #(AdicCompletion.AdicCauchySequence a C) :=
    Cardinal.mk_le_of_surjective (AdicCompletion.mk_surjective a C)
  have h2 : #(AdicCompletion.AdicCauchySequence a C) ≤ #(ℕ → C) :=
    Cardinal.mk_le_of_injective (f := fun x => (x : ℕ → C)) Subtype.val_injective
  have h3 : #(ℕ → C) = #C ^ ℵ₀ := by simp
  refine h1.trans (h2.trans ?_)
  rw [h3]
  exact Cardinal.power_le_power_right (le_max_right _ _)

end Ring

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### The completion as an object of the site -/

section Compl

variable (T : BigFppfOver B S hS) [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))

/-- `Spec Ĉ` lies in the site: the cutoff is a strong limit cardinal. -/
lemma contains_compl [IsNoetherianRing Γ((SCH).obj T, ⊤)] :
    B.Contains (Spec (.of (AdicCompletion a Γ((SCH).obj T, ⊤)))) :=
  Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ (contains_RT T) (by
    rw [Scheme.size_Spec]
    exact compl_card_le a)

variable [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

/-- `Y = Spec Ĉ`, as an object of the site over `T`. -/
noncomputable abbrev complObj : BigFppfOver B S hS :=
  spObj T (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤))) (contains_compl T a)

/-- `Y → T`. -/
noncomputable abbrev complMap : complObj T a ⟶ T :=
  spToT T (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤))) (contains_compl T a)

/-- The ring isomorphism `Ĉ ≃ Γ(Y)`. -/
noncomputable def complSec : AdicCompletion a Γ((SCH).obj T, ⊤) ≃+* Γ((SCH).obj (complObj T a), ⊤) :=
  RingEquiv.ofBijective (spSec T _ (contains_compl T a)) (spSec_bijective T _ (contains_compl T a))

lemma complMap_appTop :
    ((SCH).map (complMap T a)).appTop.hom = (complSec T a).toRingHom.comp
        (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤))) := by
  ext x
  exact spToT_appTop T _ (contains_compl T a) x

instance : IsNoetherianRing Γ((SCH).obj (complObj T a), ⊤) :=
  isNoetherianRing_of_ringEquiv _ (complSec T a)

lemma map_complMap (k : Ideal Γ((SCH).obj T, ⊤)) :
    k.map ((SCH).map (complMap T a)).appTop.hom =
      (k.map (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤)))).map
        (complSec T a).toRingHom := by
  rw [complMap_appTop, Ideal.map_map]

instance complComplete : IsAdicComplete (a.map ((SCH).map (complMap T a)).appTop.hom)
    Γ((SCH).obj (complObj T a), ⊤) := by
  rw [map_complMap]
  have h1 : IsAdicComplete a (AdicCompletion a Γ((SCH).obj T, ⊤)) :=
    AdicCompletion.isAdicComplete (IsNoetherian.noetherian a)
  have h2 := (IsAdicComplete.map_algebraMap_iff (S := AdicCompletion a Γ((SCH).obj T, ⊤))
    (M := AdicCompletion a Γ((SCH).obj T, ⊤)) a).2 h1
  exact (IsAdicComplete.congr_ringEquiv _ (complSec T a)).2 h2

lemma compl_hsurj (k : ℕ) (r : Γ((SCH).obj (complObj T a), ⊤)) : ∃ c : Γ((SCH).obj T, ⊤),
    r - ((SCH).map (complMap T a)).appTop.hom c ∈
      (a ^ k).map ((SCH).map (complMap T a)).appTop.hom := by
  obtain ⟨r', rfl⟩ := (complSec T a).surjective r
  obtain ⟨c, hc⟩ := compl_surj a k r'
  refine ⟨c, ?_⟩
  rw [map_complMap, complMap_appTop]
  have := Ideal.mem_map_of_mem (complSec T a).toRingHom hc
  rwa [map_sub] at this

lemma compl_hinj (k : ℕ) (c : Γ((SCH).obj T, ⊤))
    (h : ((SCH).map (complMap T a)).appTop.hom c ∈
      (a ^ k).map ((SCH).map (complMap T a)).appTop.hom) : c ∈ a ^ k := by
  refine compl_inj a k c ?_
  rw [map_complMap, complMap_appTop] at h
  have h3 := Ideal.comap_map_of_bijective (complSec T a).toRingHom (complSec T a).bijective
    (I := (a ^ k).map (algebraMap _ (AdicCompletion a Γ((SCH).obj T, ⊤))))
  rw [← h3]
  exact h

lemma compl_flat : Flat ((SCH).map (complMap T a)) := by
  have hf : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤))))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  change Flat (Spec.map _ ≫ ((SCH).obj T).isoSpec.inv)
  infer_instance

/-- `V(a)` lies in the image of `Y`. -/
lemma compl_hcov (x : (SCH).obj T) (hx : ∀ g ∈ a, x ∉ ((SCH).obj T).basicOpen g) :
    x ∈ Set.range ((SCH).map (complMap T a)) := by
  let y : PrimeSpectrum Γ((SCH).obj T, ⊤) := ((SCH).obj T).isoSpec.hom x
  have hy : a ≤ y.asIdeal := fun g hg => by
    by_contra hn
    refine hx g hg ?_
    rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine]
    exact hn
  obtain ⟨Q, hQ, hQc⟩ := compl_prime a y.asIdeal hy
  let pt : Spec (.of (AdicCompletion a Γ((SCH).obj T, ⊤))) := ⟨Q, hQ⟩
  refine ⟨pt, ?_⟩
  have e : (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤))))) pt = y :=
    PrimeSpectrum.ext hQc
  have e2 : (Spec.map (CommRingCat.ofHom
      (algebraMap Γ((SCH).obj T, ⊤) (AdicCompletion a Γ((SCH).obj T, ⊤)))) ≫
        ((SCH).obj T).isoSpec.inv) pt = ((SCH).obj T).isoSpec.inv y := by
    rw [Scheme.Hom.comp_apply, e]
  refine e2.trans ?_
  change ((SCH).obj T).isoSpec.inv (((SCH).obj T).isoSpec.hom x) = x
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

end Compl

/-! ### The inductive step -/

/-- The closed strata `Z^(k) = V(J^k)` of the setup of §4: equivariant monomorphisms to `X`. -/
structure ClosedTower {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X) where
  /-- `Z^(k)`. -/
  Z : ℕ → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The action on `Z^(k)`. -/
  actZ : ∀ k, AAction (fppfO B S hS) M (Z k)
  /-- `Z^(k) → X`. -/
  i : ∀ k, Z k ⟶ X
  equiv : ∀ k, IsEquivariant (actZ k) actX (i k)
  mono : ∀ k U, Function.Injective ((i k).app U)

/-- **Lemma 4.3 with the setup of §4 and the compatibility on `V`**, as a named proposition (not
proved here). For a system `x` on a complete pair `(C, m)`:
the homogeneous ideal `a`, in the form used: the truncations of `V(aᵏ)` land
in `Z^(k)`; the open `T_U = T \ V(a)` with its equivariant `τ`, restricting to `x`; and, for any
flat `Y` over `T` which is an isomorphism along the `V(aᵏ)` with `θ` extending the maps on `V(aᵏ)`,
`τ` and `θ` agree on `V = Y \ V(aŶ)` ("Compatibility on V"). -/
def OpenStratumMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
    (tow : ClosedTower actX) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (m : Ideal Γ((SCH).obj T, ⊤)),
    (letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m) →
    ∀ x, IsEquivSystem actT actX m x →
    ∃ (a : Ideal Γ((SCH).obj T, ⊤)) (gens : Set Γ((SCH).obj T, ⊤)),
      a = Ideal.span gens ∧ (∀ g ∈ gens, ∃ d, g ∈ homog actT d) ∧
      (∀ k, ∀ y ∈ a ^ k, ∀ d, (coact actT y).coeff d ∈ a ^ k) ∧
      (∀ (k n : ℕ) (W : BigFppfOver B S hS)
        (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
        (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
        g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ →
        ∃ z : (tow.Z k).obj (op W), (tow.i k).app _ z = X.map g₂.op (x n)) ∧
      ∃ (UT : BigFppfOver B S hS) (j : UT ⟶ T) (τ : X.obj (op UT)),
        IsOpenImmersion ((SCH).map j) ∧
        (∀ y : (SCH).obj T, y ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, y ∈ ((SCH).obj T).basicOpen g) ∧
        EquivAlong actT actX j τ ∧
        (∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UT)
          (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
          g₁ ≫ j = g₂ ≫ Chart.immι T _ → X.map g₁.op τ = X.map g₂.op (x n)) ∧
        ∀ (Y : BigFppfOver B S hS) [IsAffine ((SCH).obj Y)] [IsNoetherianRing Γ((SCH).obj Y, ⊤)]
          (p : Y ⟶ T), Flat ((SCH).map p) →
          (∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
            r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom) →
          (∀ (k : ℕ) (c : Γ((SCH).obj T, ⊤)),
            ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom → c ∈ a ^ k) →
          IsAdicComplete (a.map ((SCH).map p).appTop.hom) Γ((SCH).obj Y, ⊤) →
          ∀ (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))))),
          (∀ (k n : ℕ) ⦃W : BigFppfOver B S hS⦄
            (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
            (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
            g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → X.map g₁.op (χ k) = X.map g₂.op (x n)) →
          ∀ θ : X.obj (op Y),
          (∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y)
            (s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
            s ≫ Chart.immι T _ = i ≫ p → X.map i.op θ = X.map s.op (χ k)) →
          ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UT) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
            X.map g₁.op τ = X.map g₂.op θ

set_option maxHeartbeats 4000000 in
/-- `hχc`, on an abstract stable closed `ιE : E → T`: a point pulled back from `E'` and a point of
`E`, both restricting to the system `x`, agree (`thm41_unique` on `E`). -/
lemma chi_compat_aux {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T E E' : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj E)] (hsep : Space.IsSeparatedOver B S hS X)
    (ιE : E ⟶ T) (actE : AAction (fppfO B S hS) M (yoneda.obj E))
    {m : Ideal Γ((SCH).obj T, ⊤)} (mE : Ideal Γ((SCH).obj E, ⊤))
    (hmE : ∀ n, mE ^ n = (m ^ n).map ((SCH).map ιE).appTop.hom)
    (hPE : letI := gradedRingOfAction actE; ChartGraded.IsCompletePair (homog actE) mE)
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (ψ : X.obj (op E))
    (hψ : ∀ (r : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ E)
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ r))),
      g₁ ≫ ιE = g₂ ≫ Chart.immι T _ → X.map g₁.op ψ = X.map g₂.op (x r))
    (χ' : X.obj (op E')) (ι' : E' ⟶ T) (e : E ⟶ E') (he : e ≫ ι' = ιE)
    (hχ' : ∀ (r : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ E')
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ r))),
      g₁ ≫ ι' = g₂ ≫ Chart.immι T _ → X.map g₁.op χ' = X.map g₂.op (x r)) :
    X.map e.op χ' = ψ := by
  refine thm41_unique actE hsep mE hPE _ _ fun r => ?_
  have hkill : ∀ c ∈ m ^ r, ((SCH).map (Chart.immι E (Chart.closedι ((SCH).obj E) (mE ^ r)) ≫ ιE)).appTop.hom c = 0 :=
    fun c hc => by
      rw [Functor.map_comp]
      exact appTop_comp_eq_zero (Chart.closedι ((SCH).obj E) (mE ^ r)) ((SCH).map ιE) c
        (closedι_appTop_of_mem _ (by rw [hmE]; exact Ideal.mem_map_of_mem _ hc))
  obtain ⟨s, hs⟩ := exists_factor_closed _ (m ^ r) hkill
  have h1 := hψ r _ s hs.symm
  have h2 := hχ' r (Chart.immι E (Chart.closedι ((SCH).obj E) (mE ^ r)) ≫ e) s (by
    rw [Category.assoc, he, hs])
  rw [← Functor.map_comp_apply, ← op_comp]
  exact h2.trans h1.symm

set_option maxHeartbeats 4000000 in
/-- **Theorem 4.1, existence: the inductive step.** Given the closed strata, effective by induction
(Lemma 4.4), and the map on the open stratum (Lemma 4.3), `X` is effective. `hχc` is
`thm41_unique` on the complete pair `V(aⁿ)`, and `Y = Spec Ĉ`. -/
theorem effective_of_stratum {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actX : AAction (fppfO B S hS) M X} (hX : IsAlgebraicSpace B S hS X)
    (hsep : Space.IsSeparatedOver B S hS X) (hB : NoetherianAlgebraization X)
    (tow : ClosedTower actX) (hL : OpenStratumMap tow) (hZ : ∀ k, Effective (tow.actZ k)) :
    Effective actX := by
  intro T _ actT m hP x hx
  obtain ⟨a, gens, hgens, hhom, hI, hfac, UT, j, τ, hj, hjr, hτ, hτx, hθ⟩ := hL T actT m hP x hx
  letI := gradedRingOfAction actT
  haveI : IsNoetherianRing Γ((SCH).obj T, ⊤) := hP.noeth
  choose χ hχ hχx using fun k => lemma44 actT actX (tow.actZ k) (tow.i k) (tow.equiv k)
    (tow.mono k) (hZ k) (hI k) hP x hx (hfac k)
  have hχc : ∀ (n k : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ n)) ⟶
      Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
      e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (χ k) = χ n := by
    intro n k e he
    exact chi_compat_aux hsep _ (closedAct actT (hI n)) _ (fun r => (Ideal.map_pow _ m r).symm)
      (isCompletePair_closedAct actT (hI n) hP) x (χ n) (hχx n) (χ k) _ e he (hχx k)
  have hsu := compl_hsurj T a
  have hin := compl_hinj T a
  exact thm41_exists_of_strata actT actX hX hsep hB a gens hgens hhom hI j (complMap T a) hj hjr
    (compl_flat T a)
    (fun y hy => compl_hcov T a y fun g hg hyg => hy ((hjr y).2 ⟨g, hg, hyg⟩))
    hsu hin τ hτ χ hχ hχc
    (fun θ hθk _ g₁ g₂ hg => hθ _ _ (compl_flat T a) hsu hin inferInstance χ
      (fun k n _ g₁ g₂ h => hχx k n g₁ g₂ h) θ hθk g₁ g₂ hg)
    m x hτx (fun n k _ g₁ g₂ h => hχx k n g₁ g₂ h)

/-- `X` with no point over a nonempty scheme is effective: then `C = 0`. -/
theorem effective_of_isEmpty {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (actX : AAction (fppfO B S hS) M X)
    (hE : ¬ ∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (X.obj (op W))) :
    Effective actX := by
  intro T _ actT m hP x hx
  letI := gradedRingOfAction actT
  have htop : m = ⊤ := by
    by_contra hm
    have hm1 : m ^ 1 ≠ ⊤ := by simpa using hm
    haveI : Nontrivial (Γ((SCH).obj T, ⊤) ⧸ m ^ 1) := Ideal.Quotient.nontrivial_iff.2 hm1
    refine hE ⟨_, ?_, ⟨x 1⟩⟩
    exact inferInstanceAs (Nonempty (PrimeSpectrum (Γ((SCH).obj T, ⊤) ⧸ m ^ 1)))
  have h10 : (1 : Γ((SCH).obj T, ⊤)) = 0 := hP.sep 0 1 SetLike.GradedOne.one_mem
    (fun n => by rw [htop, Ideal.top_pow]; trivial)
  obtain ⟨s, hs⟩ := exists_factor_closed (𝟙 T) (m ^ 0) (fun c _ => by
    have hc : c = 0 := by rw [← one_mul c, h10, zero_mul]
    rw [hc, map_zero])
  refine ⟨X.map s.op (x 0), fun n => ?_, fun {W} t h => ?_⟩
  · rw [← Functor.map_comp_apply, ← op_comp]
    have := hx.agree (Chart.immι T _ ≫ s) (𝟙 _) (n := 0) (k := n) (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
    rw [this, CategoryTheory.op_id, FunctorToTypes.map_id_apply]
  · have := hx.equiv 0 (t ≫ s) (smulAt actT h t ≫ s) h (by
      rw [Category.assoc, hs, Category.assoc, hs, Category.comp_id, Category.comp_id])
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    exact this

/-! ### The noetherian induction -/

section Induction

attribute [local instance] Space.pointTopology

variable {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A closed `D(M)`-stable subspace of `X₀`, with any structure. -/
structure ClosedStable (act₀ : AAction (fppfO B S hS) M X₀) where
  /-- The subspace. -/
  Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its action. -/
  actZ : AAction (fppfO B S hS) M Z
  /-- Its inclusion. -/
  i : Z ⟶ X₀
  equiv : IsEquivariant actZ act₀ i
  mono : ∀ U, Function.Injective (i.app U)
  closed : Space.IsClosedImmersion B S hS i
  alg : IsAlgebraicSpace B S hS Z

/-- `X₀` itself. -/
def ClosedStable.self (act₀ : AAction (fppfO B S hS) M X₀) (hX₀ : IsAlgebraicSpace B S hS X₀) :
    ClosedStable act₀ where
  Z := X₀
  actZ := act₀
  i := 𝟙 _
  equiv := fun _ _ => rfl
  mono := fun _ => Function.injective_id
  closed := MorphismProperty.id_mem (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) _
  alg := hX₀

/-- **The setup of §4 for `Z`, with Lemma 4.3**, as a named proposition (not proved here): for a
stable open `f : U → Z`, the tower `V(J^k)` of closed stable subspaces with the complement of `U`
as point set, and the map on the open stratum. -/
def StrataOver {act₀ : AAction (fppfO B S hS) M X₀} (C : ClosedStable act₀) : Prop :=
  ∀ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ C.Z), IsAffine ((SCH).obj U) → Nonempty ((SCH).obj U) →
    IsEquivariant actU C.actZ f →
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) f →
    ∃ tow : ClosedTower C.actZ,
      (∀ k, Space.IsClosedImmersion B S hS (tow.i k)) ∧
      (∀ k, IsAlgebraicSpace B S hS (tow.Z k)) ∧
      (∀ k, Disjoint (Set.range (pointsMap B S hS _ (tow.i k)))
        (Set.range (pointsMap B S hS _ f))) ∧
      OpenStratumMap tow

/-- The closed point set of `C` in `|X₀|`. -/
def ClosedStable.pts {act₀ : AAction (fppfO B S hS) M X₀} (hX₀ : IsAlgebraicSpace B S hS X₀)
    (C : ClosedStable act₀) : TopologicalSpace.Closeds (points B S hS X₀) :=
  ⟨Set.range (pointsMap B S hS _ C.i),
    isClosed_range_pointsMap_of_isClosedImmersion B S hS hX₀ C.i C.closed⟩

/-- **Theorem 4.1, existence: the noetherian induction** on closed stable subsets of `|X₀|`, "for
all closed `G`-stable structures on them at once". -/
theorem effective_of_noetherian {act₀ : AAction (fppfO B S hS) M X₀}
    (hX₀ : IsAlgebraicSpace B S hS X₀)
    [TopologicalSpace.NoetherianSpace (points B S hS X₀)]
    (hC : ∀ C : ClosedStable act₀, Space.IsSeparatedOver B S hS C.Z ∧ NoetherianAlgebraization C.Z)
    (h42 : ∀ C : ClosedStable act₀, AffineStratum C.Z C.actZ)
    (h43 : ∀ C : ClosedStable act₀, StrataOver C)
    (C : ClosedStable act₀) : Effective C.actZ := by
  suffices h : ∀ (K : TopologicalSpace.Closeds (points B S hS X₀)) (C : ClosedStable act₀),
      C.pts hX₀ = K → Effective C.actZ from h _ C rfl
  intro K
  induction K using WellFoundedLT.induction with
  | ind K IH =>
    intro C hCK
    by_cases hne : ∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (C.Z.obj (op W))
    · obtain ⟨U, actU, f, hUa, hUn, hfe, hfo⟩ := h42 C hne
      obtain ⟨tow, hcl, halg, hdis, hL⟩ := h43 C U actU f hUa hUn hfe hfo
      obtain ⟨hsep, hB⟩ := hC C
      refine effective_of_stratum C.alg hsep hB tow hL fun k => ?_
      let C' : ClosedStable act₀ :=
        { Z := tow.Z k
          actZ := tow.actZ k
          i := tow.i k ≫ C.i
          equiv := fun h x => (C.equiv h _).symm ▸ congrArg (C.i.app _) (tow.equiv k h x)
          mono := fun V => (C.mono V).comp (tow.mono k V)
          closed := MorphismProperty.comp_mem _ _ _ (hcl k) C.closed
          alg := halg k }
      refine IH (C'.pts hX₀) ?_ C' rfl
      have hle : C'.pts hX₀ ≤ K := by
        rw [← hCK]
        rintro _ ⟨q, rfl⟩
        refine ⟨pointsMap B S hS _ (tow.i k) q, ?_⟩
        change _ = pointsMap B S hS _ (tow.i k ≫ C.i) q
        rw [pointsMap_comp]
        rfl
      refine lt_of_le_of_ne hle fun heq => ?_
      obtain ⟨u⟩ := hUn
      obtain ⟨p, -⟩ := (pointsEquivScheme B S hS U).surjective u
      have hmemK : pointsMap B S hS _ C.i (pointsMap B S hS _ f p) ∈ (K : Set _) := by
        rw [← hCK]
        exact ⟨_, rfl⟩
      rw [← heq] at hmemK
      obtain ⟨q, hq⟩ := hmemK
      haveI : Mono C.i := (NatTrans.mono_iff_mono_app _).2 fun V =>
        (mono_iff_injective _).2 (C.mono V)
      have hq' : pointsMap B S hS _ (tow.i k ≫ C.i) q = _ := hq
      rw [pointsMap_comp] at hq'
      have hinj := pointsMap_injective_of_mono B S hS C.i hq'
      exact Set.disjoint_left.1 (hdis k) ⟨q, hinj⟩ ⟨p, rfl⟩
    · exact effective_of_isEmpty C.actZ hne

end Induction

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.effective_of_stratum
#print axioms AlgMag.ChartMain.effective_of_noetherian
