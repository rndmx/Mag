/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec16Remaining
import AlgMag.Sec11SchemesRep
import AlgMag.Sec13General
import AlgMag.Sec3Remaining
import AlgMag.Sec15General
import AlgMag.Sec3IntersectionsWeak
import AlgMag.Sec13Dilatations
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Remaining items of §13, §15, §16

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126-201.

* `AlgMag.prop1615_ii`: **Proposition 16.15 (ii)**.
* `AlgMag.Dil.smooth_of_isDilatation`: **[Mayeux-Richarz-Romagny, Prop. 2.16]**.
* `AlgMag.Dil.cor13_3`: **Corollary 13.3**.
* `AlgMag.pureMagnets_p1`: **§15, Example (iv)**, the pure magnets of `ℙ¹`.
* `AlgMag.Mono.toricAction`, `toric_atlas`, `toric_attractor_cover`: **§16.7**.
-/

universe u

/-! ### Proposition 16.15 (ii) -/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgMag

section Prop1615ii

open AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]

/-- **Proposition 16.15 (ii)**, for `G^{[α⟩}`: if `G/S` is smooth and `G^{[α⟩}` is represented by a
scheme, it is smooth over `S` (Corollary 11.2; the paper cites the companion Corollary 11.10). -/
theorem prop1615_ii_attr {X Y : Over S} [Smooth X.hom] (act : AAction (overO S) M (yoneda.obj X))
    (N : AddSubmonoid M) (rY : RepresentsAttractor act N (yoneda.obj Y)) : Smooth Y.hom := by
  let g : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (Category.comp_id _)
  have : Smooth g.left := inferInstanceAs (Smooth X.hom)
  exact SmoothSchemes.smooth_repMap N (aY := SmoothSchemes.trivAction) g (fun _ _ => SmoothSchemes.term_ext _ _) rY
    (SmoothSchemes.repTerminal N) (Over.homMk Y.hom (Category.comp_id _)) (fun T w => by
      refine AttractorPt.ext ?_
      funext T₁ t a
      exact SmoothSchemes.term_ext _ _)

/-- **Proposition 16.15 (ii).** Let `G` be a group scheme smooth over `S`, with `D(M)_S` acting by
group automorphisms, `α ∈ M`, and assume `G^{[α⟩}`, `G^0 = G^{[α⟩^×}` are represented by schemes
(automatic if `G` is `S`-affine, see `prop1615_ii_of_isAffineHom`). Then `G^{[α⟩}` and
`G^{[α⟩}_{e_S}` are smooth over `S`: the latter is `G^{[α⟩} ×_{G^0} e_S`, a base change of the smooth
`G^{[α⟩} → G^0` (Corollary 11.10) along the unit section. -/
theorem prop1615_ii {X Y Y0 : Over S} [Smooth X.hom]
    {grp : ∀ U : (Over S)ᵒᵖ, Group ((yoneda.obj X).obj U)}
    {map_mul : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y}
    (act : AAction (overO S) M (schemeGrp X grp map_mul).F)
    (ha : ActsByMonoidEnd act) (α : M)
    (r1 : RepresentsAttractor (F := yoneda.obj X) act (AddSubmonoid.closure {α}) (yoneda.obj Y))
    (r0 : RepresentsAttractor (F := yoneda.obj X) act (unitsFace (AddSubmonoid.closure {α}))
      (yoneda.obj Y0)) :
    Smooth Y.hom ∧ ∃ (K : Over S) (j : K ⟶ Y)
      (eK : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T)),
      Smooth K.hom ∧ ∀ {T : Over S} (z : T ⟶ K), (eK T z).1.1 = r1.equiv T (z ≫ j) := by
  let act' : AAction (overO S) M (yoneda.obj X) := act
  let N := AddSubmonoid.closure {α}
  let Q := unitsFace N
  have hQ : IsFace Q N := unitsIsFace N
  let e1 : ∀ T, (T ⟶ Y) ≃ AttractorPt act' N T := fun T => r1.equiv T
  let e0 : ∀ T, (T ⟶ Y0) ≃ AttractorPt act' Q T := fun T => r0.equiv T
  have n0 : ∀ {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ Y0), e0 T' (s ≫ z) = (e0 T z).baseChange s :=
    fun s z => r0.naturality s z
  have n1 : ∀ {T T' : Over S} (s : T' ⟶ T) (z : T ⟶ Y), e1 T' (s ≫ z) = (e1 T z).baseChange s :=
    fun s z => r1.naturality s z
  let p : Y ⟶ Y0 := (e0 Y).symm (AttractorPt.ofFace hQ (e1 Y (𝟙 Y)))
  have hp : ∀ {T : Over S} (z : T ⟶ Y), e0 T (z ≫ p) = AttractorPt.ofFace hQ (e1 T z) := by
    intro T z
    rw [n0, Equiv.apply_symm_apply]
    have : e1 T z = (e1 Y (𝟙 Y)).baseChange z := by
      rw [← n1, Category.comp_id]
    rw [this]
    rfl
  have hps : Smooth p.left := SmoothSchemes.smooth_repFace N act' hQ r1 r0 p (fun T w => hp w)
  let G' := attrGrp (schemeGrp X grp map_mul) act ha Q
  let Sobj : Over S := Over.mk (𝟙 S)
  let oneQ : ∀ T : Over S, AttractorPt act' Q T := fun T => (1 : G'.F.obj (op T))
  have hone : ∀ {T T' : Over S} (s : T' ⟶ T), (oneQ T).baseChange s = oneQ T' := fun {T T'} s =>
    GrpFunctor.map_one G' s.op
  let u : Sobj ⟶ Y0 := (e0 Sobj).symm (oneQ Sobj)
  have hu : ∀ {T : Over S} (τ : T ⟶ Sobj), e0 T (τ ≫ u) = oneQ T := by
    intro T τ
    rw [n0, Equiv.apply_symm_apply, hone]
  let K : Over S := Over.mk (pullback.fst p.left u.left ≫ Y.hom)
  let j : K ⟶ Y := Over.homMk (pullback.fst p.left u.left) rfl
  let v : K ⟶ Sobj := Over.homMk (pullback.snd p.left u.left) (by
    have h1 := pullback.condition (f := p.left) (g := u.left)
    have h2 : p.left ≫ Y0.hom = Y.hom := Over.w p
    have h3 : u.left ≫ Y0.hom = 𝟙 S := Over.w u
    change pullback.snd p.left u.left ≫ 𝟙 S = pullback.fst p.left u.left ≫ Y.hom
    rw [← h3, ← Category.assoc, ← h1, Category.assoc, h2])
  have hjv : j ≫ p = v ≫ u := Over.OverMorphism.ext (pullback.condition (f := p.left) (g := u.left))
  let eK : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T) := fun T =>
    { toFun := fun z => ⟨(e1 T (z ≫ j), PUnit.unit), by
        change AttractorPt.ofFace hQ (e1 T (z ≫ j)) = oneQ T
        rw [← hp, Category.assoc, hjv, ← Category.assoc, hu]⟩
      invFun := fun x =>
        let z0 : T ⟶ Y := (e1 T).symm x.1.1
        let τ : T ⟶ Sobj := Over.homMk T.hom (by simp [Sobj])
        have hz : z0 ≫ p = τ ≫ u := by
          apply (e0 T).injective
          rw [hp, hu]
          have e : e1 T z0 = x.1.1 := Equiv.apply_symm_apply _ _
          rw [e]
          exact x.2
        Over.homMk (pullback.lift z0.left τ.left (congrArg (fun k => k.left) hz)) (by
          simp only [K, Over.mk_hom]
          rw [pullback.lift_fst_assoc]
          exact Over.w z0)
      left_inv := fun z => by
        refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
        · simp only [Over.homMk_left, pullback.lift_fst, Equiv.symm_apply_apply]
          rfl
        · simp only [Over.homMk_left, pullback.lift_snd]
          have := Over.w (z ≫ v)
          simpa [Sobj, v] using this.symm
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext ?_ rfl)
        have h : ∀ w : T ⟶ K, w.left ≫ pullback.fst p.left u.left = ((e1 T).symm x.1.1).left →
            w ≫ j = (e1 T).symm x.1.1 := fun w hw => Over.OverMorphism.ext hw
        exact (congrArg (e1 T) (h _ (pullback.lift_fst _ _ _))).trans (Equiv.apply_symm_apply _ _) }
  have hK : Smooth K.hom := by
    -- `K → S` is the base change of `p` along `u`.
    have h1 : Smooth (pullback.snd p.left u.left) := inferInstance
    have h2 : K.hom = pullback.snd p.left u.left := by
      have h4 : (v.left : K.left ⟶ S) ≫ 𝟙 S = K.hom := Over.w v
      exact h4.symm.trans (Category.comp_id _)
    rw [h2]
    exact h1
  exact ⟨prop1615_ii_attr (act : AAction (overO S) M (yoneda.obj X)) N r1, K, j, eK, hK, fun z => rfl⟩

/-- **Proposition 16.15 (ii)**, `G` affine over `S`: representability is Theorem 3.20. -/
theorem prop1615_ii_of_isAffineHom {X : Over S} [Smooth X.hom] [IsAffineHom X.hom]
    {grp : ∀ U : (Over S)ᵒᵖ, Group ((yoneda.obj X).obj U)}
    {map_mul : ∀ {U V : (Over S)ᵒᵖ} (s : U ⟶ V) (x y : (yoneda.obj X).obj U),
      (yoneda.obj X).map s (x * y) = (yoneda.obj X).map s x * (yoneda.obj X).map s y}
    (act : AAction (overO S) M (schemeGrp X grp map_mul).F)
    (ha : ActsByMonoidEnd act) (α : M) :
    Smooth (GB.Zatt (act : AAction (overO S) M (yoneda.obj X)) (AddSubmonoid.closure {α})).hom ∧
      ∃ (K : Over S) (j : K ⟶ GB.Zatt (act : AAction (overO S) M (yoneda.obj X)) (AddSubmonoid.closure {α}))
        (_ : ∀ T : Over S, (T ⟶ K) ≃ (rootKernel act ha α).F.obj (op T)), Smooth K.hom := by
  obtain ⟨h1, K, j, eK, hK, -⟩ := prop1615_ii act ha α
    (GB.representsAttractor (act : AAction (overO S) M (yoneda.obj X)) (AddSubmonoid.closure {α}))
    (GB.representsAttractor (act : AAction (overO S) M (yoneda.obj X))
      (unitsFace (AddSubmonoid.closure {α})))
  exact ⟨h1, K, j, eK, hK⟩

end Prop1615ii

end AlgMag

/-! ### [Mayeux-Richarz-Romagny, Prop. 2.16]: the algebra -/


namespace AlgMag.Dil

section Pres

variable {R A L : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing L] [Algebra R L]
  [Algebra A L] [IsScalarTower R A L] {n : ℕ}

/-- The ideal `(a yᵢ - fᵢ)` of `L[y₁, …, yₙ]`. -/
noncomputable abbrev presIdeal (a : L) (f : Fin n → L) : Ideal (MvPolynomial (Fin n) L) :=
  Ideal.span (Set.range fun i => MvPolynomial.C a * MvPolynomial.X i - MvPolynomial.C (f i))

/-- The ring `L[y₁, …, yₙ] / (a yᵢ - fᵢ)`. -/
noncomputable abbrev PresRing (a : L) (f : Fin n → L) : Type u := MvPolynomial (Fin n) L ⧸ presIdeal a f

/-- **Core of [Mayeux-Richarz-Romagny, Prop. 2.16].** `L = A_g` is formally smooth over `R`, and
`f` admits `R`-derivations `D_k : A → L` with `D_k f_i = δ_ik`. Then `L[y]/(r y - f)` is formally
smooth over `R`. -/
theorem formallySmooth_presRing (g : A) [IsLocalization.Away g L] [Algebra.FormallySmooth R L]
    (r : R) (f : Fin n → A) (D : Fin n → Derivation R A L)
    (hD : ∀ i k, D k (f i) = if i = k then 1 else 0) :
    Algebra.FormallySmooth R
      (PresRing (algebraMap R L r) (fun i => algebraMap A L (f i))) := by
  classical
  let a : L := algebraMap R L r
  let f' : Fin n → L := fun i => algebraMap A L (f i)
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ K hK φ => ?_
  have hKK : ∀ x ∈ K, ∀ y ∈ K, x * y = 0 := fun x hx y hy => by
    have : x * y ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hK] at this
    exact this
  let ιL : L →ₐ[R] PresRing a f' :=
    (Ideal.Quotient.mkₐ R (presIdeal a f')).comp (IsScalarTower.toAlgHom R L (MvPolynomial (Fin n) L))
  obtain ⟨g₀, hg₀⟩ := Algebra.FormallySmooth.comp_surjective R L K hK (φ.comp ιL)
  have hg₀' : ∀ x : L, Ideal.Quotient.mk K (g₀ x) = φ (ιL x) := fun x =>
    DFunLike.congr_fun hg₀ x
  let yb : Fin n → PresRing a f' := fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)
  choose Y hY using fun i => Ideal.Quotient.mk_surjective (φ (yb i))
  let k : Fin n → B := fun i => algebraMap R B r * Y i - g₀ (f' i)
  have hrel : ∀ i, ιL a * yb i = ιL (f' i) := fun i => by
    change Ideal.Quotient.mk _ (MvPolynomial.C a) * Ideal.Quotient.mk _ (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (MvPolynomial.C (f' i))
    rw [← map_mul]
    exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
  have hk : ∀ i, k i ∈ K := fun i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hY, hg₀', ← hrel i, sub_eq_zero, map_mul]
    congr 1
    change Ideal.Quotient.mk K (algebraMap R B r) = φ (ιL (algebraMap R L r))
    rw [ιL.commutes, φ.commutes]
    rfl
  -- the corrected lift on `A`
  let dd : A → B := fun x => ∑ i, g₀ (D i x) * k i
  have hdd : ∀ x, dd x ∈ K := fun x => Ideal.sum_mem _ fun i _ => K.mul_mem_left _ (hk i)
  let g₁ : A →+* B :=
    { toFun := fun x => g₀ (algebraMap A L x) + dd x
      map_one' := by
        have : dd 1 = 0 := by simp [dd]
        rw [this, map_one, map_one, add_zero]
      map_zero' := by
        have : dd 0 = 0 := by simp [dd]
        rw [this, map_zero, map_zero, add_zero]
      map_add' := fun x y => by
        have : dd (x + y) = dd x + dd y := by simp [dd, add_mul, Finset.sum_add_distrib]
        rw [this, map_add, map_add]; ring
      map_mul' := fun x y => by
        have e : dd (x * y) = g₀ (algebraMap A L x) * dd y + g₀ (algebraMap A L y) * dd x := by
          simp only [dd, Derivation.leibniz, Finset.mul_sum, ← Finset.sum_add_distrib, Algebra.smul_def,
            map_add, map_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
        change g₀ (algebraMap A L (x * y)) + dd (x * y) =
          (g₀ (algebraMap A L x) + dd x) * (g₀ (algebraMap A L y) + dd y)
        rw [e, map_mul, map_mul]
        linear_combination -(hKK _ (hdd x) _ (hdd y)) }
  have hg₁mk : ∀ x, Ideal.Quotient.mk K (g₁ x) = φ (ιL (algebraMap A L x)) := fun x => by
    change Ideal.Quotient.mk K (g₀ (algebraMap A L x) + dd x) = _
    rw [map_add, hg₀', Ideal.Quotient.eq_zero_iff_mem.2 (hdd x), add_zero]
  have hg₁unit : IsUnit (g₁ g) := by
    rw [← IsNilpotent.isUnit_quotient_mk_iff (I := K) ⟨2, hK⟩, hg₁mk]
    exact ((IsLocalization.Away.algebraMap_isUnit g : IsUnit (algebraMap A L g)).map ιL).map φ
  let g₂ : L →+* B := IsLocalization.Away.lift g hg₁unit
  have hg₂ : ∀ x, g₂ (algebraMap A L x) = g₁ x := fun x => IsLocalization.Away.lift_eq g hg₁unit x
  have hg₂mk : ∀ x, Ideal.Quotient.mk K (g₂ x) = φ (ιL x) := by
    intro x
    have : (Ideal.Quotient.mk K).comp g₂ = (φ.comp ιL : L →+* B ⧸ K) :=
      IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun y => by
        change Ideal.Quotient.mk K (g₂ (algebraMap A L y)) = _
        rw [hg₂, hg₁mk]; rfl)
    exact DFunLike.congr_fun this x
  have hg₂r : ∀ s : R, g₂ (algebraMap R L s) = algebraMap R B s := fun s => by
    rw [IsScalarTower.algebraMap_apply R A L, hg₂]
    change g₀ (algebraMap A L (algebraMap R A s)) + dd (algebraMap R A s) = _
    have : dd (algebraMap R A s) = 0 := by simp [dd]
    rw [this, add_zero, ← IsScalarTower.algebraMap_apply, g₀.commutes]
  have hfi : ∀ j, g₂ (f' j) = algebraMap R B r * Y j := fun j => by
    change g₂ (algebraMap A L (f j)) = _
    rw [hg₂]
    change g₀ (algebraMap A L (f j)) + dd (f j) = _
    have : dd (f j) = k j := by
      simp only [dd, hD, apply_ite g₀, map_one, map_zero, ite_mul, one_mul, zero_mul]
      simp
    rw [this]
    simp only [k, f']
    ring
  let ev : MvPolynomial (Fin n) L →+* B := MvPolynomial.eval₂Hom g₂ Y
  have hev : presIdeal a f' ≤ RingHom.ker ev := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change ev _ = 0
    simp only [map_sub, map_mul, ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    rw [hfi i, sub_eq_zero]
    exact congrArg (· * Y i) (hg₂r r)
  let lf : PresRing a f' →+* B := Ideal.Quotient.lift _ ev (fun x hx => hev hx)
  refine ⟨{ lf with commutes' := fun s => ?_ }, ?_⟩
  · change ev (MvPolynomial.C (algebraMap R L s)) = _
    simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact hg₂r s
  · apply AlgHom.coe_ringHom_injective
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun x => ?_) (fun i => ?_))
    · change Ideal.Quotient.mk K (ev (MvPolynomial.C x)) = φ (ιL x)
      simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact hg₂mk x
    · change Ideal.Quotient.mk K (ev (MvPolynomial.X i)) = φ (yb i)
      simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      exact hY i

end Pres

end AlgMag.Dil

namespace AlgMag.Dil

open TensorProduct

section Gen

variable {A : Type u} [CommRing A]

/-- Nakayama at `p`: if `J` is f.g. in `p` and every `z ∈ J` is, up to a unit at `p`, in `J' ⊔ J²`,
then `h J ≤ J'` for some `h ∉ p`. -/
lemma exists_mul_mem_of_local {J J' : Ideal A} (hJ : J.FG) (p : Ideal A) [p.IsPrime] (hp : J ≤ p)
    (h : ∀ z ∈ J, ∃ s ∉ p, s * z ∈ J' ⊔ J ^ 2) :
    ∃ h₂ ∉ p, ∀ z ∈ J, h₂ * z ∈ J' := by
  classical
  let Ap := Localization.AtPrime p
  let JJ : Ideal Ap := J.map (algebraMap A Ap)
  let JJ' : Ideal Ap := J'.map (algebraMap A Ap)
  have hunit : ∀ s, s ∉ p → IsUnit (algebraMap A Ap s) := fun s hs =>
    IsLocalization.map_units Ap (⟨s, hs⟩ : p.primeCompl)
  have hmax : JJ ≤ IsLocalRing.maximalIdeal Ap := by
    refine Ideal.map_le_iff_le_comap.2 fun z hz => ?_
    rw [Ideal.mem_comap, IsLocalization.AtPrime.to_map_mem_maximal_iff Ap p]
    exact hp hz
  have hle : JJ ≤ JJ' ⊔ (IsLocalRing.maximalIdeal Ap) • JJ := by
    refine Ideal.map_le_iff_le_comap.2 fun z hz => ?_
    obtain ⟨s, hs, hsz⟩ := h z hz
    have h1 : algebraMap A Ap (s * z) ∈ JJ' ⊔ JJ ^ 2 := by
      have : (J' ⊔ J ^ 2).map (algebraMap A Ap) = JJ' ⊔ JJ ^ 2 := by
        rw [Ideal.map_sup, Ideal.map_pow]
      rw [← this]
      exact Ideal.mem_map_of_mem _ hsz
    rw [map_mul] at h1
    have h2 : JJ' ⊔ JJ ^ 2 ≤ JJ' ⊔ (IsLocalRing.maximalIdeal Ap) • JJ := by
      refine sup_le_sup_left ?_ _
      rw [pow_two]
      exact Ideal.mul_mono_left hmax
    have h3 := h2 h1
    obtain ⟨v, hv⟩ := (hunit s hs).exists_left_inv
    have := Ideal.mul_mem_left _ v h3
    rwa [← mul_assoc, hv, one_mul] at this
  have hfg : JJ.FG := hJ.map _
  have hN : JJ ≤ JJ' := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    exact hle
  obtain ⟨T, hT⟩ := hJ
  have hgen : ∀ t ∈ T, ∃ h ∉ p, h * t ∈ J' := by
    intro t ht
    have htJ : t ∈ J := hT ▸ Ideal.subset_span ht
    have := hN (Ideal.mem_map_of_mem (algebraMap A Ap) htJ)
    obtain ⟨⟨x, y⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl Ap).1 this
    rw [← map_mul] at e
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl Ap).1 e
    refine ⟨c * y, Submonoid.mul_mem _ c.2 y.2, ?_⟩
    have : (c : A) * y * t = c * x := by rw [← hc]; ring
    rw [this]
    exact J'.mul_mem_left _ x.2
  choose! H hH hH' using hgen
  refine ⟨∏ t ∈ T, H t, ?_, fun z hz => ?_⟩
  · exact Submonoid.prod_mem p.primeCompl fun t ht => hH t ht
  · rw [← hT] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem H hx
      rw [hu, mul_right_comm]
      exact J'.mul_mem_right _ (hH' x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact J'.mul_mem_left _ hx

end Gen

section Conormal

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]

/-- The local structure of a center `J` with projective conormal module, at `p ⊇ J`. -/
theorem exists_pres_of_conormal {J : Ideal A} (a : A) (ha : a ∈ J) (hJ : J.FG)
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (ψ : Ω[A⁄R] →ₗ[A] N) (c : J →ₗ[A] N) (hc : Function.Surjective c)
    (hψ : ∀ z : J, ψ (KaehlerDifferential.D R A z) = c z)
    (hk : ∀ z : J, c z = 0 → (z : A) ∈ J ^ 2 ⊔ Ideal.span {a})
    (p : Ideal A) [p.IsPrime] (hp : J ≤ p) :
    ∃ g ∉ p, ∃ (n : ℕ) (f : Fin n → A) (D : Fin n → Derivation R A (Localization.Away g)),
      (∀ i, f i ∈ J) ∧ (∀ i k, D k (f i) = if i = k then 1 else 0) ∧
      ∀ z ∈ J, g * z ∈ Ideal.span (insert a (Set.range f)) := by
  classical
  let S := p.primeCompl
  let Ap := Localization.AtPrime p
  let k := IsLocalRing.ResidueField Ap
  let M := LocalizedModule S N
  let loc : N →ₗ[A] M := LocalizedModule.mkLinearMap S N
  let T := k ⊗[Ap] M
  let b := Module.finBasis k T
  let n := Module.finrank k T
  have hres : Function.Surjective (IsLocalRing.residue Ap) := IsLocalRing.residue_surjective
  have hsurj : ∀ t : T, ∃ m : M, (1 : k) ⊗ₜ[Ap] m = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x y =>
      obtain ⟨v, rfl⟩ := hres x
      refine ⟨v • y, ?_⟩
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      change IsLocalRing.residue Ap v * 1 = _
      rw [mul_one]
    | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, by rw [TensorProduct.tmul_add]⟩
  choose m hm using fun i => hsurj (b i)
  have hloc : ∀ i, ∃ (z : J) (s : S), s • m i = loc (c z) := by
    intro i
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalizedModule.surj S loc (m i)
    obtain ⟨z, rfl⟩ := hc x
    exact ⟨z, s, e⟩
  choose z s hzs using hloc
  let f : Fin n → A := fun i => (z i : A)
  -- generation
  have hspan : Submodule.span Ap (Set.range m) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis m b hm
  let NN : Submodule A N := Submodule.span A (Set.range fun i => c (z i))
  have hP : ∀ y : M, ∃ τ : A, τ ∈ S ∧ ∃ w ∈ NN, τ • y = loc w := by
    intro y
    have hy : y ∈ Submodule.span Ap (Set.range m) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨s i, (s i).2, _, Submodule.subset_span ⟨i, rfl⟩, hzs i⟩
    | zero => exact ⟨1, S.one_mem, 0, NN.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨τ₁, h₁', w₁, h₁, e₁⟩ := hx
      obtain ⟨τ₂, h₂', w₂, h₂, e₂⟩ := hy
      refine ⟨τ₁ * τ₂, S.mul_mem h₁' h₂', τ₂ • w₁ + τ₁ • w₂, NN.add_mem (NN.smul_mem _ h₁) (NN.smul_mem _ h₂), ?_⟩
      rw [smul_add, map_add, map_smul, map_smul, ← e₁, ← e₂, mul_comm τ₁ τ₂, mul_smul, mul_comm τ₂ τ₁,
        mul_smul]
    | smul v x _ hx =>
      obtain ⟨τ₁, h₁', w₁, h₁, e₁⟩ := hx
      obtain ⟨⟨u, σ⟩, hu⟩ := IsLocalization.surj S v
      refine ⟨σ * τ₁, S.mul_mem σ.2 h₁', u • w₁, NN.smul_mem _ h₁, ?_⟩
      rw [map_smul, ← e₁, ← algebraMap_smul Ap u, ← hu, mul_smul (σ : A) τ₁, smul_comm τ₁ v x,
        ← algebraMap_smul Ap (σ : A) (v • (τ₁ • x)), smul_smul, mul_comm]
  have hw' : ∀ w ∈ NN, ∃ q : J, (q : A) ∈ Ideal.span (Set.range f) ∧ c q = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨z i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
    | zero => exact ⟨0, Ideal.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨q₁, a₁, rfl⟩ := hx
      obtain ⟨q₂, a₂, rfl⟩ := hy
      exact ⟨q₁ + q₂, Ideal.add_mem _ a₁ a₂, map_add _ _ _⟩
    | smul v x _ hx =>
      obtain ⟨q, a₁, rfl⟩ := hx
      exact ⟨v • q, Ideal.mul_mem_left _ v a₁, map_smul _ _ _⟩
  have hgen : ∀ y ∈ J, ∃ σ ∉ p, σ * y ∈ Ideal.span (insert a (Set.range f)) ⊔ J ^ 2 := by
    intro y hy
    obtain ⟨τ, hτ, w, hw, e⟩ := hP (loc (c ⟨y, hy⟩))
    obtain ⟨τ', hτ'⟩ := (IsLocalizedModule.eq_iff_exists S loc).1 (show loc (τ • c ⟨y, hy⟩) = loc w by
      rw [map_smul]; exact e)
    obtain ⟨q, hq, rfl⟩ := hw' w hw
    have h0 : c ((τ' : A) • (τ • (⟨y, hy⟩ : J) - q)) = 0 := by
      rw [map_smul, map_sub, map_smul, smul_sub, sub_eq_zero]
      exact hτ'
    have h1 := hk _ h0
    refine ⟨τ' * τ, S.mul_mem τ'.2 hτ, ?_⟩
    have e1 : (τ' : A) * τ * y = (τ' : A) * q + (((τ' : A) • (τ • (⟨y, hy⟩ : J) - q) : J) : A) := by
      change (τ' : A) * τ * y = (τ' : A) * q + (τ' : A) * (τ * y - q)
      ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.span_mono (Set.subset_insert _ _) hq))) ?_
    refine (sup_le ?_ ?_ : J ^ 2 ⊔ Ideal.span {a} ≤ _) h1
    · exact le_sup_right
    · exact le_sup_of_le_left (Ideal.span_mono (by simp))
  obtain ⟨h₂, hh₂, hh₂'⟩ := exists_mul_mem_of_local hJ p hp hgen
  -- the derivations
  have hFin : Module.Finite Ap M := inferInstance
  let toT : M →ₗ[Ap] T := TensorProduct.mk Ap k M 1
  let c0 : Fin n → (M →ₗ[Ap] k) := fun l => ((b.coord l).restrictScalars Ap) ∘ₗ toT
  let e0 : Fin n → (Ω[A⁄R] →ₗ[A] k) := fun l => ((c0 l).restrictScalars A) ∘ₗ loc ∘ₗ ψ
  let res : Ap →ₗ[A] k := (Algebra.linearMap Ap k).restrictScalars A
  have hres' : Function.Surjective res := hres
  have hlift : ∀ l, ∃ e : Ω[A⁄R] →ₗ[A] Ap, res ∘ₗ e = e0 l := fun l =>
    Module.projective_lifting_property res (e0 l) hres'
  choose e he using hlift
  let Mat : Matrix (Fin n) (Fin n) Ap := fun l i => e l (KaehlerDifferential.D R A (f i))
  have hsu : ∀ i, algebraMap A Ap (s i) ≠ 0 ∧ IsUnit (algebraMap A Ap (s i)) := fun i =>
    ⟨(IsLocalization.map_units Ap (s i)).ne_zero, IsLocalization.map_units Ap (s i)⟩
  have hMat : ∀ l i, IsLocalRing.residue Ap (Mat l i) =
      if l = i then IsLocalRing.residue Ap (algebraMap A Ap (s i)) else 0 := by
    intro l i
    have h1 : res (e l (KaehlerDifferential.D R A (f i))) = e0 l (KaehlerDifferential.D R A (f i)) :=
      LinearMap.congr_fun (he l) _
    change res (e l (KaehlerDifferential.D R A (f i))) = _
    rw [h1]
    change b.coord l (toT (loc (ψ (KaehlerDifferential.D R A (z i))))) = _
    rw [hψ, ← hzs i]
    have h2 : toT ((s i : A) • m i) = IsLocalRing.residue Ap (algebraMap A Ap (s i)) • b i := by
      rw [← algebraMap_smul Ap (s i : A) (m i), map_smul]
      change algebraMap A Ap (s i) • ((1 : k) ⊗ₜ[Ap] m i) = _
      rw [hm i]
      exact (IsScalarTower.algebraMap_smul k (algebraMap A Ap (s i)) (b i)).symm
    change b.coord l (toT ((s i : A) • m i)) = _
    rw [h2, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hli : l = i
    · subst hli; simp
    · simp [hli, Ne.symm hli]
  have hdet : IsUnit Mat.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue Ap).mapMatrix Mat =
        Matrix.diagonal fun i => IsLocalRing.residue Ap (algebraMap A Ap (s i)) := by
      ext l i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMat, Matrix.diagonal_apply]
      split_ifs with h
      · rw [h]
      · rfl
    rw [this, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hsu i).2
  let W := Mat⁻¹
  have hW : W * Mat = 1 := Matrix.nonsing_inv_mul _ hdet
  let e' : Fin n → (Ω[A⁄R] →ₗ[A] Ap) := fun k' => ∑ l, W k' l • e l
  have he' : ∀ k' i, e' k' (KaehlerDifferential.D R A (f i)) = if k' = i then 1 else 0 := by
    intro k' i
    have := congrFun (congrFun hW k') i
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    simp [e', LinearMap.sum_apply, Mat]
  have hl : ∀ k', ∃ (hh : Ω[A⁄R] →ₗ[A] A) (s' : S), Algebra.linearMap A Ap ∘ₗ hh = s' • e' k' := fun k' =>
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S (Algebra.linearMap A Ap) (e' k')
  choose hh s' hhs using hl
  have hrel : ∀ k' i, algebraMap A Ap (hh k' (KaehlerDifferential.D R A (f i))) =
      algebraMap A Ap ((s' k' : A) * if k' = i then 1 else 0) := by
    intro k' i
    have := LinearMap.congr_fun (hhs k') (KaehlerDifferential.D R A (f i))
    refine this.trans ?_
    change (s' k' : A) • e' k' _ = _
    rw [he', map_mul, Algebra.smul_def]
    congr 1
    split_ifs <;> simp
  have ht : ∀ k' i, ∃ t : S, (t : A) * hh k' (KaehlerDifferential.D R A (f i)) =
      t * ((s' k' : A) * if k' = i then 1 else 0) := fun k' i =>
    (IsLocalization.eq_iff_exists S Ap).1 (hrel k' i)
  choose t ht using ht
  let g : A := h₂ * ((∏ k', (s' k' : A)) * ∏ k', ∏ i, (t k' i : A))
  have hg : g ∉ p := by
    refine S.mul_mem hh₂ (S.mul_mem (S.prod_mem fun k' _ => (s' k').2)
      (S.prod_mem fun k' _ => S.prod_mem fun i _ => (t k' i).2))
  let L := Localization.Away g
  have hgu : IsUnit (algebraMap A L g) := IsLocalization.Away.algebraMap_isUnit g
  have hdvd : ∀ x, x ∣ g → IsUnit (algebraMap A L x) := fun x hx =>
    isUnit_of_dvd_unit (map_dvd _ hx) hgu
  have hs'u : ∀ k', IsUnit (algebraMap A L (s' k')) := fun k' => hdvd _ <|
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ k')) _) _
  have htu : ∀ k' i, IsUnit (algebraMap A L (t k' i)) := fun k' i => hdvd _ <|
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem (fun i => (t k' i : A)) (Finset.mem_univ i)).trans
      (Finset.dvd_prod_of_mem (fun k' => ∏ i, (t k' i : A)) (Finset.mem_univ k'))) _) _
  let D : Fin n → Derivation R A L := fun k' =>
    (((hs'u k').unit⁻¹ : Lˣ) : L) • (((Algebra.linearMap A L) ∘ₗ hh k').compDer (KaehlerDifferential.D R A))
  refine ⟨g, hg, n, f, D, fun i => (z i).2, fun i k' => ?_, fun y hy => ?_⟩
  · have h1 : algebraMap A L (hh k' (KaehlerDifferential.D R A (f i))) =
        algebraMap A L (s' k') * if k' = i then 1 else 0 := by
      have := congrArg (algebraMap A L) (ht k' i)
      rw [map_mul, map_mul] at this
      have h3 := (htu k' i).mul_left_cancel this
      rw [h3, map_mul]
      congr 1
      split_ifs <;> simp
    change (((hs'u k').unit⁻¹ : Lˣ) : L) * algebraMap A L (hh k' (KaehlerDifferential.D R A (f i))) = _
    rw [h1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    simp only [eq_comm]
  · have : g = ((∏ k', (s' k' : A)) * ∏ k', ∏ i, (t k' i : A)) * h₂ := mul_comm _ _
    rw [this, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hh₂' y hy)

end Conormal

end AlgMag.Dil

namespace AlgMag.Dil

section Section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]

/-- The section `σ̃ : A → Q = A/(J² + a)` gives the conormal data of `exists_pres_of_conormal`. -/
theorem exists_pres_of_section {J : Ideal A} (r : R) (ha : algebraMap R A r ∈ J) (hJ : J.FG)
    (σ : A →+* A ⧸ (J ^ 2 ⊔ Ideal.span {algebraMap R A r}))
    (hσ0 : ∀ z ∈ J, σ z = 0)
    (hσ1 : ∀ x, Ideal.Quotient.mk _ x - σ x ∈ J.map (Ideal.Quotient.mk (J ^ 2 ⊔ Ideal.span {algebraMap R A r})))
    (hσR : ∀ s : R, σ (algebraMap R A s) = Ideal.Quotient.mk _ (algebraMap R A s))
    (p : Ideal A) [p.IsPrime] (hp : J ≤ p) :
    ∃ g ∉ p, ∃ (n : ℕ) (f : Fin n → A) (D : Fin n → Derivation R A (Localization.Away g)),
      (∀ i, f i ∈ J) ∧ (∀ i k, D k (f i) = if i = k then 1 else 0) ∧
      ∀ z ∈ J, g * z ∈ Ideal.span (insert (algebraMap R A r) (Set.range f)) := by
  let a := algebraMap R A r
  let K := J ^ 2 ⊔ Ideal.span {a}
  let mk := Ideal.Quotient.mk K
  let N : Ideal (A ⧸ K) := J.map mk
  have hNN : ∀ x ∈ N, ∀ y ∈ N, x * y = 0 := by
    intro x hx y hy
    have h1 : x * y ∈ N * N := Ideal.mul_mem_mul hx hy
    have h2 : N * N = ⊥ := by
      change J.map mk * J.map mk = ⊥
      rw [← Ideal.map_mul, ← pow_two, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact le_sup_left
    rw [h2] at h1
    exact h1
  have hzN : ∀ z ∈ J, mk z ∈ N := fun z hz => Ideal.mem_map_of_mem _ hz
  let δ : A → N := fun x => ⟨mk x - σ x, hσ1 x⟩
  let Dl : A →ₗ[R] N :=
    { toFun := δ
      map_add' := fun x y => Subtype.ext (by
        change mk (x + y) - σ (x + y) = (mk x - σ x) + (mk y - σ y)
        rw [map_add, map_add]; ring)
      map_smul' := fun s x => Subtype.ext (by
        change mk (s • x) - σ (s • x) = s • (mk x - σ x)
        have e : algebraMap R (A ⧸ K) s = mk (algebraMap R A s) := rfl
        rw [Algebra.smul_def s (mk x - σ x), Algebra.smul_def, map_mul, map_mul, hσR, e]
        ring) }
  let DN : Derivation R A N := Derivation.mk' Dl fun x y => Subtype.ext (by
    change mk (x * y) - σ (x * y) = mk x * (mk y - σ y) + mk y * (mk x - σ x)
    have := hNN _ (hσ1 x) _ (hσ1 y)
    rw [map_mul, map_mul]
    linear_combination -this)
  let c : J →ₗ[A] N :=
    { toFun := fun z => ⟨mk z, hzN z z.2⟩
      map_add' := fun x y => Subtype.ext (map_add mk _ _)
      map_smul' := fun s x => Subtype.ext (map_mul mk _ _) }
  have hc : Function.Surjective c := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).1 hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have : Module.Finite A J := Module.Finite.iff_fg.2 hJ
  have : Module.Finite A N := Module.Finite.of_surjective c hc
  let ψ : Ω[A⁄R] →ₗ[A] N := DN.liftKaehlerDifferential
  refine exists_pres_of_conormal a ha hJ ψ c hc (fun z => ?_) (fun z hz => ?_) p hp
  · rw [Derivation.liftKaehlerDifferential_comp_D]
    refine Subtype.ext ?_
    change mk z - σ z = mk z
    rw [hσ0 z z.2, sub_zero]
  · have : mk z = 0 := congrArg Subtype.val hz
    exact Ideal.Quotient.eq_zero_iff_mem.1 this

end Section

section Iso

variable {L : Type u} [CommRing L] {n : ℕ}

/-- `L[y]/(a y - f) → L[J/a]`, for `J = (a, f)`. -/
theorem presRing_equiv_dilatation (a : L) (f : Fin n → L) {J : Ideal L}
    (hJ : J = Ideal.span (insert a (Set.range f)))
    (hreg : ∀ x : PresRing a f, Ideal.Quotient.mk (presIdeal a f) (MvPolynomial.C a) * x = 0 → x = 0) :
    (∃ e : PresRing a f ≃+* dilatation J a, a ∈ J ∧
      ∀ q : L, e (Ideal.Quotient.mk (presIdeal a f) (MvPolynomial.C q)) = algebraMap L _ q) := by
  classical
  have ha : a ∈ J := hJ ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hf : ∀ i, f i ∈ J := fun i => hJ ▸ Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  let ev : MvPolynomial (Fin n) L →+* dilatation J a :=
    MvPolynomial.eval₂Hom (algebraMap L (dilatation J a)) fun i => dilOverA (hf i)
  have hev : presIdeal a f ≤ RingHom.ker ev := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change ev _ = 0
    simp only [map_sub, map_mul, ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    rw [algebraMap_mul_dilOverA, sub_self]
  let ψ : PresRing a f →+* dilatation J a := Ideal.Quotient.lift _ ev fun x hx => hev hx
  let mk := Ideal.Quotient.mk (presIdeal a f)
  -- every element is a fraction
  have hfrac : ∀ z : MvPolynomial (Fin n) L, ∃ (m : ℕ) (w : L), mk (MvPolynomial.C (a ^ m)) * mk z = mk (MvPolynomial.C w) := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C w => exact ⟨0, w, by simp⟩
    | add x y hx hy =>
      obtain ⟨m, u, hu⟩ := hx
      obtain ⟨l, v, hv⟩ := hy
      refine ⟨m + l, a ^ l * u + a ^ m * v, ?_⟩
      simp only [map_add, map_mul, map_pow, pow_add] at hu hv ⊢
      linear_combination (mk (MvPolynomial.C a) ^ l) * hu + (mk (MvPolynomial.C a) ^ m) * hv
    | mul_X x i hx =>
      obtain ⟨m, u, hu⟩ := hx
      refine ⟨m + 1, u * f i, ?_⟩
      have hi : mk (MvPolynomial.C a) * mk (MvPolynomial.X i) = mk (MvPolynomial.C (f i)) := by
        rw [← map_mul]
        exact Ideal.Quotient.eq.2 (Ideal.subset_span ⟨i, rfl⟩)
      simp only [map_mul, map_pow, pow_succ] at hu hi ⊢
      linear_combination (mk (MvPolynomial.X i) * mk (MvPolynomial.C a)) * hu + (mk (MvPolynomial.C u)) * hi
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨m, w, hw⟩ := hfrac z
    have h1 : algebraMap L (dilatation J a) w = 0 := by
      have := congrArg ψ hw
      have e : ∀ q : L, ψ (mk (MvPolynomial.C q)) = algebraMap L (dilatation J a) q := fun q => by
        change ev _ = _
        simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [map_mul, e, e] at this
      rw [← this]
      have hx' : ψ (mk z) = 0 := hx
      rw [hx', mul_zero]
    have h2 : algebraMap L (Localization.Away a) w = 0 := congrArg Subtype.val h1
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) w).1 h2
    have hzero : mk (MvPolynomial.C a) ^ (k + m) * mk z = 0 := by
      have := congrArg (mk (MvPolynomial.C a) ^ k * ·) hw
      simp only [map_mul, map_pow] at this hk
      rw [pow_add, mul_assoc]
      refine this.trans ?_
      have hk' := congrArg mk (congrArg MvPolynomial.C hk)
      simpa [map_mul, map_pow] using hk'
    clear hw h1 h2 hk
    generalize k + m = e at hzero
    induction e with
    | zero => simpa using hzero
    | succ e ih =>
      exact ih (hreg _ (by rw [← hzero, pow_succ]; ring))
  have hsurj : Function.Surjective ψ := by
    have hr : (⊤ : Subalgebra L (dilatation J a)) = ⊤ := rfl
    rintro ⟨u, hu⟩
    induction hu using Algebra.adjoin_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      have hx' := hx
      rw [hJ] at hx'
      have key : ∃ w, ((ψ w : dilatation J a) : Localization.Away a) = dilFrac a x 1 := by
        clear hx
        induction hx' using Submodule.span_induction with
        | mem y hy =>
          rcases hy with hy | ⟨i, rfl⟩
          · refine ⟨1, ?_⟩
            rw [map_one, hy]
            have h1 := algebraMap_mul_dilOverA (a := a) ha
            have h2 : algebraMap L (Localization.Away a) a * dilFrac a a 1 = algebraMap L _ a :=
              congrArg Subtype.val h1
            have hu : IsUnit (algebraMap L (Localization.Away a) a) := IsLocalization.Away.algebraMap_isUnit a
            exact (hu.mul_left_cancel (h2.trans (mul_one _).symm)).symm
          · refine ⟨mk (MvPolynomial.X i), ?_⟩
            change ((ev (MvPolynomial.X i) : dilatation J a) : Localization.Away a) = _
            simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
            rfl
        | zero => exact ⟨0, by rw [map_zero]; simp [dilFrac]⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨q, hq⟩ := hy
          exact ⟨p + q, by rw [map_add, dilFrac_add, ← hp, ← hq]; rfl⟩
        | smul c x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨mk (MvPolynomial.C c) * p, ?_⟩
          have e : ψ (mk (MvPolynomial.C c)) = algebraMap L (dilatation J a) c := by
            change ev _ = _
            simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
          rw [map_mul, e, smul_eq_mul]
          have h3 := dilFrac_mul a c x 0 1
          rw [zero_add, dilFrac_zero_right] at h3
          rw [h3, ← hp]
          rfl
      obtain ⟨w, hw⟩ := key
      exact ⟨w, Subtype.ext hw⟩
    | algebraMap q => exact ⟨mk (MvPolynomial.C q), by
        change ev _ = _
        simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rfl⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨p, hp⟩ := ihx
      obtain ⟨q, hq⟩ := ihy
      exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩, ha, fun q => ?_⟩
  change ev _ = _
  simp only [ev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]

end Iso

end AlgMag.Dil

namespace AlgMag.Dil

section Sec

variable {R A R₀ C' : Type u} [CommRing R] [CommRing A] [CommRing R₀] [CommRing C'] [Algebra R A]

/-- `C' = A/J` formally smooth over `R₀ = R/r` gives the section of `A/(J² + a) → A/J`. -/
theorem exists_section (r : R) (φ₀ : R →+* R₀) (hφ₀ : Function.Surjective φ₀)
    (hker : RingHom.ker φ₀ = Ideal.span {r}) (ψ₀ : R₀ →+* C') (hψ₀ : ψ₀.FormallySmooth)
    (e : A →+* C') (he : Function.Surjective e) {J : Ideal A} (hJ : RingHom.ker e = J)
    (hc : ∀ s, e (algebraMap R A s) = ψ₀ (φ₀ s)) :
    ∃ σ : A →+* A ⧸ (J ^ 2 ⊔ Ideal.span {algebraMap R A r}), (∀ z ∈ J, σ z = 0) ∧
      (∀ x, Ideal.Quotient.mk _ x - σ x ∈ J.map (Ideal.Quotient.mk (J ^ 2 ⊔ Ideal.span {algebraMap R A r}))) ∧
      ∀ s : R, σ (algebraMap R A s) = Ideal.Quotient.mk _ (algebraMap R A s) := by
  let K := J ^ 2 ⊔ Ideal.span {algebraMap R A r}
  let mk := Ideal.Quotient.mk K
  let m0 : R →+* A ⧸ K := mk.comp (algebraMap R A)
  have hm0 : RingHom.ker φ₀ ≤ RingHom.ker m0 := by
    rw [hker]
    refine Ideal.span_le.2 ?_
    rintro _ rfl
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  let θ : R₀ →+* A ⧸ K := φ₀.liftOfSurjective hφ₀ ⟨m0, hm0⟩
  have hθ : ∀ s, θ (φ₀ s) = mk (algebraMap R A s) := fun s =>
    φ₀.liftOfSurjective_comp_apply hφ₀ ⟨m0, hm0⟩ s
  letI : Algebra R₀ (A ⧸ K) := θ.toAlgebra
  letI : Algebra R₀ C' := ψ₀.toAlgebra
  haveI : Algebra.FormallySmooth R₀ C' := hψ₀
  let N : Ideal (A ⧸ K) := J.map mk
  have hN : N ^ 2 = ⊥ := by
    change (J.map mk) ^ 2 = ⊥
    rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_left
  let mN := Ideal.Quotient.mk N
  let t0 : A →+* (A ⧸ K) ⧸ N := mN.comp mk
  have ht0 : RingHom.ker e ≤ RingHom.ker t0 := by
    rw [hJ]
    intro z hz
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hz)
  let τ₀ : C' →+* (A ⧸ K) ⧸ N := e.liftOfSurjective he ⟨t0, ht0⟩
  have hτ₀ : ∀ x, τ₀ (e x) = mN (mk x) := fun x => e.liftOfSurjective_comp_apply he ⟨t0, ht0⟩ x
  let τ : C' →ₐ[R₀] (A ⧸ K) ⧸ N :=
    { τ₀ with
      commutes' := fun q => by
        obtain ⟨s, rfl⟩ := hφ₀ q
        change τ₀ (ψ₀ (φ₀ s)) = mN (θ (φ₀ s))
        rw [← hc, hτ₀, hθ] }
  obtain ⟨σ', hσ'⟩ := Algebra.FormallySmooth.comp_surjective R₀ C' N hN τ
  have hσ'' : ∀ y, mN (σ' y) = τ₀ y := fun y => DFunLike.congr_fun hσ' y
  refine ⟨(σ' : C' →+* A ⧸ K).comp e, fun z hz => ?_, fun x => ?_, fun s => ?_⟩
  · have : e z = 0 := by
      have : z ∈ RingHom.ker e := hJ ▸ hz
      exact this
    change σ' (e z) = 0
    rw [this, map_zero]
  · change mk x - σ' (e x) ∈ N
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hσ'', hτ₀, sub_self]
  · change σ' (e (algebraMap R A s)) = mk _
    rw [hc]
    have := σ'.commutes (φ₀ s)
    refine this.trans (hθ s)

end Sec

section Local

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]

lemma smooth_of_bij {P Q T : Type u} [CommRing P] [CommRing Q] [CommRing T] (f : P →+* Q) (hf : f.Smooth)
    (e : Q →+* T) (he : Function.Bijective e) : (e.comp f).Smooth :=
  hf.comp (RingHom.Smooth.of_bijective he)

/-- **[Mayeux-Richarz-Romagny, Prop. 2.16], affine form.** Locally on `A`, the dilatation is smooth
over `R`. -/
theorem smooth_dilatation_local (r : R) (hr : ∀ x : R, r * x = 0 → x = 0) {J : Ideal A}
    (ha : algebraMap R A r ∈ J) (hJ : J.FG)
    (σ : A →+* A ⧸ (J ^ 2 ⊔ Ideal.span {algebraMap R A r}))
    (hσ0 : ∀ z ∈ J, σ z = 0)
    (hσ1 : ∀ x, Ideal.Quotient.mk _ x - σ x ∈ J.map (Ideal.Quotient.mk (J ^ 2 ⊔ Ideal.span {algebraMap R A r})))
    (hσR : ∀ s : R, σ (algebraMap R A s) = Ideal.Quotient.mk _ (algebraMap R A s))
    (p : Ideal A) [p.IsPrime] :
    ∃ g ∉ p, ∀ (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away g L],
      ((algebraMap L (dilatation (J.map (algebraMap A L)) (algebraMap A L (algebraMap R A r)))).comp
        ((algebraMap A L).comp (algebraMap R A))).Smooth := by
  classical
  have hRA : (algebraMap R A).Smooth := RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  by_cases hp : J ≤ p
  · obtain ⟨g, hg, n, f, D, hf, hD, hgen⟩ := exists_pres_of_section r ha hJ σ hσ0 hσ1 hσR p hp
    refine ⟨g, hg, fun L _ _ _ => ?_⟩
    letI : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
    haveI : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq' rfl
    have hAL : Algebra.Smooth A L := Algebra.Smooth.of_isLocalization_Away g
    haveI : Algebra.FormallySmooth R L := .comp R A L
    haveI : Algebra.FinitePresentation R L := .trans R A L
    let φ : Localization.Away g →ₗ[A] L :=
      (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) L).toLinearMap
    let D' : Fin n → Derivation R A L := fun k => φ.compDer (D k)
    have hD' : ∀ i k, D' k (f i) = if i = k then 1 else 0 := by
      intro i k
      change φ (D k (f i)) = _
      rw [hD]
      split_ifs
      · exact map_one (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) L)
      · exact map_zero φ
    let a' : L := algebraMap R L r
    let f' : Fin n → L := fun i => algebraMap A L (f i)
    haveI hfs : Algebra.FormallySmooth R (PresRing a' f') := formallySmooth_presRing g r f D' hD'
    have hIfg : (presIdeal a' f').FG := ⟨(Finset.univ.image fun i =>
        MvPolynomial.C a' * MvPolynomial.X i - MvPolynomial.C (f' i)), by simp [presIdeal]⟩
    haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) L) := .trans R L _
    haveI hfp : Algebra.FinitePresentation R (PresRing a' f') := .quotient hIfg
    haveI : Algebra.Smooth R (PresRing a' f') := ⟨inferInstance, inferInstance⟩
    have hreg : ∀ x : PresRing a' f', Ideal.Quotient.mk (presIdeal a' f') (MvPolynomial.C a') * x = 0 → x = 0 := by
      intro x hx
      have reg : IsSMulRegular R r := fun u v e => by
        have : r * (u - v) = 0 := by
          simp only [smul_eq_mul] at e; rw [mul_sub, e, sub_self]
        exact sub_eq_zero.1 (hr _ this)
      refine reg.of_flat (S := PresRing a' f') (a₁ := x) (a₂ := 0) ?_
      change algebraMap R (PresRing a' f') r * x = algebraMap R (PresRing a' f') r * 0
      rw [mul_zero]
      exact hx
    have hJmap : J.map (algebraMap A L) = Ideal.span (insert a' (Set.range f')) := by
      apply le_antisymm
      · refine Ideal.map_le_iff_le_comap.2 fun z hz => ?_
        have h1 := Ideal.mem_map_of_mem (algebraMap A L) (hgen z hz)
        rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, map_mul] at h1
        obtain ⟨v, hv⟩ := (IsLocalization.Away.algebraMap_isUnit (S := L) g).exists_left_inv
        have := Ideal.mul_mem_left _ v h1
        rwa [← mul_assoc, hv, one_mul] at this
      · refine Ideal.span_le.2 ?_
        rintro _ (rfl | ⟨i, rfl⟩)
        · exact Ideal.mem_map_of_mem _ ha
        · exact Ideal.mem_map_of_mem _ (hf i)
    obtain ⟨e, hae, hec⟩ := presRing_equiv_dilatation a' f' hJmap hreg
    have hsm : (algebraMap R (PresRing a' f')).Smooth := RingHom.smooth_algebraMap.2 inferInstance
    have := smooth_of_bij _ hsm e.toRingHom e.bijective
    have eqq : e.toRingHom.comp (algebraMap R (PresRing a' f')) =
        (algebraMap L (dilatation (J.map (algebraMap A L)) a')).comp ((algebraMap A L).comp (algebraMap R A)) :=
      RingHom.ext fun s => hec _
    rw [eqq] at this
    exact this
  · obtain ⟨g, hgJ, hg⟩ := SetLike.not_le_iff_exists.1 hp
    refine ⟨g, hg, fun L _ _ _ => ?_⟩
    have hAL : (algebraMap A L).Smooth := RingHom.smooth_algebraMap.2 (Algebra.Smooth.of_isLocalization_Away g)
    let a' : L := algebraMap A L (algebraMap R A r)
    have htop : J.map (algebraMap A L) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hgJ) (IsLocalization.Away.algebraMap_isUnit g)
    have hLA : (algebraMap L (Localization.Away a')).Smooth :=
      RingHom.smooth_algebraMap.2 (Algebra.Smooth.of_isLocalization_Away a')
    let incl : dilatation (J.map (algebraMap A L)) a' →+* Localization.Away a' :=
      (dilatation (J.map (algebraMap A L)) a').val
    have hbij : Function.Bijective incl := by
      refine ⟨Subtype.val_injective, fun u => ?_⟩
      obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers a') u
      have hm : x ∈ (J.map (algebraMap A L)) ^ n := by
        rw [htop, Ideal.top_pow]; exact Submodule.mem_top
      refine ⟨⟨dilFrac a' x n, dilFrac_mem_dilatation hm⟩, ?_⟩
      have hu : IsUnit ((algebraMap L (Localization.Away a') a') ^ n) :=
        (IsLocalization.Away.algebraMap_isUnit a').pow n
      have hx' : u * (algebraMap L (Localization.Away a') a') ^ n = algebraMap L _ x := by
        simpa using hx
      refine hu.mul_right_cancel ?_
      rw [hx']
      have h4 := dilFrac_mul_pow a' x n
      rw [map_pow] at h4
      exact h4
    let eq := RingEquiv.ofBijective incl hbij
    have hf0 : ((algebraMap L (Localization.Away a')).comp ((algebraMap A L).comp (algebraMap R A))).Smooth :=
      (hRA.comp hAL).comp hLA
    have := smooth_of_bij _ hf0 eq.symm.toRingHom eq.symm.bijective
    convert this using 1
    refine RingHom.ext fun s => ?_
    exact (eq.symm_apply_eq.2 rfl).symm

end Local

end AlgMag.Dil

/-! ### Corollary 13.3, from the smoothness of the dilatation -/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry



namespace AlgMag.Dil

open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData} {M : Type u} [AddCommGroup M]
  {X Y B ZX ZY ZB : Over S} {j : Y ⟶ X} {b : B ⟶ X}
  {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}

/-- **Corollary 13.3, reduced to [Mayeux-Richarz-Romagny, Prop. 2.16].** The smoothness of
`Bl_Y^D X → S`, which is what that proposition provides, is the hypothesis `[Smooth B.hom]`. Then
`(Bl_Y^D X)^N → S` is smooth (Corollary 11.2) and `(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over
`X^N` (Proposition 13.1). -/
theorem cor13_3_of_smooth (hs : Stable j act actY) (hD : IsDilatation I j b) [Mono j] [Smooth B.hom]
    {N : AddSubmonoid M} (rX : RepresentsAttractor act N (yoneda.obj ZX))
    (rY : RepresentsAttractor actY N (yoneda.obj ZY))
    (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB))
    {B' : Over S} {b' : B' ⟶ ZX} (hB' : IsDilatation I (jN hs rX rY) b') :
    Smooth ZB.hom ∧ IsDilatation I (jN hs rX rY) (bN hs hD rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD rX rB := by
  have h : Smooth ZB.hom := AlgMag.prop1615_ii_attr (blAction hs hD) N rB
  have : Flat ZB.hom := inferInstance
  exact ⟨h, prop13_1 hs hD rX rY rB hB'⟩

end AlgMag.Dil

/-! ### [Mayeux-Richarz-Romagny, Prop. 2.16] for schemes, and Corollary 13.3 -/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace


namespace AlgMag.Dil

open GB

variable {S : Scheme.{u}} {I : S.IdealSheafData} {X Y : Over S} {j : Y ⟶ X}

/-- `S'` is an effective Cartier divisor of `S`. -/
def IsEffCartier (I : S.IdealSheafData) : Prop :=
  LocPrincipal I ∧ ∀ (U : S.affineOpens) (r : Γ(S, U.1)), I.ideal U = Ideal.span {r} →
    ∀ x : Γ(S, U.1), r * x = 0 → x = 0

/-- The restriction of a dilatation over an open. -/
theorem IsDilOn.restrict_top {B : Over S} {b : B ⟶ X} (h : IsDilatation I j b) (V : X.left.Opens) :
    let W : B.left.Opens := b.left ⁻¹ᵁ V
    IsDilOn I j V (Over.homMk (U := Over.mk (W.ι ≫ B.hom)) W.ι rfl ≫ b) := by
  intro W
  let m : Over.mk (W.ι ≫ B.hom) ⟶ B := Over.homMk W.ι rfl
  have hflat : Flat m.left := inferInstanceAs (Flat W.ι)
  have hmono : Mono m := ⟨fun f g e => Over.OverMorphism.ext
    ((cancel_mono W.ι).1 (congrArg (fun q => q.left) e))⟩
  refine ⟨h.reg.of_flat m, ?_, h.factors.comp j m, ?_, ?_⟩
  · rintro z -
    exact z.2
  · intro T hT x hx hf
    obtain ⟨f, hf'⟩ := h.exists_lift hT x (fun _ _ => trivial) hf
    have hr : Set.range f.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change b.left (f.left z) ∈ V
      have : (f ≫ b).left z ∈ V := by rw [hf']; exact hx (Set.mem_univ z)
      exact this
    let lf : T.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι f.left hr
    have hlf : lf ≫ W.ι = f.left := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk lf ?_, ?_⟩
    · change lf ≫ W.ι ≫ B.hom = T.hom
      rw [← Category.assoc, hlf]
      exact Over.w f
    · rw [← hf', ← Category.assoc]
      congr 1
      exact Over.OverMorphism.ext hlf
  · intro T hT f g e
    exact (cancel_mono m).1 (h.uniq hT _ _ (by simpa only [Category.assoc] using e))

lemma appLE_congr' {P Q : Scheme.{u}} {f g : P ⟶ Q} (h : f = g) (U : Q.Opens) (V : P.Opens) (e e') :
    f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

/-- **[Mayeux-Richarz-Romagny, Prop. 2.16].** `S'` an effective Cartier divisor of `S`, `X → S` smooth,
`Y` a closed subscheme of `X|_{S'}` with `Y → S'` smooth. Then `Bl_Y^D X → S` is smooth. -/
theorem smooth_of_isDilatation (hC : IsEffCartier I) [IsClosedImmersion j.left]
    {l : Y.left ⟶ I.subscheme} (hl : l ≫ I.subschemeι = Y.hom) [Smooth l] [Smooth X.hom]
    {B : Over S} {b : B ⟶ X} (h : IsDilatation I j b) : Smooth B.hom := by
  have hYI : LiesOver I Y := ⟨l, hl⟩
  have key : ∀ y : X.left, ∃ V' : X.left.Opens, y ∈ V' ∧ Smooth ((b.left ⁻¹ᵁ V').ι ≫ B.hom) := by
    intro y
    obtain ⟨U, hsU, r, hr⟩ := hC.1 (X.hom y)
    obtain ⟨V, hV, hy, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (x := y) (U := X.hom ⁻¹ᵁ U.1) hsU
    let φ := X.hom.appLE U.1 V hVU
    have hRA : φ.hom.Smooth := HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance U ⟨V, hV⟩ hVU
    letI : Algebra Γ(S, U.1) Γ(X.left, V) := φ.hom.toAlgebra
    haveI : Algebra.Smooth Γ(S, U.1) Γ(X.left, V) := hRA
    have hjV : IsAffineOpen (j.left ⁻¹ᵁ V) := hV.preimage j.left
    let W₀ : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U.1
    have hW₀ : IsAffineOpen W₀ := U.2.preimage I.subschemeι
    have e3 : j.left ≫ X.hom = l ≫ I.subschemeι := (Over.w j).trans hl.symm
    have hle : j.left ⁻¹ᵁ V ≤ l ⁻¹ᵁ W₀ := by
      intro t ht
      have h1 : X.hom (j.left t) ∈ U.1 := hVU ht
      have h2 : (j.left ≫ X.hom) t ∈ U.1 := h1
      rw [e3] at h2
      exact h2
    let e := j.left.app V
    have he : Function.Surjective e.hom := j.left.app_surjective V hV
    have hφ₀ : Function.Surjective (I.subschemeι.app U.1).hom := I.subschemeι_app_surjective U
    have hker : RingHom.ker (I.subschemeι.app U.1).hom = Ideal.span {r} := by
      rw [← hr]; exact I.ker_subschemeι_app U
    let ψ₀ := l.appLE W₀ (j.left ⁻¹ᵁ V) hle
    have hψ₀ : ψ₀.hom.Smooth := HasRingHomProperty.appLE (P := @Smooth) l inferInstance ⟨W₀, hW₀⟩ ⟨_, hjV⟩ hle
    have hcomp : ∀ s, e.hom (algebraMap Γ(S, U.1) Γ(X.left, V) s) = ψ₀.hom ((I.subschemeι.app U.1).hom s) := by
      intro s
      have h1 : φ ≫ j.left.app V = (j.left ≫ X.hom).appLE U.1 (j.left ⁻¹ᵁ V) (fun t ht => hVU ht) := by
        rw [Scheme.Hom.app_eq_appLE]
        exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
      have h2 : I.subschemeι.app U.1 ≫ ψ₀ =
          (l ≫ I.subschemeι).appLE U.1 (j.left ⁻¹ᵁ V) (hle.trans le_rfl) := by
        rw [Scheme.Hom.app_eq_appLE]
        exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
      have h3 := h1.trans ((appLE_congr' e3 _ _ _ _).trans h2.symm)
      exact congrArg (fun q => q.hom s) h3
    have hJdef : RingHom.ker e.hom = chartJ j (V := V) := rfl
    have ha : algebraMap Γ(S, U.1) Γ(X.left, V) r ∈ chartJ j (V := V) := chartA_mem j hVU hr hYI
    -- `J` is finitely generated
    have hJfg : (chartJ j (V := V)).FG := by
      letI : Algebra Γ(S, U.1) Γ(Y.left, j.left ⁻¹ᵁ V) := (e.hom.comp (algebraMap Γ(S, U.1) Γ(X.left, V))).toAlgebra
      have hfp : (ψ₀.hom.comp (I.subschemeι.app U.1).hom).FinitePresentation :=
        hψ₀.finitePresentation.comp (RingHom.FinitePresentation.of_surjective _ hφ₀ (by rw [hker]; exact ⟨{r}, by simp⟩))
      have heq : e.hom.comp (algebraMap Γ(S, U.1) Γ(X.left, V)) = ψ₀.hom.comp (I.subschemeι.app U.1).hom :=
        RingHom.ext hcomp
      haveI : Algebra.FinitePresentation Γ(S, U.1) Γ(Y.left, j.left ⁻¹ᵁ V) := by
        rw [← heq] at hfp
        exact RingHom.finitePresentation_algebraMap.1 hfp
      let eA : Γ(X.left, V) →ₐ[Γ(S, U.1)] Γ(Y.left, j.left ⁻¹ᵁ V) := { e.hom with commutes' := fun _ => rfl }
      exact Algebra.FinitePresentation.ker_fG_of_surjective eA he
    obtain ⟨σ, hσ0, hσ1, hσR⟩ := exists_section r (I.subschemeι.app U.1).hom hφ₀ hker ψ₀.hom hψ₀.formallySmooth
      e.hom he hJdef hcomp
    let q := hV.primeIdealOf ⟨y, hy⟩
    obtain ⟨g, hg, hS⟩ := smooth_dilatation_local r (hC.2 U r hr) ha hJfg σ hσ0 hσ1 hσR q.asIdeal
    let V' := X.left.basicOpen g
    have hV' : IsAffineOpen V' := hV.basicOpen g
    have hV'V : V' ≤ V := X.left.basicOpen_le g
    have hyV' : y ∈ V' := by
      have h1 : hV.fromSpec q = y := hV.fromSpec_primeIdealOf ⟨y, hy⟩
      have h2 : q ∈ hV.fromSpec ⁻¹ᵁ V' := by
        rw [hV.fromSpec_preimage_basicOpen]
        exact hg
      rw [← h1]
      exact h2
    refine ⟨V', hyV', ?_⟩
    have hLoc : IsLocalization.Away g Γ(X.left, V') := hV.isLocalization_basicOpen g
    have hSm := hS Γ(X.left, V')
    have hVU' : V' ≤ X.hom ⁻¹ᵁ U.1 := hV'V.trans hVU
    have eA : chartA hVU' r = algebraMap Γ(X.left, V) Γ(X.left, V') (algebraMap Γ(S, U.1) Γ(X.left, V) r) := by
      change X.hom.appLE U.1 V' hVU' r = X.left.presheaf.map (homOfLE hV'V).op (φ r)
      rw [← Scheme.Hom.appLE_map X.hom hVU (homOfLE hV'V).op]
      rfl
    have eJ : chartJ j (V := V') = (chartJ j (V := V)).map (algebraMap Γ(X.left, V) Γ(X.left, V')) := by
      have k1 := j.left.ker.map_ideal (U := ⟨V', hV'⟩) (V := ⟨V, hV⟩) hV'V
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at k1
      exact k1.symm
    rw [← eJ, ← eA] at hSm
    have hD := chart_isDilOn (j := j) hYI hV' hVU' hr
    obtain ⟨iso, hiso⟩ := (IsDilOn.restrict_top h V').exists_iso hD
    have hCh : Smooth (chartOver j hV' hVU' r).hom := by
      have e1 : (chartOver j hV' hVU' r).hom =
          Spec.map (CommRingCat.ofHom ((algebraMap Γ(X.left, V') (chartC j hVU' r)).comp
            ((algebraMap Γ(X.left, V) Γ(X.left, V')).comp (algebraMap Γ(S, U.1) Γ(X.left, V))))) ≫ U.2.fromSpec := by
        change chartB j hV' hVU' r ≫ X.hom = _
        have h5 : hV'.fromSpec ≫ X.hom = Spec.map (X.hom.appLE U.1 V' hVU') ≫ U.2.fromSpec :=
          (IsAffineOpen.SpecMap_appLE_fromSpec X.hom U.2 hV' hVU').symm
        have h6 : X.hom.appLE U.1 V' hVU' = CommRingCat.ofHom
            ((algebraMap Γ(X.left, V) Γ(X.left, V')).comp (algebraMap Γ(S, U.1) Γ(X.left, V))) := by
          rw [← Scheme.Hom.appLE_map X.hom hVU (homOfLE hV'V).op]
          rfl
        rw [chartB, Category.assoc, h5, h6, ← Category.assoc, ← Spec.map_comp]
        rfl
      rw [e1]
      have : Smooth (Spec.map (CommRingCat.ofHom ((algebraMap Γ(X.left, V') (chartC j hVU' r)).comp
            ((algebraMap Γ(X.left, V) Γ(X.left, V')).comp (algebraMap Γ(S, U.1) Γ(X.left, V)))))) :=
        (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hSm
      have hUa : IsAffineOpen U.1 := U.2
      have hfs : IsOpenImmersion hUa.fromSpec := inferInstance
      have hfs' : Smooth hUa.fromSpec := SmoothOfRelativeDimension.smooth 0 _
      exact MorphismProperty.comp_mem (@Smooth) _ _ this hfs'
    have e2 : (b.left ⁻¹ᵁ V').ι ≫ B.hom = iso.hom.left ≫ (chartOver j hV' hVU' r).hom :=
      (Over.w iso.hom).symm
    rw [e2]
    have hi : IsIso iso.hom.left := inferInstanceAs (IsIso ((Over.forget S).map iso.hom))
    have hi' : Smooth iso.hom.left := SmoothOfRelativeDimension.smooth 0 _
    exact MorphismProperty.comp_mem (@Smooth) _ _ hi' hCh
  choose V hyV hsm using key
  haveI hloc : IsZariskiLocalAtSource (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := (@Smooth : MorphismProperty Scheme.{u}))
    (fun x : B.left => b.left ⁻¹ᵁ V (b.left x)) ?_).2 (fun x => hsm _)
  refine top_le_iff.1 fun x _ => ?_
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hyV (b.left x)⟩

/-- **Corollary 13.3.** `S'` an effective Cartier divisor of `S`, `X` a smooth `S`-scheme with an
action of `D(M)_S`, `Y` a closed subscheme of `X|_{S'}`, smooth over `S'` and stable under the action,
`N` a submonoid of `M`. Then `D(M)_S` acts on `Bl_Y^D X` (`blAction`), `(Bl_Y^D X)^N → S` is smooth, and
`(Bl_Y^D X)^N = Bl_{Y^N}^{D^N} X^N` canonically over `X^N`. The attractors are assumed representable by
schemes. -/
theorem cor13_3 {M : Type u} [AddCommGroup M] {B ZX ZY ZB : Over S} {b : B ⟶ X}
    {act : AAction (overO S) M (yoneda.obj X)} {actY : AAction (overO S) M (yoneda.obj Y)}
    (hC : IsEffCartier I) [IsClosedImmersion j.left] [Mono j]
    {l : Y.left ⟶ I.subscheme} (hl : l ≫ I.subschemeι = Y.hom) [Smooth l] [Smooth X.hom]
    (hs : Stable j act actY) (hD : IsDilatation I j b)
    {N : AddSubmonoid M} (rX : RepresentsAttractor act N (yoneda.obj ZX))
    (rY : RepresentsAttractor actY N (yoneda.obj ZY))
    (rB : RepresentsAttractor (blAction hs hD) N (yoneda.obj ZB))
    {B' : Over S} {b' : B' ⟶ ZX} (hB' : IsDilatation I (jN hs rX rY) b') :
    Smooth ZB.hom ∧ IsDilatation I (jN hs rX rY) (bN hs hD rX rB) ∧
      ∃ e : ZB ≅ B', e.hom ≫ b' = bN hs hD rX rB := by
  haveI : Smooth B.hom := smooth_of_isDilatation hC hl hD
  exact cor13_3_of_smooth hs hD rX rY rB hB'

end AlgMag.Dil

/-! ### Example (iv) of §15: the pure magnets of `ℙ¹` -/

open CategoryTheory Opposite

namespace AlgMag

section P1Pure

variable (R : Type) [CommRing R]

/-- The projector relations. -/
structure Proj2 {D : Type} [CommRing D] (a b c d : D) : Prop where
  h1 : a * a + b * c = a
  h2 : a * b + b * d = b
  h3 : c * a + d * c = c
  h4 : c * b + d * d = d
  h5 : a + d = 1

lemma Proj2.fix {D : Type} [CommRing D] {a b c d : D} (P : Proj2 a b c d) {z : D × D}
    (hz : z ∈ Submodule.span D {((a, c) : D × D), (b, d)}) :
    a * z.1 + b * z.2 = z.1 ∧ c * z.1 + d * z.2 = z.2 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
  have := P.h1; have := P.h2; have := P.h3; have := P.h4
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  constructor
  · linear_combination s * P.h1 + t * P.h2
  · linear_combination s * P.h3 + t * P.h4

lemma coeff_mul_singleZ {D : Type} [CommRing D] (f : AddMonoidAlgebra D ℤ) (k n : ℤ) (r : D) :
    (f * AddMonoidAlgebra.single k r).coeff n = f.coeff (n - k) * r := by
  rw [AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

lemma mapSub_single {D : Type} [CommRing D] (N : AddSubmonoid ℤ) (n : N) (r : D) :
    AddMonoidAlgebra.mapDomainAlgHom D D N.subtype (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single (n : ℤ) r := by
  simp

lemma singleZ_uv {D : Type} [CommRing D] :
    (AddMonoidAlgebra.single (1 : ℤ) (1 : D) * AddMonoidAlgebra.single (-1) 1 :
      AddMonoidAlgebra D ℤ) = 1 := by
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  simp

lemma coeff_mapSub {D : Type} [CommRing D] (N : AddSubmonoid ℤ) (f : AddMonoidAlgebra D N) {n : ℤ}
    (hn : n ∉ N) : (AddMonoidAlgebra.mapDomainAlgHom D D N.subtype f).coeff n = 0 := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy, add_zero]
  | single m r =>
    rw [mapSub_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
    intro e
    exact hn (e ▸ m.2)

/-- The eight fixed-point equations, over an abstract ring. -/
theorem eight_eqs {E : Type} [CommRing E] {A B C F ua ub a b c d vc : E} (hQ : Proj2 A B C F)
    (r1 : a * ua + ub * c = ua) (r2 : a * ub + ub * d = ub)
    (r3 : vc * ua + d * c = c) (r4 : vc * ub + d * d = d)
    (hK : Submodule.span E {((A, C) : E × E), (B, F)} = Submodule.span E {((ua, c) : E × E), (ub, d)}) :
    (A * ua + B * c = ua ∧ C * ua + F * c = c ∧ A * ub + B * d = ub ∧ C * ub + F * d = d) ∧
    (A * a + C * ub = A ∧ B * a + F * ub = B ∧ A * vc + C * d = C ∧ B * vc + F * d = F) := by
  have m1 : ((ua, c) : E × E) ∈ Submodule.span E {((A, C) : E × E), (B, F)} := by
    rw [hK]; exact Submodule.subset_span (by simp)
  have m2 : ((ub, d) : E × E) ∈ Submodule.span E {((A, C) : E × E), (B, F)} := by
    rw [hK]; exact Submodule.subset_span (by simp)
  have m3 : ((A, C) : E × E) ∈ Submodule.span E {((ua, c) : E × E), (ub, d)} := by
    rw [← hK]; exact Submodule.subset_span (by simp)
  have m4 : ((B, F) : E × E) ∈ Submodule.span E {((ua, c) : E × E), (ub, d)} := by
    rw [← hK]; exact Submodule.subset_span (by simp)
  have f1 := hQ.fix m1
  have f2 := hQ.fix m2
  obtain ⟨s1, t1, h1⟩ := Submodule.mem_span_pair.mp m3
  obtain ⟨s2, t2, h2⟩ := Submodule.mem_span_pair.mp m4
  have a1 : s1 * ua + t1 * ub = A := by simpa using congrArg Prod.fst h1
  have a2 : s1 * c + t1 * d = C := by simpa using congrArg Prod.snd h1
  have b1 : s2 * ua + t2 * ub = B := by simpa using congrArg Prod.fst h2
  have b2 : s2 * c + t2 * d = F := by simpa using congrArg Prod.snd h2
  refine ⟨⟨f1.1, f1.2, f2.1, f2.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [← a1, ← a2]; linear_combination s1 * r1 + t1 * r2
  · rw [← b1, ← b2]; linear_combination s2 * r1 + t2 * r2
  · rw [← a1, ← a2]; linear_combination s1 * r3 + t1 * r4
  · rw [← b1, ← b2]; linear_combination s2 * r3 + t2 * r4

/-- What the coefficient computation yields. -/
def ProjOut {D : Type} [CommRing D] (N : AddSubmonoid ℤ) (a b c d : D) : Prop :=
  ∃ a' b' c' d' : D, Proj2 a' b' c' d' ∧ ((1 : ℤ) ∉ N → b' = 0) ∧ ((-1 : ℤ) ∉ N → c' = 0) ∧
    a' * a + b' * c = a ∧ a' * b + b' * d = b ∧ c' * a + d' * c = c ∧ c' * b + d' * d = d ∧
    a * a' + b * c' = a' ∧ a * b' + b * d' = b' ∧ c * a' + d * c' = c' ∧ c * b' + d * d' = d'

/-- Pure algebra of Example (iv): extracting the coefficients of the projector over `D[N]`. -/
theorem coeff_core {D : Type} [CommRing D] {N : AddSubmonoid ℤ}
    {a b c d : D} (hP : Proj2 a b c d) {A B C F : AddMonoidAlgebra D ℤ} (hQ : Proj2 A B C F)
    (hA : ∀ n, n ∉ N → A.coeff n = 0) (hB : ∀ n, n ∉ N → B.coeff n = 0)
    (hC : ∀ n, n ∉ N → C.coeff n = 0)
    (hK : Submodule.span (AddMonoidAlgebra D ℤ) {((A, C) : AddMonoidAlgebra D ℤ × AddMonoidAlgebra D ℤ), (B, F)} =
      Submodule.span (AddMonoidAlgebra D ℤ)
        {((AddMonoidAlgebra.single 1 a, AddMonoidAlgebra.single 0 c) :
            AddMonoidAlgebra D ℤ × AddMonoidAlgebra D ℤ),
          (AddMonoidAlgebra.single 1 b, AddMonoidAlgebra.single 0 d)}) :
    ProjOut N a b c d := by
  classical
  have sm : ∀ (k l m : ℤ) (x y : D), k + l = m →
      (AddMonoidAlgebra.single k x * AddMonoidAlgebra.single l y : AddMonoidAlgebra D ℤ) =
        AddMonoidAlgebra.single m (x * y) := by
    intro k l m x y h
    rw [AddMonoidAlgebra.single_mul_single, h]
  have sa : ∀ (m : ℤ) (x y z : D), x + y = z →
      (AddMonoidAlgebra.single m x + AddMonoidAlgebra.single m y : AddMonoidAlgebra D ℤ) =
        AddMonoidAlgebra.single m z := by
    intro m x y z h
    rw [← AddMonoidAlgebra.single_add, h]
  obtain ⟨⟨E1, E2, E3, E4⟩, E5, E6, E7, E8⟩ := eight_eqs (a := AddMonoidAlgebra.single 0 a)
    (b := AddMonoidAlgebra.single 0 b) (vc := AddMonoidAlgebra.single (-1) c) hQ
    (by rw [sm 0 1 1 _ _ (by norm_num), sm 1 0 1 _ _ (by norm_num)]; exact sa _ _ _ _ hP.h1)
    (by rw [sm 0 1 1 _ _ (by norm_num), sm 1 0 1 _ _ (by norm_num)]; exact sa _ _ _ _ hP.h2)
    (by rw [sm (-1) 1 0 _ _ (by norm_num), sm 0 0 0 _ _ (by norm_num)]; exact sa _ _ _ _ hP.h3)
    (by rw [sm (-1) 1 0 _ _ (by norm_num), sm 0 0 0 _ _ (by norm_num)]; exact sa _ _ _ _ hP.h4)
    hK
  have cf : ∀ {X Y Z : AddMonoidAlgebra D ℤ} (_ : X + Y = Z) (n : ℤ), X.coeff n + Y.coeff n = Z.coeff n := by
    rintro X Y Z rfl n
    rw [AddMonoidAlgebra.coeff_add]; rfl
  have mc : ∀ (f : AddMonoidAlgebra D ℤ) (k n m : ℤ) (r : D), n - k = m →
      (f * AddMonoidAlgebra.single k r).coeff n = f.coeff m * r := by
    intro f k n m r h
    rw [coeff_mul_singleZ, h]
  have s1 : ∀ (m : ℤ) (r : D), (AddMonoidAlgebra.single m r : AddMonoidAlgebra D ℤ).coeff m = r := by
    intro m r
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  let a' := A.coeff 0
  let b' := B.coeff 1
  let c' := C.coeff (-1)
  let d' := F.coeff 0
  have e1 : a' * a + b' * c = a := by
    have := cf E1 1
    rwa [mc _ 1 1 0 _ (by norm_num), mc _ 0 1 1 _ (by norm_num), s1] at this
  have e2 : c' * a + d' * c = c := by
    have := cf E2 0
    rwa [mc _ 1 0 (-1) _ (by norm_num), mc _ 0 0 0 _ (by norm_num), s1] at this
  have e3 : a' * b + b' * d = b := by
    have := cf E3 1
    rwa [mc _ 1 1 0 _ (by norm_num), mc _ 0 1 1 _ (by norm_num), s1] at this
  have e4 : c' * b + d' * d = d := by
    have := cf E4 0
    rwa [mc _ 1 0 (-1) _ (by norm_num), mc _ 0 0 0 _ (by norm_num), s1] at this
  have e5 : a * a' + b * c' = a' := by
    have := cf E5 0
    rw [mc _ 0 0 0 _ (by norm_num), mc _ 1 0 (-1) _ (by norm_num)] at this
    change a' * a + c' * b = a' at this
    linear_combination this
  have e6 : a * b' + b * d' = b' := by
    have := cf E6 1
    rw [mc _ 0 1 1 _ (by norm_num), mc _ 1 1 0 _ (by norm_num)] at this
    change b' * a + d' * b = b' at this
    linear_combination this
  have e7 : c * a' + d * c' = c' := by
    have := cf E7 (-1)
    rw [mc _ (-1) (-1) 0 _ (by norm_num), mc _ 0 (-1) (-1) _ (by norm_num)] at this
    change a' * c + c' * d = c' at this
    linear_combination this
  have e8 : c * b' + d * d' = d' := by
    have := cf E8 0
    rw [mc _ (-1) 0 1 _ (by norm_num), mc _ 0 0 0 _ (by norm_num)] at this
    change b' * c + d' * d = d' at this
    linear_combination this
  have tr : a' + d' = 1 := by
    have := cf hQ.h5 0
    rw [AddMonoidAlgebra.one_def, s1] at this
    exact this
  refine ⟨a', b', c', d', ⟨?_, ?_, ?_, ?_, tr⟩, fun h => hB 1 h, fun h => hC (-1) h,
    e1, e3, e2, e4, e5, e6, e7, e8⟩
  · linear_combination (-a') * e5 - b' * e7 + a' * e1 + c' * e3 + e5
  · linear_combination (-a') * e6 - b' * e8 + b' * e1 + d' * e3 + e6
  · linear_combination (-c') * e5 - d' * e7 + a' * e2 + c' * e4 + e7
  · linear_combination (-c') * e6 - d' * e8 + b' * e2 + d' * e4 + e8

/-- **The key step of Example (iv).** -/
theorem exists_proj_of_attractor {D : CommAlgCat.{0} R} {N : AddSubmonoid ℤ}
    (φ : AttractorPt (p1Action R) N (op D)) {a b c d : D} (hP : Proj2 a b c d)
    (hK : (φ.toPoint).1 = Submodule.span D {((a, c) : D × D), (b, d)}) :
    ProjOut N a b c d := by
  classical
  let DD : Type := D
  let EN := AddMonoidAlgebra DD N
  let EZ := AddMonoidAlgebra DD ℤ
  let tN : op (CommAlgCat.of R EN) ⟶ op D := affHom (constAlg (R := R) N DD)
  let aN : APt (affO R) N (op (op (CommAlgCat.of R EN))) := AddMonoidAlgebra.of DD N
  obtain ⟨A, B, C, F, q1, q2, q3, q4, q5, q6⟩ := (φ.app tN aN).2
  let τ₀ := AddMonoidAlgebra.mapDomainAlgHom DD DD N.subtype
  let τ : EN →ₐ[R] EZ := τ₀.restrictScalars R
  let tτ : op (CommAlgCat.of R EZ) ⟶ op (CommAlgCat.of R EN) := affHom τ
  let ι : DD →ₐ[R] EZ := constAlg (R := R) ℤ DD
  let tZ : op (CommAlgCat.of R EZ) ⟶ op D := affHom ι
  have htt : tτ ≫ tN = tZ := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun x => ?_))
    exact mapSub_single N 0 x
  let u : EZ := AddMonoidAlgebra.single 1 1
  let hU : APt (affO R) ℤ (op (op (CommAlgCat.of R EZ))) := AddMonoidAlgebra.of DD ℤ
  have e1 : φ.app tZ (APt.res tτ.op aN) = (p1 R).map tτ.op (φ.app tN aN) := by
    rw [← htt]
    exact φ.naturality tτ tN aN
  have e2 : APt.res tτ.op aN = APt.toMagnet N hU * 1 := by
    refine MonoidHom.ext fun n => ?_
    exact (mapSub_single N (Multiplicative.toAdd n) (1 : DD)).trans (mul_one _).symm
  have e3 := φ.equivariant tZ hU 1
  have e4 : φ.app tZ 1 = (p1 R).map tZ.op φ.toPoint := by
    have := φ.naturality tZ (𝟙 _) 1
    rw [Category.comp_id, show APt.res tZ.op (1 : APt (affO R) N (op (op D))) = 1 from by ext p; simp] at this
    exact this
  have e5 : (((p1 R).map tτ.op (φ.app tN aN)).1 : Submodule EZ (EZ × EZ)) =
      Submodule.map (diag2 u) (((p1 R).map tZ.op φ.toPoint).1) := by
    rw [← e1, e2, e3, e4]
    rfl
  have l1 : (((p1 R).map tτ.op (φ.app tN aN)).1 : Submodule EZ (EZ × EZ)) =
      Submodule.span EZ {((τ A, τ C) : EZ × EZ), (τ B, τ F)} := by
    change bc τ.toRingHom (φ.app tN aN).1 = _
    rw [q6]
    exact bc_span_pair τ.toRingHom _ _
  have l2 : ((p1 R).map tZ.op φ.toPoint).1 =
      Submodule.span EZ {((ι a, ι c) : EZ × EZ), (ι b, ι d)} := by
    change bc ι.toRingHom φ.toPoint.1 = _
    rw [hK]
    exact bc_span_pair ι.toRingHom _ _
  have sm1 : ∀ x : DD, u * ι x = AddMonoidAlgebra.single 1 x := by
    intro x
    change AddMonoidAlgebra.single (1 : ℤ) (1 : DD) * AddMonoidAlgebra.single 0 x = _
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_zero]
  rw [l1, l2, map_diag2_span, diag2_apply, diag2_apply] at e5
  simp only [sm1] at e5
  have mapP : Proj2 (τ A) (τ B) (τ C) (τ F) :=
    ⟨by rw [← map_mul, ← map_mul, ← map_add]; exact congrArg τ q1,
     by rw [← map_mul, ← map_mul, ← map_add]; exact congrArg τ q2,
     by rw [← map_mul, ← map_mul, ← map_add]; exact congrArg τ q3,
     by rw [← map_mul, ← map_mul, ← map_add]; exact congrArg τ q4,
     by rw [← map_add]; exact (congrArg τ q5).trans (map_one τ)⟩
  exact coeff_core (D := DD) hP mapP (fun n hn => coeff_mapSub N A hn) (fun n hn => coeff_mapSub N B hn)
    (fun n hn => coeff_mapSub N C hn) e5

open Classical in
/-- The coordinate `a(e)` of `a ∈ 𝔸(N)`, zero if `e ∉ N`. -/
noncomputable def xv (N : AddSubmonoid ℤ) (e : ℤ) {T' : Aff R} (a : APt (affO R) N (op T')) :
    (unop T' : CommAlgCat.{0} R) :=
  if h : e ∈ N then (show (unop T' : CommAlgCat.{0} R) from a (Multiplicative.ofAdd (⟨e, h⟩ : N))) else 0

lemma xv_res (N : AddSubmonoid ℤ) (e : ℤ) {T' T'' : Aff R} (s : T'' ⟶ T') (a : APt (affO R) N (op T')) :
    xv R N e (APt.res s.op a) = s.unop.hom (xv R N e a) := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (map_zero _).symm

lemma xv_one (N : AddSubmonoid ℤ) (e : ℤ) (h : e ∈ N) {T' : Aff R} :
    xv R N e (1 : APt (affO R) N (op T')) = 1 := by
  unfold xv
  rw [dif_pos h]
  rfl

lemma xv_mul (N : AddSubmonoid ℤ) (e : ℤ) {T' : Aff R} (g : APt (affO R) ℤ (op T')) (a : APt (affO R) N (op T')) :
    xv R N e (APt.toMagnet N g * a) =
      (show (unop T' : CommAlgCat.{0} R) from g (Multiplicative.ofAdd e)) * xv R N e a := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (mul_zero _).symm

lemma map_diag2_line {D : Type} [CommRing D] {u v : D} (huv : u * v = 1) (p q r s : D) :
    Submodule.map (diag2 u) (Submodule.span D {((p, r) : D × D), (q, s)}) =
      Submodule.span D {((p, v * r) : D × D), (u * q, s)} := by
  rw [map_diag2_span, diag2_apply, diag2_apply]
  have e1 : ((u * p, r) : D × D) = u • (p, v * r) := by
    ext
    · rfl
    · change r = u * (v * r)
      rw [← mul_assoc, huv, one_mul]
  have e2 : ((p, v * r) : D × D) = v • (u * p, r) := by
    ext
    · change p = v * (u * p)
      rw [← mul_assoc, mul_comm v u, huv, one_mul]
    · rfl
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · change (u * p, r) ∈ _
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

/-- The line of `[[A, B x], [C y, F]]`, an attractor point when `B C = 0`. -/
noncomputable def p1Lift {D : CommAlgCat.{0} R} (N : AddSubmonoid ℤ) {A B C F : D} (hP : Proj2 A B C F)
    (hBC : B * C = 0) : AttractorPt (p1Action R) N (op D) where
  app {T'} t a := ⟨Submodule.span T'.unop
      {((t.unop.hom A, t.unop.hom C * xv R N (-1) a) : T'.unop × T'.unop),
        (t.unop.hom B * xv R N 1 a, t.unop.hom F)}, by
    let φ := t.unop.hom
    have h0 : φ B * φ C = 0 := by rw [← map_mul, hBC, map_zero]
    have h1 : φ A * φ A + φ B * φ C = φ A := by rw [← map_mul, ← map_mul, ← map_add, hP.h1]
    have h2 : φ A * φ B + φ B * φ F = φ B := by rw [← map_mul, ← map_mul, ← map_add, hP.h2]
    have h3 : φ C * φ A + φ F * φ C = φ C := by rw [← map_mul, ← map_mul, ← map_add, hP.h3]
    have h4 : φ C * φ B + φ F * φ F = φ F := by rw [← map_mul, ← map_mul, ← map_add, hP.h4]
    have h5 : φ A + φ F = 1 := by rw [← map_add, hP.h5, map_one]
    refine ⟨φ A, φ B * xv R N 1 a, φ C * xv R N (-1) a, φ F, ?_, ?_, ?_, ?_, h5, rfl⟩
    · linear_combination h1 + (xv R N 1 a * xv R N (-1) a - 1) * h0
    · linear_combination xv R N 1 a * h2
    · linear_combination xv R N (-1) a * h3
    · linear_combination h4 + (xv R N 1 a * xv R N (-1) a - 1) * h0⟩
  naturality {T' T''} s t a := by
    refine Subtype.ext ?_
    refine Eq.trans ?_ (bc_span_pair (s.unop.hom : _ →ₐ[R] _).toRingHom _ _).symm
    simp only [xv_res, Prod.map]
    congr 3 <;> simp <;> rfl
  equivariant {T'} t g a := by
    refine Subtype.ext ?_
    have huv : (show T'.unop from g (Multiplicative.ofAdd (1 : ℤ))) *
        (show T'.unop from g (Multiplicative.ofAdd (-1 : ℤ))) = 1 :=
      (map_mul g (Multiplicative.ofAdd (1 : ℤ)) (Multiplicative.ofAdd (-1 : ℤ))).symm.trans (map_one g)
    refine Eq.trans ?_ (map_diag2_line huv _ _ _ _).symm
    simp only [xv_mul]
    have lc : ∀ p q r : T'.unop, p * (q * r) = q * (p * r) := mul_left_comm
    congr 3 <;> first | rfl | exact lc _ _ _ | (refine Prod.ext ?_ ?_ <;> first | rfl | exact lc _ _ _)

lemma p1Lift_toPoint {D : CommAlgCat.{0} R} (N : AddSubmonoid ℤ) {A B C F : D} (hP : Proj2 A B C F)
    (hBC : B * C = 0) (hB : (1 : ℤ) ∉ N → B = 0) (hC : (-1 : ℤ) ∉ N → C = 0) :
    ((p1Lift R N hP hBC).toPoint).1 = Submodule.span D {((A, C) : D × D), (B, F)} := by
  have e1 : C * xv R N (-1) (1 : APt (affO R) N (op (op D))) = C := by
    by_cases h : (-1 : ℤ) ∈ N
    · rw [xv_one R N _ h, mul_one]
    · rw [hC h, zero_mul]
  have e2 : B * xv R N 1 (1 : APt (affO R) N (op (op D))) = B := by
    by_cases h : (1 : ℤ) ∈ N
    · rw [xv_one R N _ h, mul_one]
    · rw [hB h, zero_mul]
  have e : ((p1Lift R N hP hBC).toPoint).1 = Submodule.span D {((A, C * xv R N (-1) (1 : APt (affO R) N (op (op D)))) : D × D),
      (B * xv R N 1 (1 : APt (affO R) N (op (op D))), F)} := rfl
  rw [e, e1, e2]

lemma span_swap {D : Type} [CommRing D] {a b c d a' b' c' d' : D}
    (e1 : a' * a + b' * c = a) (e2 : a' * b + b' * d = b) (e3 : c' * a + d' * c = c)
    (e4 : c' * b + d' * d = d) (e5 : a * a' + b * c' = a') (e6 : a * b' + b * d' = b')
    (e7 : c * a' + d * c' = c') (e8 : c * b' + d * d' = d') :
    Submodule.span D {((a', c') : D × D), (b', d')} = Submodule.span D {((a, c) : D × D), (b, d)} := by
  have key : ∀ {p q r s x y : D}, x * p + y * q = r → x * s + y * (0 : D) = x * s → True :=
    fun _ _ => trivial
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · refine Submodule.mem_span_pair.mpr ⟨a', c', Prod.ext ?_ ?_⟩
      · change a' * a + c' * b = a'; linear_combination e5
      · change a' * c + c' * d = c'; linear_combination e7
    · refine Submodule.mem_span_pair.mpr ⟨b', d', Prod.ext ?_ ?_⟩
      · change b' * a + d' * b = b'; linear_combination e6
      · change b' * c + d' * d = d'; linear_combination e8
  · refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · refine Submodule.mem_span_pair.mpr ⟨a, c, Prod.ext ?_ ?_⟩
      · change a * a' + c * b' = a; linear_combination e1
      · change a * c' + c * d' = c; linear_combination e3
    · refine Submodule.mem_span_pair.mpr ⟨b, d, Prod.ext ?_ ?_⟩
      · change b * a' + d * b' = b; linear_combination e2
      · change b * c' + d * d' = d; linear_combination e4

/-- The reduction: `X^N` and `X^{N'}` have the same points, `N'` generated by `N ∩ {1, -1}`. -/
theorem image_eq_closure (N : AddSubmonoid ℤ) :
    attractorImage (p1Action R) N =
      attractorImage (p1Action R) (AddSubmonoid.closure ((N : Set ℤ) ∩ {1, -1})) := by
  set N' := AddSubmonoid.closure ((N : Set ℤ) ∩ {1, -1}) with hN'
  have hle : N' ≤ N := (AddSubmonoid.closure_le).2 Set.inter_subset_left
  funext T
  apply Set.Subset.antisymm
  · rintro _ ⟨φ, rfl⟩
    by_cases hb : (1 : ℤ) ∈ N ∧ (-1 : ℤ) ∈ N
    · have h1 : (1 : ℤ) ∈ N' := AddSubmonoid.subset_closure ⟨hb.1, by simp⟩
      have h2 : (-1 : ℤ) ∈ N' := AddSubmonoid.subset_closure ⟨hb.2, by simp⟩
      have htop : N ≤ N' := by
        intro n hn
        clear hn
        induction n using Int.induction_on with
        | zero => exact N'.zero_mem
        | succ i hi => exact N'.add_mem hi h1
        | pred i hi => exact N'.add_mem hi h2
      exact ⟨AttractorPt.ofLE htop φ, rfl⟩
    · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5, q6⟩ := (φ.toPoint).2
      obtain ⟨a', b', c', d', P', hb', hc', e1, e2, e3, e4, e5, e6, e7, e8⟩ :=
        exists_proj_of_attractor R (D := unop T) (φ := φ) (hP := ⟨q1, q2, q3, q4, q5⟩) q6
      have hBC : b' * c' = 0 := by
        by_cases h : (1 : ℤ) ∈ N
        · rw [hc' fun h' => hb ⟨h, h'⟩, mul_zero]
        · rw [hb' h, zero_mul]
      have n1 : (1 : ℤ) ∉ N' → b' = 0 := fun h => hb' fun h' =>
        h (AddSubmonoid.subset_closure ⟨h', by simp⟩)
      have n2 : (-1 : ℤ) ∉ N' → c' = 0 := fun h => hc' fun h' =>
        h (AddSubmonoid.subset_closure ⟨h', by simp⟩)
      refine ⟨p1Lift R N' P' hBC, Subtype.ext ?_⟩
      exact (p1Lift_toPoint R N' P' hBC n1 n2).trans
        ((span_swap e1 e2 e3 e4 e5 e6 e7 e8).trans q6.symm)
  · rintro _ ⟨φ, rfl⟩
    exact ⟨AttractorPt.ofLE hle φ, rfl⟩

lemma proj_lineA {D : Type} [CommRing D] (b : D) : Proj2 (0 : D) b 0 1 :=
  ⟨by ring, by ring, by ring, by ring, by ring⟩

lemma proj_lineB {D : Type} [CommRing D] (c : D) : Proj2 (1 : D) 0 c 0 :=
  ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- The dual numbers, as a test object. -/
noncomputable abbrev dualAlg : CommAlgCat.{0} R := CommAlgCat.of R (DualNumber R)

lemma eps_ne [Nontrivial R] : (DualNumber.eps : DualNumber R) ≠ 0 := fun h =>
  (one_ne_zero (α := R)) (by simpa using congrArg TrivSqZeroExt.snd h)

/-- If `[ε : 1]` lifts to `X^L` then `1 ∈ L`. -/
lemma one_mem_of_lift [Nontrivial R] {L : AddSubmonoid ℤ} (φ : AttractorPt (p1Action R) L (op (dualAlg R)))
    (h : (φ.toPoint).1 = Submodule.span (DualNumber R) {(((0 : DualNumber R), (0 : DualNumber R))), (DualNumber.eps, 1)}) :
    (1 : ℤ) ∈ L := by
  by_contra hL
  obtain ⟨a', b', c', d', -, hb', -, -, e2, -, -, e5, -, -, -⟩ :=
    exists_proj_of_attractor R (D := dualAlg R) (φ := φ) (hP := proj_lineA (D := DualNumber R) DualNumber.eps) h
  have hb0 : (b' : DualNumber R) = 0 := hb' hL
  have e2' : (a' : DualNumber R) * DualNumber.eps = DualNumber.eps := by
    have e2'' : (a' : DualNumber R) * DualNumber.eps + b' * 1 = DualNumber.eps := e2
    rw [hb0] at e2''; simpa using e2''
  have e5' : (DualNumber.eps : DualNumber R) * c' = a' := by
    have e5'' : (0 : DualNumber R) * a' + DualNumber.eps * c' = a' := e5
    simpa using e5''
  apply eps_ne R
  rw [← e2', ← e5', mul_right_comm, DualNumber.eps_mul_eps, zero_mul]

/-- If `[1 : ε]` lifts to `X^L` then `-1 ∈ L`. -/
lemma neg_one_mem_of_lift [Nontrivial R] {L : AddSubmonoid ℤ} (φ : AttractorPt (p1Action R) L (op (dualAlg R)))
    (h : (φ.toPoint).1 = Submodule.span (DualNumber R) {(((1 : DualNumber R), (DualNumber.eps : DualNumber R))), (0, 0)}) :
    (-1 : ℤ) ∈ L := by
  by_contra hL
  obtain ⟨a', b', c', d', -, -, hc', -, -, e3, -, -, -, -, e8⟩ :=
    exists_proj_of_attractor R (D := dualAlg R) (φ := φ) (hP := proj_lineB (D := DualNumber R) DualNumber.eps) h
  have hc0 : (c' : DualNumber R) = 0 := hc' hL
  have e3' : (d' : DualNumber R) * DualNumber.eps = DualNumber.eps := by
    have e3'' : (c' : DualNumber R) * 1 + d' * DualNumber.eps = DualNumber.eps := e3
    rw [hc0] at e3''; simpa using e3''
  have e8' : (DualNumber.eps : DualNumber R) * b' = d' := by
    have e8'' : (DualNumber.eps : DualNumber R) * b' + 0 * d' = d' := e8
    simpa using e8''
  apply eps_ne R
  rw [← e3', ← e8', mul_right_comm, DualNumber.eps_mul_eps, zero_mul]

lemma closure_one : AddSubmonoid.closure ({1} : Set ℤ) = posN := by
  apply le_antisymm
  · exact (AddSubmonoid.closure_le).2 (by simp [mem_posN])
  · intro n hn
    have hn' : 0 ≤ n := hn
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn'
    have := (AddSubmonoid.closure ({1} : Set ℤ)).nsmul_mem (AddSubmonoid.subset_closure (Set.mem_singleton (1 : ℤ))) k
    simpa using this

lemma closure_neg_one : AddSubmonoid.closure ({-1} : Set ℤ) = negN := by
  apply le_antisymm
  · exact (AddSubmonoid.closure_le).2 (by simp [mem_negN])
  · intro n hn
    have hn' : 0 ≤ -n := by have : n ≤ 0 := hn; omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn'
    have := (AddSubmonoid.closure ({-1} : Set ℤ)).nsmul_mem (AddSubmonoid.subset_closure (Set.mem_singleton (-1 : ℤ))) k
    have e : n = k • (-1 : ℤ) := by simp; omega
    rw [e]; exact this

lemma closure_both : AddSubmonoid.closure ({1, -1} : Set ℤ) = ⊤ := by
  refine top_le_iff.1 fun n hn => ?_
  clear hn
  induction n using Int.induction_on with
  | zero => exact AddSubmonoid.zero_mem _
  | succ i hi => exact AddSubmonoid.add_mem _ hi (AddSubmonoid.subset_closure (by simp))
  | pred i hi => exact AddSubmonoid.add_mem _ hi (AddSubmonoid.subset_closure (by simp))

/-- **§15, Example (iv).** For the action of `D(ℤ)` on `ℙ¹` over a nonzero ring,
`Π(a) = {0, ℕ, -ℕ, ℤ}`. -/
theorem pureMagnets_p1 [Nontrivial R] :
    pureMagnets (attractorImage (p1Action R)) = {⊥, posN, negN, ⊤} := by
  have wA : ∀ L : AddSubmonoid ℤ, (1 : ℤ) ∈ L → ∃ φ : AttractorPt (p1Action R) L (op (dualAlg R)),
      (φ.toPoint).1 = Submodule.span (DualNumber R) {(((0 : DualNumber R), (0 : DualNumber R))), (DualNumber.eps, 1)} := by
    intro L h
    have hB : (DualNumber.eps : DualNumber R) * 0 = 0 := mul_zero _
    exact ⟨p1Lift R (D := dualAlg R) L (proj_lineA (D := DualNumber R) DualNumber.eps) hB,
      p1Lift_toPoint R L _ hB (fun h' => absurd h h') (fun _ => rfl)⟩
  have wB : ∀ L : AddSubmonoid ℤ, (-1 : ℤ) ∈ L → ∃ φ : AttractorPt (p1Action R) L (op (dualAlg R)),
      (φ.toPoint).1 = Submodule.span (DualNumber R) {(((1 : DualNumber R), (DualNumber.eps : DualNumber R))), (0, 0)} := by
    intro L h
    have hB : (0 : DualNumber R) * DualNumber.eps = 0 := zero_mul _
    exact ⟨p1Lift R (D := dualAlg R) L (proj_lineB (D := DualNumber R) DualNumber.eps) hB,
      p1Lift_toPoint R L _ hB (fun _ => rfl) (fun h' => absurd h h')⟩
  have dA : ∀ N L : AddSubmonoid ℤ, attractorImage (p1Action R) N = attractorImage (p1Action R) L →
      (1 : ℤ) ∈ N → (1 : ℤ) ∈ L := by
    intro N L e h
    obtain ⟨φ, hφ⟩ := wA N h
    have : φ.toPoint ∈ attractorImage (p1Action R) L (op (dualAlg R)) := by
      rw [← e]; exact ⟨φ, rfl⟩
    obtain ⟨ψ, hψ⟩ := this
    exact one_mem_of_lift R ψ ((congrArg Subtype.val hψ).trans hφ)
  have dB : ∀ N L : AddSubmonoid ℤ, attractorImage (p1Action R) N = attractorImage (p1Action R) L →
      (-1 : ℤ) ∈ N → (-1 : ℤ) ∈ L := by
    intro N L e h
    obtain ⟨φ, hφ⟩ := wB N h
    have : φ.toPoint ∈ attractorImage (p1Action R) L (op (dualAlg R)) := by
      rw [← e]; exact ⟨φ, rfl⟩
    obtain ⟨ψ, hψ⟩ := this
    exact neg_one_mem_of_lift R ψ ((congrArg Subtype.val hψ).trans hφ)
  ext N
  constructor
  · intro hN
    have hc : N = AddSubmonoid.closure ((N : Set ℤ) ∩ {1, -1}) :=
      IsPure.eq_closure_inter (fun N => image_eq_closure R N) hN
    by_cases h1 : (1 : ℤ) ∈ N <;> by_cases h2 : (-1 : ℤ) ∈ N
    · have : (N : Set ℤ) ∩ {1, -1} = {1, -1} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨h1, Or.inl rfl⟩
          · exact ⟨h2, Or.inr rfl⟩
      rw [this, closure_both] at hc
      simp [hc]
    · have : (N : Set ℤ) ∩ {1, -1} = {1} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, rfl | rfl⟩
          · rfl
          · exact absurd hx h2
        · rintro rfl; exact ⟨h1, Or.inl rfl⟩
      rw [this, closure_one] at hc
      simp [hc]
    · have : (N : Set ℤ) ∩ {1, -1} = {-1} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, rfl | rfl⟩
          · exact absurd hx h1
          · rfl
        · rintro rfl; exact ⟨h2, Or.inr rfl⟩
      rw [this, closure_neg_one] at hc
      simp [hc]
    · have : (N : Set ℤ) ∩ {1, -1} = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hx, rfl | rfl⟩
        · exact h1 hx
        · exact h2 hx
      rw [this, AddSubmonoid.closure_empty] at hc
      simp [hc]
  · rintro (rfl | rfl | rfl | rfl) L e
    · exact bot_le
    · have h := dA _ L e (by simp [mem_posN])
      rw [← closure_one]
      exact (AddSubmonoid.closure_le).2 (by simpa using h)
    · have h := dB _ L e (by simp [mem_negN])
      rw [← closure_neg_one]
      exact (AddSubmonoid.closure_le).2 (by simpa using h)
    · have h1 := dA _ L e (AddSubmonoid.mem_top _)
      have h2 := dB _ L e (AddSubmonoid.mem_top _)
      rw [← closure_both]
      refine (AddSubmonoid.closure_le).2 ?_
      rintro _ (rfl | rfl)
      · exact h1
      · exact h2

end P1Pure

end AlgMag

/-! ### §16.7: the action on the toric scheme -/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AddMonoidAlgebra


namespace AlgMag.Mono

noncomputable section

section Generic

variable {C : Type*} [Category.{u} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}} {M : Type*} [AddCommMonoid M]
  {N : AddSubmonoid M} {E : C} (U : UniversalPoint 𝒪 N E) (tb : ∀ T : C, T ⟶ E)
  (hE : ∀ {T : C} (a b : T ⟶ E), a = b)

include tb hE in
lemma univ_ext {T : C} {s s' : T ⟶ U.P} (e : APt.res s.op U.u = APt.res s'.op U.u) : s = s' := by
  have hs : ∀ r : T ⟶ U.P, r = U.lift (tb T) (APt.res r.op U.u) := fun r =>
    U.uniq _ _ _ (hE _ _) rfl
  rw [hs s, hs s', e]

include tb hE in
/-- **Fact 2.12.** The action of `𝔸(M)` on `𝔸(N)_E`: `(h • a)(n) = h(n) a(n)`. -/
def univAct : AAction 𝒪 M (yoneda.obj U.P) where
  smul {T} h t := U.lift (tb (unop T)) (APt.toMagnet N h * APt.res (show unop T ⟶ U.P from t).op U.u)
  one_smul {T} t := by
    refine univ_ext U tb hE ?_
    rw [U.res_lift]
    have : APt.toMagnet N (1 : APt 𝒪 M T) = 1 := rfl
    rw [this, one_mul]
  mul_smul {T} g h t := by
    refine univ_ext U tb hE ?_
    rw [U.res_lift]
    change _ = APt.res (U.lift (tb (unop T)) _).op U.u
    rw [U.res_lift]
    change _ = APt.toMagnet N g * _
    rw [show APt.res _ U.u = _ from U.res_lift (tb (unop T)) (APt.toMagnet N h * APt.res (show unop T ⟶ U.P from t).op U.u)]
    ext n
    simp [mul_assoc]
  map_smul {T T'} f h t := by
    refine univ_ext U tb hE ?_
    change APt.res (f.unop ≫ U.lift (tb (unop T)) _).op U.u = APt.res (U.lift (tb (unop T')) _).op U.u
    rw [U.res_lift, op_comp, APt.res_comp, U.res_lift]
    ext n
    simp [APt.res_mul]

lemma res_univAct {T : C} (h : APt 𝒪 M (op T)) (t : T ⟶ U.P) :
    APt.res (((univAct U tb hE).smul h t : T ⟶ U.P)).op U.u = APt.toMagnet N h * APt.res t.op U.u :=
  U.res_lift _ _

end Generic

section Toric

/-- The base `Spec ℤ`. -/
abbrev SZ : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

variable {B : BigFppfSite.{u}} {hS : B.Contains SZ.{u}}

local notation "SCH" => BigFppfOver.toScheme B SZ hS

variable (hS) in
/-- An object of the site from a scheme below the cutoff: everything lives over `ℤ`. -/
def zObj (W : Scheme.{u}) (h : B.Contains W) : BigFppfOver B SZ hS :=
  siteObject B SZ hS h (specULiftZIsTerminal.from W)

/-- A morphism of the site from one of schemes. -/
def toHom {W W' : BigFppfOver B SZ hS} (f : (SCH).obj W ⟶ (SCH).obj W') : W ⟶ W' :=
  Over.homMk (ObjectProperty.homMk f) (by
    apply B.inclusion.map_injective
    exact specULiftZIsTerminal.hom_ext _ _)

@[simp] lemma map_toHom {W W' : BigFppfOver B SZ hS} (f : (SCH).obj W ⟶ (SCH).obj W') :
    (SCH).map (toHom f) = f := rfl

lemma hom_ext_of_map {W W' : BigFppfOver B SZ hS} {f g : W ⟶ W'} (h : (SCH).map f = (SCH).map g) :
    f = g := (SCH).map_injective h

variable (hS) in
/-- `Spec ℤ` as an object. -/
def eObj : BigFppfOver B SZ hS := zObj hS SZ hS

/-- The morphism to `Spec ℤ`. -/
def tb (T : BigFppfOver B SZ hS) : T ⟶ eObj hS := toHom (specULiftZIsTerminal.from _)

lemma hE {T : BigFppfOver B SZ hS} (a b : T ⟶ eObj hS) : a = b :=
  hom_ext_of_map (specULiftZIsTerminal.hom_ext _ _)

variable {M : Type u} [AddCommGroup M]

/-- The universal point of `Spec ℤ[N]`. -/
def uPt (N : AddSubmonoid M) (h : B.Contains (Spec (ZMon N))) :
    APt (fppfO B SZ hS) N (op (zObj hS (Spec (ZMon N)) h)) :=
  MonAff.toSpecEquiv (𝟙 (Spec (ZMon N)))

lemma res_uPt (N : AddSubmonoid M) (h : B.Contains (Spec (ZMon N))) {T : BigFppfOver B SZ hS}
    (t : T ⟶ zObj hS (Spec (ZMon N)) h) :
    APt.res t.op (uPt N h) = MonAff.toSpecEquiv ((SCH).map t) := by
  ext p
  let r : (SCH).obj T ⟶ Spec (ZMon N) := (SCH).map t
  have := MonAff.toSpecEquiv_comp r (𝟙 (Spec (ZMon N))) p
  rw [Category.comp_id] at this
  exact this.symm

/-- `Spec ℤ[N]` is the universal point of `𝔸(N)`. -/
def cU (N : AddSubmonoid M) (h : B.Contains (Spec (ZMon N))) :
    UniversalPoint (fppfO B SZ hS) N (eObj hS) where
  P := zObj hS (Spec (ZMon N)) h
  π := tb _
  u := uPt N h
  lift {T'} _ a := toHom (MonAff.toSpecEquiv.symm a)
  lift_π _ _ := hE _ _
  res_lift t a := (res_uPt N h _).trans (MonAff.toSpecEquiv.apply_symm_apply a)
  uniq t a s _ hs := hom_ext_of_map ((MonAff.toSpecEquiv.symm_apply_apply _).symm.trans
    (congrArg _ ((res_uPt N h s).symm.trans hs)))

/-- The action of `D(M)` on `Spec ℤ[N]`. -/
def cAct (N : AddSubmonoid M) (h : B.Contains (Spec (ZMon N))) :
    AAction (fppfO B SZ hS) M (yoneda.obj (zObj hS (Spec (ZMon N)) h)) :=
  univAct (cU N h) tb (fun a b => hE a b)

lemma res_cAct (N : AddSubmonoid M) (h : B.Contains (Spec (ZMon N))) {T : BigFppfOver B SZ hS}
    (k : APt (fppfO B SZ hS) M (op T)) (t : T ⟶ zObj hS (Spec (ZMon N)) h) :
    APt.res (((cAct N h).smul k t : T ⟶ _)).op (uPt N h) = APt.toMagnet N k * APt.res t.op (uPt N h) :=
  res_univAct (cU N h) tb (fun a b => hE a b) k t

lemma cAct_ext {N : AddSubmonoid M} {h : B.Contains (Spec (ZMon N))} {T : BigFppfOver B SZ hS}
    {s s' : T ⟶ zObj hS (Spec (ZMon N)) h} (e : APt.res s.op (uPt N h) = APt.res s'.op (uPt N h)) :
    s = s' :=
  univ_ext (cU N h) tb (fun a b => hE a b) e

/-- `Spec ℤ[N'] → Spec ℤ[N]` for `N ≤ N'`. -/
def trH {N N' : AddSubmonoid M} (hl : N ≤ N') (h : B.Contains (Spec (ZMon N)))
    (h' : B.Contains (Spec (ZMon N'))) : zObj hS (Spec (ZMon N')) h' ⟶ zObj hS (Spec (ZMon N)) h :=
  toHom (Spec.map (trans hl))

/-- `Spec ℤ[N'] → Spec ℤ[N]` for `N ≤ N'` is equivariant. -/
lemma smul_trans {N N' : AddSubmonoid M} (hl : N ≤ N') (h : B.Contains (Spec (ZMon N)))
    (h' : B.Contains (Spec (ZMon N'))) {T : BigFppfOver B SZ hS} (k : APt (fppfO B SZ hS) M (op T))
    (d : T ⟶ zObj hS (Spec (ZMon N')) h') :
    ((cAct N' h').smul k d : T ⟶ _) ≫ trH hl h h' =
      ((cAct N h).smul k (d ≫ trH hl h h') : T ⟶ _) := by
  have key : ∀ {T : BigFppfOver B SZ hS} (d : T ⟶ zObj hS (Spec (ZMon N')) h'),
      APt.res (d ≫ trH hl h h').op (uPt N h) =
        APt.restrict hl (APt.res d.op (uPt N' h')) := by
    intro T d
    rw [res_uPt, res_uPt]
    ext p
    let r : (SCH).obj T ⟶ Spec (ZMon N') := (SCH).map d
    change (r ≫ Spec.map (trans hl)).appTop ((Scheme.ΓSpecIso (ZMon N)).inv _) =
      r.appTop ((Scheme.ΓSpecIso (ZMon N')).inv _)
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    have := congrArg (fun q => q.hom (AddMonoidAlgebra.single (Multiplicative.toAdd p) 1))
      (Scheme.ΓSpecIso_inv_naturality (trans hl))
    refine this.symm.trans ?_
    change (Scheme.ΓSpecIso (ZMon N')).inv ((trans hl).hom _) = _
    rw [trans_single]
    rfl
  refine cAct_ext ?_
  rw [key, res_cAct, res_cAct, key]
  rfl

variable (hS) (X : ToricMono M) (hN : ∀ i, B.Contains (Spec (ZMon (X.N i)))) (hV : B.Contains (toricScheme X))

/-- The toric scheme, as an object of the site. -/
def vObj : BigFppfOver B SZ hS := zObj hS (toricScheme X) hV

/-- The chart `A(N_α)`, as an object of the site. -/
def cObj (i : X.J) : BigFppfOver B SZ hS := zObj hS (Spec (ZMon (X.N i))) (hN i)

/-- The action on the chart. -/
def chartAct (i : X.J) : AAction (fppfO B SZ hS) M (yoneda.obj (cObj hS X hN i)) := cAct (X.N i) (hN i)

/-- The inclusion of the chart. -/
def chartJ (i : X.J) : cObj hS X hN i ⟶ vObj hS X hV := toHom (chartι X i)

/-- The transition morphism. -/
def chartTr {k i : X.J} (g : k ⟶ i) : cObj hS X hN k ⟶ cObj hS X hN i :=
  toHom (Spec.map (trans (X.anti (leOfHom g))))

lemma chartTr_J {k i : X.J} (g : k ⟶ i) : chartTr hS X hN g ≫ chartJ hS X hN hV i = chartJ hS X hN hV k :=
  hom_ext_of_map (colimit.w (chartF X) g)

instance (i : X.J) : IsOpenImmersion ((SCH).map (chartJ hS X hN hV i)) :=
  inferInstanceAs (IsOpenImmersion (chartι X i))

instance {k i : X.J} (g : k ⟶ i) : IsOpenImmersion ((SCH).map (chartTr hS X hN g)) :=
  inferInstanceAs (IsOpenImmersion ((chartF X).map g))

lemma chartJ_mono (i : X.J) : Mono (chartJ hS X hN hV i) :=
  (SCH).mono_of_mono_map (IsOpenImmersion.mono _)


lemma ext_local {Y W : BigFppfOver B SZ hS} {s s' : Y ⟶ W}
    (h : ∀ y : (SCH).obj Y, ∃ (Y' : BigFppfOver B SZ hS) (p : Y' ⟶ Y), IsOpenImmersion ((SCH).map p) ∧
      y ∈ Set.range ((SCH).map p) ∧ p ≫ s = p ≫ s') : s = s' := by
  choose Y' p hp hy he using h
  have hcov : Sieve.ofArrows Y' p ∈ BigFppfOver.topology B SZ hS Y :=
    BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B SZ hS p hp fun y => ⟨y, hy y⟩
  refine ((BigFppfOver.isSheaf_of_type_yoneda_obj W) _ hcov).isSeparatedFor.ext ?_
  rintro Z i ⟨V, u, e, ⟨a⟩, rfl⟩
  change (u ≫ p a) ≫ s = (u ≫ p a) ≫ s'
  rw [Category.assoc, Category.assoc, he]

/-- The action is independent of the chart. -/
lemma smul_indep {Y : BigFppfOver B SZ hS} (k : APt (fppfO B SZ hS) M (op Y)) {a a' : X.J}
    (c : Y ⟶ cObj hS X hN a) (c' : Y ⟶ cObj hS X hN a') (he : c ≫ chartJ hS X hN hV a = c' ≫ chartJ hS X hN hV a') :
    ((chartAct hS X hN a).smul k c : Y ⟶ _) ≫ chartJ hS X hN hV a =
      ((chartAct hS X hN a').smul k c' : Y ⟶ _) ≫ chartJ hS X hN hV a' := by
  refine ext_local hS fun y => ?_
  have e1 : chartι X a ((SCH).map c y) = chartι X a' ((SCH).map c' y) := by
    have h0 := congrArg (SCH).map he
    rw [Functor.map_comp, Functor.map_comp] at h0
    have h1 := congrArg (fun m => m y) h0
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1
  obtain ⟨l, f, f', z, hz, hz'⟩ := (chart_eq_iff X _ _).1 e1
  let O : ((SCH).obj Y).Opens :=
    ((SCH).map c ⁻¹ᵁ ((SCH).map (chartTr hS X hN f)).opensRange) ⊓
      ((SCH).map c' ⁻¹ᵁ ((SCH).map (chartTr hS X hN f')).opensRange)
  obtain ⟨Y', p, hp, hr, -⟩ := exists_restrict_bigFppfOver Y O
  have hO : y ∈ O := ⟨⟨z, hz⟩, ⟨z, hz'⟩⟩
  obtain ⟨d, hd⟩ := exists_factor_open (chartTr hS X hN f) (p ≫ c) (by
    rintro _ ⟨w, rfl⟩
    have hw : (SCH).map p w ∈ O := by
      have : (SCH).map p w ∈ Set.range ((SCH).map p) := ⟨w, rfl⟩
      rw [hr] at this; exact this
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hw.1)
  obtain ⟨d', hd'⟩ := exists_factor_open (chartTr hS X hN f') (p ≫ c') (by
    rintro _ ⟨w, rfl⟩
    have hw : (SCH).map p w ∈ O := by
      have : (SCH).map p w ∈ Set.range ((SCH).map p) := ⟨w, rfl⟩
      rw [hr] at this; exact this
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hw.2)
  have hdd : d = d' := by
    have := chartJ_mono hS X hN hV l
    refine (cancel_mono (chartJ hS X hN hV l)).1 ?_
    have h1 : d ≫ chartJ hS X hN hV l = (p ≫ c) ≫ chartJ hS X hN hV a := by
      rw [← hd, Category.assoc, chartTr_J hS X hN hV]
    have h2 : d' ≫ chartJ hS X hN hV l = (p ≫ c') ≫ chartJ hS X hN hV a' := by
      rw [← hd', Category.assoc, chartTr_J hS X hN hV]
    rw [h1, h2, Category.assoc, Category.assoc, he]
  subst hdd
  refine ⟨Y', p, hp, ?_, ?_⟩
  · rw [hr]; exact hO
  · have mp : ∀ {b : X.J} (q : Y ⟶ cObj hS X hN b), p ≫ ((chartAct hS X hN b).smul k q : Y ⟶ _) =
        ((chartAct hS X hN b).smul (APt.res p.op k) (p ≫ q) : Y' ⟶ _) := fun {b} q =>
      (chartAct hS X hN b).map_smul p.op k q
    have st : ∀ {b : X.J} (g : l ⟶ b), ((chartAct hS X hN l).smul (APt.res p.op k) d : Y' ⟶ _) ≫ chartTr hS X hN g =
        ((chartAct hS X hN b).smul (APt.res p.op k) (d ≫ chartTr hS X hN g) : Y' ⟶ _) := fun {b} g =>
      smul_trans (X.anti (leOfHom g)) (hN b) (hN l) _ d
    rw [← Category.assoc, ← Category.assoc, mp, mp, ← hd, ← hd', ← st, ← st, Category.assoc, Category.assoc,
      chartTr_J hS X hN hV, chartTr_J hS X hN hV]

lemma cut_mem {T : BigFppfOver B SZ hS} (t : T ⟶ vObj hS X hV) :
    cutSieve (chartJ hS X hN hV) t ∈ BigFppfOver.topology B SZ hS T := by
  have hex := fun a => exists_restrict_bigFppfOver T ((SCH).map t ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange)
  choose Y p hp hr hl using hex
  have hcov : Sieve.ofArrows Y p ∈ BigFppfOver.topology B SZ hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B SZ hS p hp fun w => ?_
    obtain ⟨a, z, hz⟩ := chart_surjective X ((SCH).map t w)
    refine ⟨a, ?_⟩
    rw [hr a]
    exact ⟨z, hz⟩
  refine GrothendieckTopology.superset_covering _ ?_ hcov
  rintro Z i ⟨W, u, e, ⟨a⟩, rfl⟩
  obtain ⟨c, hc⟩ := exists_factor_open (chartJ hS X hN hV a) (p a ≫ t) (by
    rintro _ ⟨y, rfl⟩
    have hy : (SCH).map (p a) y ∈ ((SCH).map t ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange : Set _) := by
      rw [← hr a]
      exact ⟨y, rfl⟩
    rw [(SCH).map_comp, Scheme.Hom.comp_apply]
    exact hy)
  exact ⟨a, u ≫ c, by rw [Category.assoc, Category.assoc, hc]⟩

lemma hom_ext_vcut {T W : BigFppfOver B SZ hS} (t : T ⟶ vObj hS X hV) {s s' : T ⟶ W}
    (h : ∀ {Y : BigFppfOver B SZ hS} (i : Y ⟶ T) (a : X.J) (c : Y ⟶ cObj hS X hN a),
      i ≫ t = c ≫ chartJ hS X hN hV a → i ≫ s = i ≫ s') : s = s' := by
  refine ((BigFppfOver.isSheaf_of_type_yoneda_obj W) _ (cut_mem hS X hN hV t)).isSeparatedFor.ext ?_
  rintro Y i ⟨a, c, hc⟩
  exact h i a c hc

lemma exists_vsmul {T : BigFppfOver B SZ hS} (h : APt (fppfO B SZ hS) M (op T)) (t : T ⟶ vObj hS X hV) :
    ∃ s : T ⟶ vObj hS X hV, ∀ {Y : BigFppfOver B SZ hS} (i : Y ⟶ T) (a : X.J) (c : Y ⟶ cObj hS X hN a),
      i ≫ t = c ≫ chartJ hS X hN hV a →
        i ≫ s = ((chartAct hS X hN a).smul (APt.res i.op h) c : Y ⟶ _) ≫ chartJ hS X hN hV a := by
  have hsh := BigFppfOver.isSheaf_of_type_yoneda_obj (B := B) (S := SZ) (hS := hS) (vObj hS X hV)
  let val : ∀ {Y : BigFppfOver B SZ hS} (i : Y ⟶ T), (cutSieve (chartJ hS X hN hV) t).arrows i →
      (Y ⟶ vObj hS X hV) := fun {Y} i hi =>
    ((chartAct hS X hN hi.choose).smul (APt.res i.op h) hi.choose_spec.choose : Y ⟶ _) ≫ chartJ hS X hN hV _
  have hval : ∀ {Y : BigFppfOver B SZ hS} (i : Y ⟶ T) (hi : (cutSieve (chartJ hS X hN hV) t).arrows i) (a : X.J)
      (c : Y ⟶ cObj hS X hN a), i ≫ t = c ≫ chartJ hS X hN hV a →
      val i hi = ((chartAct hS X hN a).smul (APt.res i.op h) c : Y ⟶ _) ≫ chartJ hS X hN hV a := by
    intro Y i hi a c hc
    exact smul_indep hS X hN hV _ _ _ (hi.choose_spec.choose_spec.symm.trans hc)
  let fam : Presieve.FamilyOfElements (yoneda.obj (vObj hS X hV)) (cutSieve (chartJ hS X hN hV) t).arrows :=
    fun Y i hi => val i hi
  have hcomp : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Y' i u hi
    obtain ⟨a, c, hc⟩ := id hi
    change val (u ≫ i) _ = u ≫ val i hi
    rw [hval i hi a c hc, hval (u ≫ i) ((cutSieve (chartJ hS X hN hV) t).downward_closed hi u) a (u ≫ c)
      (by rw [Category.assoc, hc, Category.assoc])]
    have e := (chartAct hS X hN a).map_smul u.op (APt.res i.op h) c
    rw [← Category.assoc]
    refine congrArg (· ≫ chartJ hS X hN hV a) (Eq.trans ?_ e.symm)
    rw [op_comp, APt.res_comp]
    rfl
  obtain ⟨s, hs, -⟩ := hsh _ (cut_mem hS X hN hV t) fam hcomp
  refine ⟨s, fun {Y} i a c hc => ?_⟩
  have hi : (cutSieve (chartJ hS X hN hV) t).arrows i := ⟨a, c, hc⟩
  exact (hs i hi).trans (hval i hi a c hc)

/-- **§16.7.** The action of `D(M)` on the toric scheme `A(N)`: on `A(N_α)` it is the action of
Fact 2.12. -/
def toricAction : AAction (fppfO B SZ hS) M (yoneda.obj (vObj hS X hV)) where
  smul {T} h t := (exists_vsmul hS X hN hV (T := unop T) h t).choose
  one_smul {T} t := by
    refine hom_ext_vcut hS X hN hV (T := unop T) t fun i a c hc => ?_
    have := (exists_vsmul hS X hN hV (T := unop T) 1 t).choose_spec i a c hc
    refine this.trans ?_
    have e : APt.res i.op (1 : APt (fppfO B SZ hS) M (op (unop T))) = 1 := by
      ext p; simp
    rw [e, (chartAct hS X hN a).one_smul, hc]
  mul_smul {T} g h t := by
    refine hom_ext_vcut hS X hN hV (T := unop T) t fun i a c hc => ?_
    have h1 := (exists_vsmul hS X hN hV (T := unop T) (g * h) t).choose_spec i a c hc
    have h2 := (exists_vsmul hS X hN hV (T := unop T) h t).choose_spec i a c hc
    have h3 := (exists_vsmul hS X hN hV (T := unop T) g _).choose_spec i a _ h2
    refine h1.trans (Eq.trans ?_ h3.symm)
    rw [APt.res_mul, (chartAct hS X hN a).mul_smul]
  map_smul {T T'} s h t := by
    let r : unop T' ⟶ unop T := s.unop
    refine hom_ext_vcut hS X hN hV (T := unop T') (r ≫ t) fun i a c hc => ?_
    have h1 := (exists_vsmul hS X hN hV (T := unop T) h t).choose_spec (i ≫ r) a c
      (by rw [Category.assoc, hc])
    have h2 := (exists_vsmul hS X hN hV (T := unop T') (APt.res s h) (r ≫ t)).choose_spec i a c hc
    change i ≫ r ≫ _ = i ≫ _
    rw [← Category.assoc]
    have er : APt.res (i ≫ r).op h = APt.res i.op (APt.res s h) := by
      change APt.res (s ≫ i.op) h = _
      rw [APt.res_comp]
    rw [er] at h1
    exact h1.trans h2.symm

lemma toricAction_spec {T : BigFppfOver B SZ hS} (h : APt (fppfO B SZ hS) M (op T)) (a : X.J)
    (c : T ⟶ cObj hS X hN a) :
    ((toricAction hS X hN hV).smul h (c ≫ chartJ hS X hN hV a) : T ⟶ _) =
      ((chartAct hS X hN a).smul h c : T ⟶ _) ≫ chartJ hS X hN hV a := by
  have := (exists_vsmul hS X hN hV (T := T) h (c ≫ chartJ hS X hN hV a)).choose_spec (𝟙 T) a c (by simp)
  rw [Category.id_comp] at this
  refine this.trans ?_
  have e : APt.res (𝟙 T).op h = h := by
    rw [op_id, APt.res_id]
  rw [e]

/-- The charts are equivariant. -/
lemma chart_equivariant (a : X.J) :
    IsEquivariant (chartAct hS X hN a) (toricAction hS X hN hV) (yoneda.map (chartJ hS X hN hV a)) := by
  intro T h x
  exact (toricAction_spec hS X hN hV h a x).symm

lemma chart_isOpen (a : X.J) : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B SZ hS)))
    (yoneda.map (chartJ hS X hN hV a)) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B SZ hS _ _).2
    (inferInstanceAs (IsOpenImmersion ((SCH).map (chartJ hS X hN hV a))))

/-- **§16.7.** The toric scheme is Zariski locally linearizable: the `A(N_α)` are `D(M)`-stable affine
opens covering it. -/
def toricLinearizable : ZariskiLocallyLinearizable (toricAction hS X hN hV) X.J (cObj hS X hN) where
  act := chartAct hS X hN
  j a := yoneda.map (chartJ hS X hN hV a)
  equivariant := chart_equivariant hS X hN hV
  isOpen := chart_isOpen hS X hN hV
  isAffineHom a := inferInstanceAs (IsAffineHom (specULiftZIsTerminal.from (Spec (ZMon (X.N a)))))
  covers T x t := by
    let y : T ⟶ vObj hS X hV := yoneda.preimage x
    obtain ⟨a, z, hz⟩ := chart_surjective X ((SCH).map y t)
    refine ⟨a, ?_⟩
    obtain ⟨Y, p, hp, hr, -⟩ := exists_restrict_bigFppfOver T
      ((SCH).map y ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange)
    obtain ⟨c, hc⟩ := exists_factor_open (chartJ hS X hN hV a) (p ≫ y) (by
      rintro _ ⟨w, rfl⟩
      have hw : (SCH).map p w ∈ ((SCH).map y ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange : Set _) := by
        rw [← hr]; exact ⟨w, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hw)
    have ht : t ∈ Set.range ((SCH).map p) := by
      rw [hr]; exact ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := ht
    let rep := (chart_isOpen hS X hN hV a).rep
    have hsq : yoneda.map c ≫ yoneda.map (chartJ hS X hN hV a) = yoneda.map p ≫ x := by
      rw [← yoneda.map_comp, hc, yoneda.map_comp]
      simp [y]
    refine ⟨(SCH).map (rep.lift' _ _ hsq) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, rep.lift'_snd]

/-- **§16.7.** `∐ A(N_α) → A(N)` is a strongly-FPR equivariant atlas. The coproduct `Q` of the charts is
given as in Fact 7.3; it lies in the site if the index set of the charts is countable. -/
theorem toric_atlas {Q : BigFppfOver B SZ hS} {q : ∀ a, cObj hS X hN a ⟶ Q}
    (hQ : IsColimit (Cofan.mk Q q)) :
    ∃ (actQ : AAction (fppfO B SZ hS) M (yoneda.obj Q)) (v : yoneda.obj Q ⟶ yoneda.obj (vObj hS X hV)),
      IsStronglyFPRAtlas actQ (toricAction hS X hN hV) v :=
  fact73 (isAlgebraicSpace_yoneda B SZ hS _) (toricLinearizable hS X hN hV) hQ

/-- **§16.7, last assertion.** `{A(N_α)^L}` covers `A(N)^L`: a `T`-point of `A(N)^L` lifts, Zariski
locally on `T`, to a point of some `A(N_α)^L` (`M` finitely generated, `L` finitely generated, `A(N)`
separated; each `A(N_α)^L` is affine by Theorem 3.20 and the lift is unique as `A(N_α) → A(N)` is a
monomorphism). -/
theorem toric_attractor_cover [AddGroup.FG M]
    (hsep : IsSeparatedOver (yoneda.obj (vObj hS X hV))) {L : AddSubmonoid M} (hL : L.FG)
    {T : BigFppfOver B SZ hS} (x : AttractorPt (toricAction hS X hN hV) L T) (t : (SCH).obj T) :
    ∃ (a : X.J) (Y : BigFppfOver B SZ hS) (p : Y ⟶ T) (w : AttractorPt (chartAct hS X hN a) L Y),
      IsOpenImmersion ((SCH).map p) ∧ t ∈ Set.range ((SCH).map p) ∧
      AttractorPt.push ⟨yoneda.map (chartJ hS X hN hV a), chart_equivariant hS X hN hV a⟩ w =
        AttractorPt.baseChange p x := by
  have hX := isAlgebraicSpace_yoneda B SZ hS (vObj hS X hV)
  let Z := unitsSubgroup L
  have hQ : IsFace Z.toAddSubmonoid L := isFace_units L
  let x₀ : AttractorPt (toricAction hS X hN hV) Z.toAddSubmonoid T := AttractorPt.ofFace hQ x
  let y : T ⟶ vObj hS X hV := x₀.toPoint
  obtain ⟨a, z, hz⟩ := chart_surjective X ((SCH).map y t)
  obtain ⟨Y, p, hp, hr, -⟩ := exists_restrict_bigFppfOver T
    ((SCH).map y ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange)
  obtain ⟨u, hu⟩ := exists_factor_open (chartJ hS X hN hV a) (p ≫ y) (by
    rintro _ ⟨w, rfl⟩
    have hw : (SCH).map p w ∈ ((SCH).map y ⁻¹ᵁ ((SCH).map (chartJ hS X hN hV a)).opensRange : Set _) := by
      rw [← hr]; exact ⟨w, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hw)
  have hequiv : IsEquivariant (chartAct hS X hN a) (toricAction hS X hN hV)
      (yoneda.map (chartJ hS X hN hV a)) := fun h x => chart_equivariant hS X hN hV a h x
  let F : EquivariantHom (chartAct hS X hN a) (toricAction hS X hN hV) :=
    ⟨yoneda.map (chartJ hS X hN hV a), hequiv⟩
  have hmono : Mono (yoneda.map (chartJ hS X hN hV a)) := by
    have := chartJ_mono hS X hN hV a
    infer_instance
  have hZ : IsZFPR hequiv Z := isZFPR_of_mono hequiv Z
  have hfix : u ∈ (fixedPoints (quotientAction (chartAct hS X hN a) Z)).obj (op Y) := by
    refine (isFPR_iff (IsEquivariant.comap (actU := chartAct hS X hN a) (actX := toricAction hS X hN hV)
      hequiv (QuotientAddGroup.mk' Z))).mp hZ (op Y) u ?_
    have e : (yoneda.map (chartJ hS X hN hV a)).app (op Y) u = (yoneda.obj (vObj hS X hV)).map p.op x₀.toPoint := hu
    rw [e, ← AttractorPt.toPoint_baseChange]
    change _ ∈ (fixedPoints (quotientAction (toricAction hS X hN hV) Z)).obj (op Y)
    exact (AttractorPt.baseChange p x₀).toPoint_mem_fixedPoints
  have hcov : ∀ {W : BigFppfOver B SZ hS} (b : APt (fppfO B SZ hS) Z.toAddSubmonoid (op W)),
      extSieve (fppfO B SZ hS) Z b ∈ BigFppfOver.topology B SZ hS W :=
    fun b => extSieve_mem Z b
  let wZ : AttractorPt (chartAct hS X hN a) Z.toAddSubmonoid Y :=
    attractorFixedEquivOfCover (BigFppfOver.isSheaf_of_type_yoneda_obj _) hcov Y ⟨u, hfix⟩
  have hwZ : wZ.toPoint = u := congrArg Subtype.val
    ((attractorFixedEquivOfCover (act := chartAct hS X hN a) (BigFppfOver.isSheaf_of_type_yoneda_obj _)
      hcov Y).symm_apply_apply ⟨u, hfix⟩)
  have hpush : AttractorPt.ofFace hQ (AttractorPt.baseChange p x) = AttractorPt.push F wZ := by
    apply attractor_toPoint_injective_sep hX hsep
    change (AttractorPt.baseChange p x₀).toPoint = (yoneda.map (chartJ hS X hN hV a)).app (op Y) wZ.toPoint
    rw [AttractorPt.toPoint_baseChange, hwZ]
    exact hu.symm
  have het : Space.IsEtale B SZ hS (yoneda.map (chartJ hS X hN hV a)) := by
    intro V φ hφ
    refine MorphismProperty.comp_mem _ _ _ hφ ?_
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B SZ hS _ _).2 ?_
    exact inferInstanceAs (Etale ((SCH).map (chartJ hS X hN hV a)))
  haveI hAff : IsAffineHom (cObj hS X hN a).hom.hom :=
    inferInstanceAs (IsAffineHom (specULiftZIsTerminal.from (Spec (ZMon (X.N a)))))
  have hcart : IsFaceCartesian F hQ := isFaceCartesian_of_fg hX hsep F het hQ hL
  obtain ⟨w, hw⟩ := (hcart Y).2 ⟨(AttractorPt.baseChange p x, wZ), hpush⟩
  refine ⟨a, Y, p, w, hp, ?_, congrArg (fun q => q.1.1) hw⟩
  rw [hr]
  exact ⟨z, hz⟩

end Toric

end

end AlgMag.Mono

#print axioms AlgMag.prop1615_ii
#print axioms AlgMag.prop1615_ii_of_isAffineHom
#print axioms AlgMag.Dil.smooth_of_isDilatation
#print axioms AlgMag.Dil.cor13_3
#print axioms AlgMag.pureMagnets_p1
#print axioms AlgMag.Mono.toricAction
#print axioms AlgMag.Mono.toric_atlas
#print axioms AlgMag.Mono.toric_attractor_cover
