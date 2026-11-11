/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6FPR
import AlgMag.GeneralBaseCore
import AlgMag.Sec2Monoids
import AlgMag.SecLeftoverEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Schreier

/-!
# Remarks 6.5 and 6.6 of *Algebraic Magnetism*, corrected

Both printed examples use that `D(M) → D(Z)` is étale for `M/Z` finite. That holds only when `[M : Z]`
is invertible on the base: `D(ℤ/2)_ℤ → Spec ℤ` is not étale (`not_etale_printed_rem65`).

* **Remark 6.5, corrected.** `S = Spec R` with `|M|` invertible (the printed `S = Spec ℤ` becomes
  `Spec ℤ[1/2]`, `rem65_zmod2`). `rem65`.
* **Remark 6.6, corrected.** `[M : Z]` invertible, and `Z ≠ 0` is added: for `Z = 0`, `X = S` has
  `X^{D(M)} = X`, and `f` is not FPR. `rem66`.

The statements are in the category of `S`-schemes.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Leftover

open AlgMag.GB

variable (R : Type u) [CommRing R]

/-- `S = Spec R`. -/
noncomputable abbrev bs : Scheme.{u} := Spec (CommRingCat.of R)

/-- `D(G)_S` for `S = Spec R`: the spectrum of `R[G]`. -/
noncomputable abbrev dS (G : Type u) [AddCommMonoid G] : Over (bs R) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R G))))

variable {R}

/-- The ring map `R → Γ(T, ⊤)` of an `S`-scheme `T`. -/
noncomputable def rT (T : Over (bs R)) : R →+* Γ(T.left, ⊤) :=
  (homSpecEquiv T.left (CommRingCat.of R) T.hom).hom

section Pts

variable {G : Type u} [AddCommMonoid G]

/-- The ring map `R[G] → Γ(T, ⊤)` of a monoid map. -/
noncomputable def liftPt (T : Over (bs R)) (χ : Multiplicative G →* Γ(T.left, ⊤)) :
    AddMonoidAlgebra R G →+* Γ(T.left, ⊤) :=
  AddMonoidAlgebra.liftNCRingHom (rT T) χ (fun _ _ => Commute.all _ _)

lemma liftPt_single (T : Over (bs R)) (χ : Multiplicative G →* Γ(T.left, ⊤)) (g : G) (r : R) :
    liftPt T χ (AddMonoidAlgebra.single g r) = rT T r * χ (Multiplicative.ofAdd g) := by
  simp [liftPt, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single]

/-- The functor of points of `D(G)_S`, valued in `Γ`. -/
noncomputable def ptsG (T : Over (bs R)) : (T ⟶ dS R G) ≃ (Multiplicative G →* Γ(T.left, ⊤)) where
  toFun x :=
    { toFun := fun g => (homSpecEquiv T.left _ x.left).hom
        (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1)
      map_one' := by
        change (homSpecEquiv T.left _ x.left).hom (AddMonoidAlgebra.single 0 1) = 1
        rw [← AddMonoidAlgebra.one_def, map_one]
      map_mul' := fun a b => by
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl }
  invFun χ := Over.homMk
    ((homSpecEquiv T.left _).symm (CommRingCat.ofHom (liftPt T χ))) (by
      apply (homSpecEquiv T.left (CommRingCat.of R)).injective
      change homSpecEquiv T.left _ (_ ≫ Spec.map _) = _
      rw [homSpecEquiv_map, Equiv.apply_symm_apply]
      ext r
      change liftPt T χ (AddMonoidAlgebra.single 0 r) = rT T r
      rw [liftPt_single]
      have : χ (Multiplicative.ofAdd 0) = 1 := map_one χ
      rw [this, mul_one])
  left_inv x := by
    apply Over.OverMorphism.ext
    change (homSpecEquiv T.left _).symm _ = x.left
    rw [Equiv.symm_apply_eq]
    ext1
    have hw : homSpecEquiv T.left (CommRingCat.of R) (x.left ≫ (dS R G).hom) =
        homSpecEquiv T.left (CommRingCat.of R) T.hom := by rw [Over.w x]
    have hw' := hw
    rw [show (dS R G).hom = Spec.map _ from rfl, homSpecEquiv_map] at hw'
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun g => ?_)
    · change liftPt T _ _ = _
      rw [liftPt_single]
      have h1 := congrArg (fun k => k.hom r) hw'
      have h2 : rT T r = (homSpecEquiv T.left _ x.left).hom (AddMonoidAlgebra.single 0 r) := h1.symm
      rw [h2]
      have : ∀ (y : Multiplicative G →* Γ(T.left, ⊤)), y (Multiplicative.ofAdd 0) = 1 := fun y => map_one y
      rw [this, mul_one]
    · change liftPt T _ _ = _
      rw [liftPt_single, map_one, one_mul]
      rfl
  right_inv χ := by
    refine MonoidHom.ext fun g => ?_
    change (homSpecEquiv T.left _ ((homSpecEquiv T.left _).symm _)).hom _ = _
    rw [Equiv.apply_symm_apply]
    change liftPt T χ _ = _
    rw [liftPt_single, map_one, one_mul]
    rfl

/-- The functor of points of `D(G)_S`. -/
noncomputable def ptsD (T : Over (bs R)) : (T ⟶ dS R G) ≃ APt (overO (bs R)) G (op T) := ptsG T

lemma ptsD_apply {T : Over (bs R)} (x : T ⟶ dS R G) (g : G) :
    ptsD T x (Multiplicative.ofAdd g) =
      (homSpecEquiv T.left _ x.left).hom (AddMonoidAlgebra.single g 1) := rfl

lemma ptsD_comp {T T' : Over (bs R)} (s : T' ⟶ T) (x : T ⟶ dS R G) :
    ptsD T' (s ≫ x) = APt.res s.op (ptsD T x) := by
  refine MonoidHom.ext fun g => ?_
  change (homSpecEquiv T'.left _ (s.left ≫ x.left)).hom _ = _
  rw [homSpecEquiv_comp]
  rfl

end Pts

section Action

variable {G P : Type u} [AddCommGroup G] [AddCommGroup P]

/-- `D(P)` acts on `D(G)` through `ι : G → P`. -/
noncomputable def actD (ι : G →+ P) : AAction (overO (bs R)) P (yoneda.obj (dS R G)) where
  smul {U} h x := (ptsD (unop U)).symm (h.comp (AddMonoidHom.toMultiplicative ι) * ptsD (unop U) x)
  one_smul {U} x := by
    apply (ptsD (unop U)).injective
    rw [Equiv.apply_symm_apply]
    ext g
    simp
  mul_smul {U} g h x := by
    apply (ptsD (unop U)).injective
    simp only [Equiv.apply_symm_apply]
    ext a
    simp [mul_assoc]
  map_smul {U V} f h x := by
    apply (ptsD (unop V)).injective
    change ptsD (unop V) (f.unop ≫ _) = ptsD (unop V) ((ptsD (unop V)).symm _)
    rw [Equiv.apply_symm_apply, ptsD_comp, Equiv.apply_symm_apply]
    change _ = _ * ptsD (unop V) (f.unop ≫ x)
    rw [ptsD_comp]
    ext a
    simp [APt.res]

lemma ptsD_smul (ι : G →+ P) {T : Over (bs R)} (h : APt (overO (bs R)) P (op T)) (x : T ⟶ dS R G)
    (g : G) :
    ptsD T ((actD ι).smul h x) (Multiplicative.ofAdd g) =
      h (Multiplicative.ofAdd (ι g)) * ptsD T x (Multiplicative.ofAdd g) := by
  change ptsD T ((ptsD T).symm _) _ = _
  rw [Equiv.apply_symm_apply]
  rfl

end Action

/-- `D(P)` has no fixed point over a nonempty scheme as soon as some `c ≠ 0` of `P` acts freely: the
test object is `Spec κ(t)[P]`. -/
theorem no_fixed {P : Type u} [AddCommGroup P] {T : Over (bs R)} (t : T.left) (c : P) (hc : c ≠ 0)
    (H : ∀ {T' : Over (bs R)} (s : T' ⟶ T) (h : APt (overO (bs R)) P (op T')),
      ∃ u : (overO (bs R)).obj (op T'), IsUnit u ∧ h (Multiplicative.ofAdd c) * u = u) : False := by
  let k := T.left.residueField t
  let A : CommRingCat.{u} := CommRingCat.of (AddMonoidAlgebra k P)
  let w : Spec A ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k P))) ≫ T.left.fromSpecResidueField t
  let T' : Over (bs R) := Over.mk (w ≫ T.hom)
  let s : T' ⟶ T := Over.homMk w rfl
  let hA : Multiplicative P →* Γ(Spec A, ⊤) :=
    { toFun := fun g => (Scheme.ΓSpecIso A).inv.hom
        (AddMonoidAlgebra.single (Multiplicative.toAdd g) (1 : k))
      map_one' := by
        have e : (AddMonoidAlgebra.single (Multiplicative.toAdd (1 : Multiplicative P)) (1 : k)) =
          (1 : AddMonoidAlgebra k P) := rfl
        exact (congrArg _ e).trans (map_one _)
      map_mul' := fun a b => by
        have e : (AddMonoidAlgebra.single (Multiplicative.toAdd (a * b)) (1 : k)) =
          (AddMonoidAlgebra.single (Multiplicative.toAdd a) (1 : k)) *
            (AddMonoidAlgebra.single (Multiplicative.toAdd b) (1 : k)) := by
          rw [AddMonoidAlgebra.single_mul_single, one_mul]
          rfl
        exact (congrArg _ e).trans (map_mul _ _ _) }
  obtain ⟨u, hu, e⟩ := H s hA
  have e1 : hA (Multiplicative.ofAdd c) = 1 := by
    exact (IsUnit.mul_left_inj hu).1 (e.trans (one_mul u).symm)
  have e2 : (AddMonoidAlgebra.single c (1 : k) : AddMonoidAlgebra k P) = 1 := by
    have hinj : Function.Injective (Scheme.ΓSpecIso A).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1
    apply hinj
    exact e1.trans (map_one (Scheme.ΓSpecIso A).inv.hom).symm
  rw [AddMonoidAlgebra.one_def] at e2
  exact hc (AddMonoidAlgebra.single_left_injective one_ne_zero e2)

/-- Over an empty scheme every point is fixed. -/
lemma smul_eq_of_isEmpty {G P : Type u} [AddCommGroup G] [AddCommGroup P] (ι : G →+ P)
    {T T' : Over (bs R)} (s : T' ⟶ T) [IsEmpty T.left] (h : APt (overO (bs R)) P (op T'))
    (x : T' ⟶ dS R G) : (actD ι).smul h x = x := by
  have : IsEmpty T'.left := Function.isEmpty s.left
  apply Over.OverMorphism.ext
  exact (isInitialOfIsEmpty (X := T'.left)).hom_ext _ _

section Etale

variable (R) {M : Type u} [AddCommGroup M]

/-- `R[Z] → R[M]` is étale if `[M : Z]` is finite and invertible, `M` finitely generated. -/
theorem etale_incl [AddGroup.FG M] (Z : AddSubgroup M) (hfin : Z.FiniteIndex)
    (hn : IsUnit ((Z.index : ℕ) : R)) : (incl R Z).Etale := by
  letI := inclAlg R Z
  have h1 := formallyEtale_incl R Z hfin hn
  have : AddGroup.FG Z := AddSubgroup.fg_of_index_ne_zero Z
  have hFT : Algebra.FiniteType R (AddMonoidAlgebra R Z) := inferInstance
  have hFP : Algebra.FinitePresentation R (AddMonoidAlgebra R M) := AlgMag.finitePresentation R M
  have : IsScalarTower R (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change AddMonoidAlgebra.single 0 r = incl R Z (AddMonoidAlgebra.single 0 r)
      rw [incl_single]
      rfl
  have h2 : Algebra.FinitePresentation (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  exact RingHom.etale_algebraMap.2 ⟨h1, h2⟩

/-- `R → R[⊥]` is bijective. -/
lemma bot_bijective : Function.Bijective
    (algebraMap R (AddMonoidAlgebra R (⊥ : AddSubgroup M))) := by
  constructor
  · intro a b h
    have h' : (AddMonoidAlgebra.single 0 a : AddMonoidAlgebra R (⊥ : AddSubgroup M)) =
      AddMonoidAlgebra.single 0 b := h
    have := congrArg (fun c => AddMonoidAlgebra.coeff c 0) h'
    simpa using this
  · intro a
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add f g hf hg =>
      obtain ⟨x, rfl⟩ := hf
      obtain ⟨y, rfl⟩ := hg
      exact ⟨x + y, map_add _ _ _⟩
    | single z r =>
      refine ⟨r, ?_⟩
      have : z = 0 := Subsingleton.elim _ _
      rw [this]
      rfl

/-- `R → R[M]` is étale for `M` finite with `|M|` invertible. -/
theorem etale_algebraMap_of_finite [Finite M] (hn : IsUnit ((Nat.card M : ℕ) : R)) :
    (algebraMap R (AddMonoidAlgebra R M)).Etale := by
  have : AddGroup.FG M := inferInstance
  have h := etale_incl R (⊥ : AddSubgroup M) inferInstance (by rwa [AddSubgroup.index_bot])
  have e : algebraMap R (AddMonoidAlgebra R M) =
      (incl R (⊥ : AddSubgroup M)).comp (algebraMap R (AddMonoidAlgebra R (⊥ : AddSubgroup M))) := by
    refine RingHom.ext fun r => ?_
    change AddMonoidAlgebra.single 0 r = incl R (⊥ : AddSubgroup M) (AddMonoidAlgebra.single 0 r)
    rw [incl_single]
    rfl
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (bot_bijective R)) h

/-- **The printed example of Remark 6.5 fails.** `D(ℤ/2)_ℤ → Spec ℤ` is not étale. -/
theorem not_etale_printed_rem65 : ¬ Etale (dS ℤ (ZMod 2)).hom := by
  intro h
  have h' : (algebraMap ℤ (AddMonoidAlgebra ℤ (ZMod 2))).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).1 h
  have h2 := RingHom.etale_algebraMap.1 h'
  exact not_formallyUnramified_int_zmod2 inferInstance

end Etale

section Rem65

variable (R) (M : Type u) [AddCommGroup M]

/-- `X = S`, with the trivial action. -/
noncomputable def actTriv : AAction (overO (bs R)) M (yoneda.obj (Over.mk (𝟙 (bs R)))) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := rfl

/-- `D(M)_S → S`. -/
noncomputable def toBaseD : dS R M ⟶ Over.mk (𝟙 (bs R)) :=
  Over.homMk (dS R M).hom (Category.comp_id _)

lemma base_ext {T : Over (bs R)} (a b : T ⟶ Over.mk (𝟙 (bs R))) : a = b := by
  apply Over.OverMorphism.ext
  have ha := Over.w a
  have hb := Over.w b
  simp only [Over.mk_hom, Category.comp_id] at ha hb
  exact ha.trans hb.symm

lemma toBaseD_equivariant :
    IsEquivariant (actD (R := R) (AddMonoidHom.id M)) (actTriv R M) (yoneda.map (toBaseD R M)) :=
  fun _ _ => base_ext R _ _

/-- **Remark 6.5, corrected.** If `M ≠ 0` is finite with `|M|` invertible in `R ≠ 0`, then
`D(M)_S → S` is étale and equivariant, and it is not FPR: `U^{D(M)} = ∅` whereas `X^{D(M)} = X`. -/
theorem rem65 [Nontrivial R] [Nontrivial M] [Finite M] (hn : IsUnit ((Nat.card M : ℕ) : R)) :
    Etale (dS R M).hom ∧ ¬ IsFPR (toBaseD_equivariant R M) := by
  refine ⟨(HasRingHomProperty.Spec_iff (P := @Etale)).2 (etale_algebraMap_of_finite R hn), ?_⟩
  intro hF
  have hfix : (𝟙 (dS R M) : (yoneda.obj (dS R M)).obj (op (dS R M))) ∈
      (fixedPoints (actD (R := R) (AddMonoidHom.id M))).obj (op (dS R M)) :=
    (isFPR_iff _).1 hF (op (dS R M)) (𝟙 _) (fun s h => base_ext R _ _)
  obtain ⟨c, hc⟩ := exists_ne (0 : M)
  have : Nonempty (dS R M).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of _)))
  obtain ⟨t⟩ := this
  refine no_fixed t c hc fun {T'} s h => ?_
  let y := (yoneda.obj (dS R M)).map s.op (𝟙 _)
  refine ⟨ptsD T' y (Multiplicative.ofAdd c), (Group.isUnit _).map (ptsD T' y), ?_⟩
  have e : (actD (AddMonoidHom.id M)).smul h y = y := hfix s.op h
  have e2 := ptsD_smul (R := R) (AddMonoidHom.id M) h y c
  rw [show (actD (AddMonoidHom.id M)).smul h y = y from e] at e2
  exact e2.symm

/-- **Remark 6.5, corrected**, the printed example over `ℤ[1/2]`. -/
theorem rem65_zmod2 :
    Etale (dS (Localization.Away (2 : ℤ)) (ZMod 2)).hom ∧
      ¬ IsFPR (toBaseD_equivariant (Localization.Away (2 : ℤ)) (ZMod 2)) := by
  have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
  have : Nontrivial (Localization.Away (2 : ℤ)) :=
    (IsLocalization.injective (Localization.Away (2 : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors h2)).nontrivial
  refine rem65 _ _ ?_
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (2 : ℤ)) (2 : ℤ)
  rw [Nat.card_zmod]
  simpa using this

end Rem65

section Rem66

variable (R) {M : Type u} [AddCommGroup M] (Z : AddSubgroup M)

/-- `f : D(M)_S → D(Z)_S`. -/
noncomputable def fD : dS R M ⟶ dS R Z :=
  Over.homMk (Spec.map (CommRingCat.ofHom (incl R Z))) (by
    change _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change incl R Z (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
    rw [incl_single]
    rfl)

lemma ptsD_fD {T : Over (bs R)} (x : T ⟶ dS R M) (z : Z) :
    ptsD T (x ≫ fD R Z) (Multiplicative.ofAdd z) = ptsD T x (Multiplicative.ofAdd (z : M)) := by
  change (homSpecEquiv T.left _ (x.left ≫ Spec.map _)).hom _ = _
  rw [homSpecEquiv_map]
  change (homSpecEquiv T.left _ x.left).hom (incl R Z (AddMonoidAlgebra.single z 1)) = _
  rw [incl_single]
  rfl

lemma fD_equivariant :
    IsEquivariant (actD (R := R) (AddMonoidHom.id M)) (actD (R := R) Z.subtype)
      (yoneda.map (fD R Z)) := by
  intro T h x
  apply (ptsD (unop T)).injective
  refine MonoidHom.ext fun a => ?_
  obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective a
  change ptsD _ (_ ≫ fD R Z) _ = ptsD _ ((actD Z.subtype).smul h (x ≫ fD R Z)) _
  rw [ptsD_fD, ptsD_smul, ptsD_smul, ptsD_fD]
  rfl

/-- **Remark 6.6, corrected.** Let `Z ≠ 0`, `Z ≠ M` be of finite index in the finitely generated `M`,
with `[M : Z]` invertible in `R ≠ 0`. Then `f : D(M)_S → D(Z)_S` is étale, surjective, equivariant and
FPR, but not `Z`-FPR. The printed hypotheses were `Z ≠ M`, `M/Z` finite: `[M : Z]` invertible is needed
for étale, `Z ≠ 0` for FPR. -/
theorem rem66 [Nontrivial R] [AddGroup.FG M] (hfin : Z.FiniteIndex) (h0 : Z ≠ ⊥) (hT : Z ≠ ⊤)
    (hn : IsUnit ((Z.index : ℕ) : R)) :
    Etale (fD R Z).left ∧ Surjective (fD R Z).left ∧ IsFPR (fD_equivariant R Z) ∧
      ¬ IsZFPR (fD_equivariant R Z) Z := by
  refine ⟨(HasRingHomProperty.Spec_iff (P := @Etale)).2 (etale_incl R Z hfin hn), ?_, ?_, ?_⟩
  · refine ⟨fun p => ?_⟩
    letI := inclAlg R Z
    have := isIntegral_incl R Z hfin
    let p' : PrimeSpectrum (AddMonoidAlgebra R Z) := p
    have : p'.asIdeal.IsPrime := p'.2
    have hbot : Ideal.comap (algebraMap (AddMonoidAlgebra R Z) (AddMonoidAlgebra R M))
        (⊥ : Ideal (AddMonoidAlgebra R M)) = ⊥ :=
      Ideal.comap_bot_of_injective _ (incl_injective R Z)
    obtain ⟨Q, -, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p'.asIdeal
      (⊥ : Ideal (AddMonoidAlgebra R M)) (by rw [hbot]; exact bot_le)
    exact ⟨(⟨Q, hQ⟩ : PrimeSpectrum (AddMonoidAlgebra R M)), PrimeSpectrum.ext hQ'⟩
  · refine (isFPR_iff _).2 fun T x hx => ?_
    obtain ⟨T⟩ := T
    by_cases hemp : IsEmpty T.left
    · intro s h
      exact smul_eq_of_isEmpty _ s.unop h _
    · exfalso
      obtain ⟨t⟩ := not_isEmpty_iff.1 hemp
      obtain ⟨w, hw⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 h0
      have hz0 : (w : M) ≠ 0 := fun e => hw (Subtype.ext e)
      refine no_fixed t (w : M) hz0 fun {T'} s h => ?_
      let y : T' ⟶ dS R Z := s ≫ x ≫ fD R Z
      refine ⟨ptsD T' y (Multiplicative.ofAdd w), (Group.isUnit _).map (ptsD T' y), ?_⟩
      have e : (actD Z.subtype).smul h y = y := hx s.op h
      have e2 := ptsD_smul (R := R) Z.subtype h y w
      rw [e] at e2
      exact e2.symm
  · intro hF
    have hF' : (𝟙 (dS R M) : (yoneda.obj (dS R M)).obj (op (dS R M))) ∈
        (fixedPoints ((actD (R := R) (AddMonoidHom.id M)).comap (QuotientAddGroup.mk' Z))).obj
          (op (dS R M)) := (isFPR_iff (IsEquivariant.comap (fD_equivariant R Z) (QuotientAddGroup.mk' Z))).1 hF (op (dS R M)) (𝟙 _) (by
      refine fun {T'} s h => ?_
      change (actD Z.subtype).smul _ _ = _
      apply (ptsD (unop T')).injective
      refine MonoidHom.ext fun a => ?_
      obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective a
      refine (ptsD_smul _ _ _ z).trans ?_
      have : h (Multiplicative.ofAdd ((QuotientAddGroup.mk' Z) (z : M))) = 1 := by
        have e : (QuotientAddGroup.mk' Z) (z : M) = 0 := (QuotientAddGroup.eq_zero_iff _).2 z.2
        rw [e]
        exact map_one h
      change h (Multiplicative.ofAdd ((QuotientAddGroup.mk' Z) (z : M))) * _ = _
      rw [this, one_mul])
    obtain ⟨q, hq⟩ : ∃ q : M, q ∉ Z := by
      by_contra hne
      push_neg at hne
      exact hT (eq_top_iff.2 fun x _ => hne x)
    have hc : (QuotientAddGroup.mk' Z) q ≠ 0 := fun e => hq ((QuotientAddGroup.eq_zero_iff _).1 e)
    have : Nonempty (dS R M).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of _)))
    obtain ⟨t⟩ := this
    refine no_fixed t _ hc fun {T'} s h => ?_
    let y := (yoneda.obj (dS R M)).map s.op (𝟙 _)
    refine ⟨ptsD T' y (Multiplicative.ofAdd q), (Group.isUnit _).map (ptsD T' y), ?_⟩
    have e : (actD (AddMonoidHom.id M)).smul (h.comp (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Z))) y = y := hF' s.op h
    have e2 := ptsD_smul (R := R) (AddMonoidHom.id M) (h.comp (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Z))) y q
    rw [e] at e2
    exact e2.symm

end Rem66

end AlgMag.Leftover

#print axioms AlgMag.Leftover.rem65
#print axioms AlgMag.Leftover.rem65_zmod2
#print axioms AlgMag.Leftover.rem66
#print axioms AlgMag.Leftover.not_etale_printed_rem65
