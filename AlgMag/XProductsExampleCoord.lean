/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsExample

/-!
# Example 4.4: coordinates on the two charts of `𝔸(𝒩) = ℙ¹`

Preparation for the classification of the attractors in Example 4.4.

## Main results

* `AlgMag.XP.coordEquiv`: `Hom(T, 𝔸(N_ε)) = Γ(T)`.
* `AlgMag.XP.coord_of_fixed`: a point of a chart which is fixed by `G_m` is `0`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

noncomputable section

variable {T T' : Scheme.{0}}

/-- The exponent of `n ∈ N_ε`: `n = k ε`. -/
def exExp {b : Bool} (n : exFam.N b) : ℕ := (n.1 * exE b).toNat

lemma exE_mul_self (b : Bool) : exE b * exE b = 1 := by cases b <;> rfl

lemma exExp_spec {b : Bool} (n : exFam.N b) : n.1 = (exExp n : ℤ) * exE b := by
  obtain ⟨k, hk⟩ := mem_exN.mp n.2
  have : n.1 * exE b = k := by rw [hk, mul_assoc, exE_mul_self, mul_one]
  rw [exExp, this, Int.toNat_natCast]
  exact hk

lemma exExp_add {b : Bool} (m n : exFam.N b) : exExp (m + n) = exExp m + exExp n := by
  have h1 := exExp_spec m
  have h2 := exExp_spec n
  have h3 := exExp_spec (m + n)
  have h4 : ((m + n : exFam.N b) : ℤ) = m.1 + n.1 := rfl
  have hne : exE b ≠ 0 := by cases b <;> decide
  have : ((exExp (m + n) : ℤ)) * exE b = ((exExp m : ℤ) + exExp n) * exE b := by
    rw [← h3, h4, add_mul, ← h1, ← h2]
  have h5 := mul_right_cancel₀ hne this
  exact_mod_cast h5

/-- The monoid map `N_ε → Γ(T)`, `kε ↦ r^k`: the point of the chart with coordinate `r`. -/
def powHom (b : Bool) (r : Scheme.Γ.obj (op T)) : APt Scheme.Γ (exFam.N b) (op T) where
  toFun n := r ^ exExp (Multiplicative.toAdd n)
  map_one' := by
    have : exExp (0 : exFam.N b) = 0 := by
      have h := exExp_spec (0 : exFam.N b)
      have hne : exE b ≠ 0 := by cases b <;> decide
      have h' : (exExp (0 : exFam.N b) : ℤ) * exE b = 0 := h.symm
      have := (mul_eq_zero.mp h').resolve_right hne
      exact_mod_cast this
    change r ^ exExp (0 : exFam.N b) = 1
    rw [this, pow_zero]
  map_mul' m n := by
    change r ^ exExp (Multiplicative.toAdd m + Multiplicative.toAdd n) = _
    rw [exExp_add, pow_add]

lemma exExp_gen (b : Bool) : exExp (Multiplicative.toAdd (exGen b)) = 1 := by
  change (exE b * exE b).toNat = 1
  rw [exE_mul_self]
  rfl

lemma eq_powHom {b : Bool} (h : APt Scheme.Γ (exFam.N b) (op T)) :
    h = powHom b (h (exGen b)) := by
  refine MonoidHom.ext fun n => ?_
  have hn : n = exGen b ^ exExp (Multiplicative.toAdd n) := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [toAdd_pow]
    have := exExp_spec (Multiplicative.toAdd n)
    refine this.trans ?_
    change _ = ((exExp (Multiplicative.toAdd n) • (Multiplicative.toAdd (exGen b)) : exFam.N b) : ℤ)
    rw [AddSubmonoidClass.coe_nsmul]
    change _ = exExp (Multiplicative.toAdd n) • exE b
    simp
  conv_lhs => rw [hn, map_pow]
  rfl

/-- `Hom(T, 𝔸(N_ε)) = Γ(T)`: the coordinate on a chart of `ℙ¹`. -/
def coordEquiv (b : Bool) (T : Scheme.{0}) : (T ⟶ AZ (exFam.N b)) ≃ Scheme.Γ.obj (op T) where
  toFun := exCoord
  invFun r := (pts (exFam.N b) T).symm (powHom b r)
  left_inv a := by
    apply (pts _ T).injective
    rw [Equiv.apply_symm_apply]
    exact (eq_powHom _).symm
  right_inv r := by
    change pts (exFam.N b) T ((pts (exFam.N b) T).symm (powHom b r)) (exGen b) = r
    rw [Equiv.apply_symm_apply]
    change r ^ exExp (Multiplicative.toAdd (exGen b)) = r
    rw [exExp_gen, pow_one]

/-- The point of the chart with coordinate `r`. -/
abbrev mkPt (b : Bool) (r : Scheme.Γ.obj (op T)) : T ⟶ AZ (exFam.N b) := (coordEquiv b T).symm r

lemma exCoord_mkPt (b : Bool) (r : Scheme.Γ.obj (op T)) : exCoord (mkPt b r) = r :=
  (coordEquiv b T).apply_symm_apply r

lemma mkPt_exCoord {b : Bool} (a : T ⟶ AZ (exFam.N b)) : mkPt b (exCoord a) = a :=
  (coordEquiv b T).symm_apply_apply a

lemma exCoord_comp {b : Bool} (g : T' ⟶ T) (a : T ⟶ AZ (exFam.N b)) :
    exCoord (g ≫ a) = (Scheme.Γ.map g.op).hom (exCoord a) := by
  unfold exCoord
  rw [pts_comp]
  rfl

lemma exCoord_smulA {b : Bool} (k : APt Scheme.Γ ℤ (op T)) (a : T ⟶ AZ (exFam.N b)) :
    exCoord (smulA k a) = k (Multiplicative.ofAdd (exE b)) * exCoord a :=
  ex_coord_smul k a

lemma exZero_eq_powHom (b : Bool) : exZeroHom b T = powHom b 0 := by
  rw [eq_powHom (exZeroHom b T), exZero_gen]

/-- `exPt b` is the point of the chart `b` with coordinate `0`. -/
lemma exPt_eq (b : Bool) : exPt b T = mkPt b 0 ≫ exFam.ι b := by
  rw [exPt, exZero_eq_powHom]
  rfl

/-- Two points of the two charts with the same image in `ℙ¹` have inverse coordinates. -/
lemma coord_mul_of_overlap {b : Bool} (a : T ⟶ AZ (exFam.N b)) (a' : T ⟶ AZ (exFam.N (!b)))
    (e : a ≫ exFam.ι b = a' ≫ exFam.ι (!b)) : exCoord a * exCoord a' = 1 := by
  obtain ⟨u, rfl, rfl⟩ := exFam.exists_factor_of_overlap (by cases b <;> decide) a a' e
  unfold exCoord
  rw [pts_gp, pts_gp, ← map_mul]
  have hneg : exGenZ b * exGenZ (!b) = 1 := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    cases b <;> rfl
  rw [hneg, map_one]

/-- If the coordinate `c` of a point of chart `b` is invertible, the point also lies in chart `!b`, with
coordinate `c⁻¹`. -/
lemma overlap_of_coord_mul {b : Bool} (r r' : Scheme.Γ.obj (op T)) (h : r * r' = 1) :
    mkPt b r ≫ exFam.ι b = mkPt (!b) r' ≫ exFam.ι (!b) := by
  let a : Γ(T, ⊤)ˣ := ⟨r, r', h, (mul_comm r' r).trans h⟩
  let hh : Multiplicative exFam.Z.toAddSubmonoid →* Scheme.Γ.obj (op T) :=
    { toFun := fun n => ((a ^ ((Multiplicative.toAdd n).1 * exE b) : Γ(T, ⊤)ˣ) : Γ(T, ⊤))
      map_one' := by
        change ((a ^ ((0 : ℤ) * exE b) : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) = 1
        rw [zero_mul, zpow_zero]
        rfl
      map_mul' := fun m n => by
        change ((a ^ (((Multiplicative.toAdd m).1 + (Multiplicative.toAdd n).1) * exE b) :
          Γ(T, ⊤)ˣ) : Γ(T, ⊤)) = _
        rw [add_mul, zpow_add, Units.val_mul]
        rfl }
  let u : T ⟶ exFam.D := (pts exFam.Z.toAddSubmonoid T).symm hh
  have hu : pts exFam.Z.toAddSubmonoid T u = hh := Equiv.apply_symm_apply _ _
  have h1 : mkPt b r = u ≫ exFam.gpMap b := by
    apply (coordEquiv b T).injective
    change exCoord (mkPt b r) = exCoord (u ≫ exFam.gpMap b)
    rw [exCoord_mkPt]
    unfold exCoord
    rw [pts_gp, hu]
    change r = ((a ^ (exE b * exE b) : Γ(T, ⊤)ˣ) : Γ(T, ⊤))
    rw [exE_mul_self, zpow_one]
  have h2 : mkPt (!b) r' = u ≫ exFam.gpMap (!b) := by
    apply (coordEquiv (!b) T).injective
    change exCoord (mkPt (!b) r') = exCoord (u ≫ exFam.gpMap (!b))
    rw [exCoord_mkPt]
    unfold exCoord
    rw [pts_gp, hu]
    change r' = ((a ^ (exE (!b) * exE b) : Γ(T, ⊤)ˣ) : Γ(T, ⊤))
    have : exE (!b) * exE b = -1 := by cases b <;> rfl
    rw [this, zpow_neg_one]
    rfl
  rw [h1, h2, Category.assoc, Category.assoc, exFam.gpMap_ι, exFam.gpMap_ι]

section Affine

variable {S S' : CommRingCat.{0}}

/-- The coordinate in the ring `S` of a point of a chart over `Spec S`. -/
def coordS {b : Bool} (a : Spec S ⟶ AZ (exFam.N b)) : S := (Scheme.ΓSpecIso S).hom.hom (exCoord a)

/-- The point of a chart over `Spec S` with coordinate `c ∈ S`. -/
def ptS (b : Bool) (c : S) : Spec S ⟶ AZ (exFam.N b) := mkPt b ((Scheme.ΓSpecIso S).inv.hom c)

lemma coordS_ptS (b : Bool) (c : S) : coordS (ptS b c) = c := by
  have e : exCoord (mkPt (T := Spec S) b ((Scheme.ΓSpecIso S).inv.hom c)) =
      (Scheme.ΓSpecIso S).inv.hom c := exCoord_mkPt b _
  exact (congrArg (Scheme.ΓSpecIso S).hom.hom e).trans
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).inv_hom_id c)

lemma ptS_coordS {b : Bool} (a : Spec S ⟶ AZ (exFam.N b)) : ptS b (coordS a) = a := by
  unfold coordS ptS
  have : (Scheme.ΓSpecIso S).inv.hom ((Scheme.ΓSpecIso S).hom.hom (exCoord a)) = exCoord a :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).hom_inv_id (exCoord a)
  rw [this, mkPt_exCoord]

lemma coordS_inj {b : Bool} {a a' : Spec S ⟶ AZ (exFam.N b)} (h : coordS a = coordS a') : a = a' := by
  rw [← ptS_coordS a, ← ptS_coordS a', h]

lemma coordS_comp {b : Bool} (θ : S ⟶ S') (a : Spec S ⟶ AZ (exFam.N b)) :
    coordS (Spec.map θ ≫ a) = θ.hom (coordS a) := by
  unfold coordS
  rw [exCoord_comp]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality θ) (exCoord a)

/-- The element of `D(M)(Spec S)` attached to a character of `ℤ` with values in `S`. -/
def charS (κ : Multiplicative ℤ →* S) : APt Scheme.Γ ℤ (op (Spec S)) :=
  ((Scheme.ΓSpecIso S).inv.hom : S →+* _).toMonoidHom.comp κ

lemma coordS_smulA {b : Bool} (κ : Multiplicative ℤ →* S) (a : Spec S ⟶ AZ (exFam.N b)) :
    coordS (smulA (charS κ) a) = κ (Multiplicative.ofAdd (exE b)) * coordS a := by
  have e := exCoord_smulA (charS κ) a
  refine (congrArg (Scheme.ΓSpecIso S).hom.hom e).trans ?_
  refine (map_mul (Scheme.ΓSpecIso S).hom.hom (charS κ (Multiplicative.ofAdd (exE b)))
    (exCoord a)).trans ?_
  exact congrArg (· * coordS a)
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso S).inv_hom_id (κ (Multiplicative.ofAdd (exE b))))

/-- The tautological character of the Laurent polynomials. -/
def tChar (R : CommRingCat.{0}) : Multiplicative ℤ →* CommRingCat.of (AddMonoidAlgebra R ℤ) where
  toFun n := AddMonoidAlgebra.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' m n := by
    rw [AddMonoidAlgebra.single_mul_single, mul_one]
    rfl

/-- `R → R[ℤ]`. -/
def laurentC (R : CommRingCat.{0}) : R ⟶ CommRingCat.of (AddMonoidAlgebra R ℤ) :=
  CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom)

/-- A point of a chart over `Spec R` which is fixed by `G_m` has coordinate `0`. -/
theorem coordS_eq_zero_of_fixed {R : CommRingCat.{0}} {d : Bool} (a : Spec R ⟶ AZ (exFam.N d))
    (hfix : smulA (charS (tChar R)) (Spec.map (laurentC R) ≫ a) = Spec.map (laurentC R) ≫ a) :
    coordS a = 0 := by
  have h := congrArg coordS hfix
  rw [coordS_smulA, coordS_comp] at h
  have h' : AddMonoidAlgebra.single (exE d) (1 : R) *
      AddMonoidAlgebra.single (0 : ℤ) (coordS a) = AddMonoidAlgebra.single (0 : ℤ) (coordS a) := h
  rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul] at h'
  have hne : exE d ≠ 0 := by cases d <;> decide
  have h2 : (AddMonoidAlgebra.single (exE d) (coordS a) : AddMonoidAlgebra R ℤ).coeff (exE d) =
      (AddMonoidAlgebra.single (0 : ℤ) (coordS a) : AddMonoidAlgebra R ℤ).coeff (exE d) := by rw [h']
  rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne] at h2
  exact h2

end Affine

/-- A point `y = a ≫ ι` of `ℙ¹` which is fixed by `G_m` is `0` or `∞`: the coordinate of `a` is `0`. -/
theorem eq_mkPt_zero_of_fixed {d : Bool} (a : T ⟶ AZ (exFam.N d))
    (hfix : ∀ {T' : Scheme.{0}} (s : T' ⟶ T) (k : APt Scheme.Γ ℤ (op T')),
      exFam.smulN k (s ≫ a ≫ exFam.ι d) = s ≫ a ≫ exFam.ι d) :
    a = mkPt d 0 := by
  refine T.affineOpenCover.openCover.hom_ext _ _ fun j => ?_
  let R := T.affineOpenCover.X j
  let f : Spec R ⟶ T := T.affineOpenCover.f j
  change f ≫ a = f ≫ mkPt d 0
  have hcoord : coordS (f ≫ a) = 0 := by
    apply coordS_eq_zero_of_fixed
    have h := hfix (Spec.map (laurentC R) ≫ f) (charS (tChar R))
    have e1 : (Spec.map (laurentC R) ≫ f) ≫ a ≫ exFam.ι d =
        (Spec.map (laurentC R) ≫ f ≫ a) ≫ exFam.ι d := by simp
    rw [e1, exFam.smulN_comp_ι] at h
    exact (cancel_mono (exFam.ι d)).mp h
  apply coordS_inj
  rw [hcoord]
  have e2 : exCoord (f ≫ mkPt d 0) = 0 := by
    rw [exCoord_comp, exCoord_mkPt]
    exact map_zero _
  exact ((congrArg (Scheme.ΓSpecIso R).hom.hom e2).trans (map_zero _)).symm

end

end AlgMag.XP

#print axioms AlgMag.XP.eq_mkPt_zero_of_fixed
