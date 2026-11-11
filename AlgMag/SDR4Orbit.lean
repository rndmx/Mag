/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Alg

/-!
# Lemma D, final bridge: the closed orbit `Spec κ'[L]` in coordinates

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 1-2. The map
`ω : O(V')[L] → κ'[Γ]`, the orbit point read on `O(T)[P]`, and the invariance of the kernel of a point fixed by the
action.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Omega

variable {Γ' F₀ κ : Type u} [AddCommGroup Γ'] [CommRing F₀] [CommRing κ] (L : AddSubgroup Γ') (E : F₀ →+* κ)

/-- `SDR3Orbit_OM L → Γ`. -/
def SDR4_omι : SDR3Orbit_OM L →+ Γ' := (AddMonoidHom.snd PUnit.{u + 1} Γ').comp (SDR3Orbit_OM L).subtype

lemma SDR4_omι_inj : Function.Injective (SDR4_omι L) := by
  rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩ h
  exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)

lemma SDR4_omι_mem (x : SDR3Orbit_OM L) : SDR4_omι L x ∈ L := by
  obtain ⟨⟨a, y⟩, hy⟩ := x
  have := mem_Pt.1 hy
  exact (QuotientAddGroup.eq_zero_iff y).1 this.symm

lemma SDR4_omι_om {d : Γ'} (hd : d ∈ L) : SDR4_omι L (SDR3Orbit_om L hd) = d := rfl

/-- `ω : F₀[L] → κ[Γ]`. -/
noncomputable def SDR4_ω : AddMonoidAlgebra F₀ (SDR3Orbit_OM L) →+* AddMonoidAlgebra κ Γ' :=
  (AddMonoidAlgebra.mapDomainRingHom κ (SDR4_omι L)).comp (AddMonoidAlgebra.mapRingHom _ E)

lemma SDR4_ω_single (x : SDR3Orbit_OM L) (y : F₀) :
    SDR4_ω L E (AddMonoidAlgebra.single x y) = AddMonoidAlgebra.single (SDR4_omι L x) (E y) := by
  simp [SDR4_ω]

lemma SDR4_ω_inj (hE : Function.Injective E) : Function.Injective (SDR4_ω L E) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro a ha
  ext x
  have h := congrArg (fun z => z.coeff (SDR4_omι L x)) ha
  have e : ∀ a : AddMonoidAlgebra F₀ (SDR3Orbit_OM L),
      (SDR4_ω L E a).coeff (SDR4_omι L x) = E (a.coeff x) := by
    intro a
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | single m c =>
      rw [SDR4_ω_single]
      by_cases hm : m = x
      · subst hm; simp
      · have : SDR4_omι L m ≠ SDR4_omι L x := fun h => hm (SDR4_omι_inj L h)
        simp [hm, this]
  have h' : E (a.coeff x) = 0 := (e a).symm.trans h
  simpa using hE (h'.trans (map_zero E).symm)

end Omega

section Coords

/-- A point of `𝔸(P)`, with values in `Γ(U, O)`. -/
def SDR4_cast {P : Type u} [AddCommMonoid P] {U : BigFppfOver B S hS} (a : APt (fppfO B S hS) P (op U)) :
    Multiplicative P →* Γ((SCH).obj U, ⊤) := a

variable (P : Type u) [AddCommMonoid P] [Countable P] (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]

/-- `Γ(𝔸(P)_V) → O(V)[P]`. -/
noncomputable def SDR4_toG : Γ((SCH).obj (specObj P V), ⊤) →+* gRing P V :=
  (Scheme.ΓSpecIso (.of (gRing P V))).hom.hom

/-- `O(V)[P] → Γ(𝔸(P)_V)`. -/
noncomputable def SDR4_ofG : gRing P V →+* Γ((SCH).obj (specObj P V), ⊤) :=
  (Scheme.ΓSpecIso (.of (gRing P V))).inv.hom

lemma SDR4_toG_ofG (x : gRing P V) : SDR4_toG P V (SDR4_ofG P V x) = x := SDR4_iso_app _ x

lemma SDR4_ofG_toG (x : Γ((SCH).obj (specObj P V), ⊤)) : SDR4_ofG P V (SDR4_toG P V x) = x := SDR4_iso_app' _ x

lemma SDR4_pr_eq (y : Γ((SCH).obj V, ⊤)) :
    ((SCH).map (specPr P V)).appTop.hom y = SDR4_ofG P V (AddMonoidAlgebra.single 0 y) :=
  specPrS_appTop (P := P) V y

lemma SDR4_toG_pr (y : Γ((SCH).obj V, ⊤)) :
    SDR4_toG P V (((SCH).map (specPr P V)).appTop.hom y) = AddMonoidAlgebra.single 0 y := by
  rw [SDR4_pr_eq, SDR4_toG_ofG]

lemma SDR4_toG_pt (x : P) :
    SDR4_toG P V (SDR4_cast (specPt P V) (Multiplicative.ofAdd x)) = AddMonoidAlgebra.single x 1 :=
  SDR4_iso_app _ _

variable {P V}

lemma SDR4_app_comp {X₁ X₂ X₃ : BigFppfOver B S hS} (f : X₁ ⟶ X₂) (k : X₂ ⟶ X₃) (y : Γ((SCH).obj X₃, ⊤)) :
    ((SCH).map (f ≫ k)).appTop.hom y = ((SCH).map f).appTop.hom (((SCH).map k).appTop.hom y) :=
  (SDR3Coact_app (f := (SCH).map f) (k := (SCH).map k) (h := (SCH).map (f ≫ k)) (Functor.map_comp _ _ _).symm y).symm

end Coords

section Formula

variable {Γ' κ P : Type u} [AddCommGroup Γ'] [Countable Γ'] [AddGroup.FG Γ'] [Field κ] [AddCommMonoid P] [Countable P]
  (L : AddSubgroup Γ') (δ : P →+ Γ') {V' T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (t' : V' ⟶ T) (c' : APt (fppfO B S hS) P (op V'))
  (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c' p = 0)

open Classical in
/-- The orbit point on a monomial. -/
lemma SDR4_toG_specRing (n : P) (x : Γ((SCH).obj T, ⊤)) :
    SDR4_toG _ V' (specRing (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL) (AddMonoidAlgebra.single n x)) =
      if h : δ n ∈ L then AddMonoidAlgebra.single (SDR3Orbit_om L h)
        (((SCH).map t').appTop.hom x * SDR4_cast c' (Multiplicative.ofAdd n)) else 0 := by
  refine (congrArg (SDR4_toG _ V') (specRing_single _ _ n x)).trans ((map_mul (SDR4_toG _ V') _ _).trans ?_)
  have e1 : SDR4_toG _ V' (((SCH).map (specPr (SDR3Orbit_OM L) V' ≫ t')).appTop.hom x) =
      AddMonoidAlgebra.single 0 (((SCH).map t').appTop.hom x) := by
    rw [SDR4_app_comp, SDR4_toG_pr]
  rw [e1]
  change _ * SDR4_toG _ V' (SDR4_cast (SDR3Orbit_c₀ L δ c' hL) (Multiplicative.ofAdd n)) = _
  split_ifs with h
  · have e2 : SDR4_cast (SDR3Orbit_c₀ L δ c' hL) (Multiplicative.ofAdd n) =
        ((SCH).map (specPr (SDR3Orbit_OM L) V')).appTop.hom (SDR4_cast c' (Multiplicative.ofAdd n)) *
          SDR4_cast (specPt (SDR3Orbit_OM L) V') (Multiplicative.ofAdd (SDR3Orbit_om L h)) :=
      SDR3Orbit_c₀_pos L δ c' hL _ h
    rw [e2, map_mul, SDR4_toG_pr, SDR4_toG_pt, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single,
      zero_add, zero_add, mul_one]
  · have e2 : SDR4_cast (SDR3Orbit_c₀ L δ c' hL) (Multiplicative.ofAdd n) = 0 := SDR3Orbit_c₀_neg L δ c' hL _ h
    rw [e2, map_zero, mul_zero]

/-- The orbit point on `O(T)[P]`. -/
theorem SDR4_formula (E : Γ((SCH).obj V', ⊤) →+* κ) (φA : gRing P T →+* κ)
    (hmono : ∀ n : P, E (SDR4_cast c' (Multiplicative.ofAdd n)) = φA (AddMonoidAlgebra.single n 1))
    (ht : ∀ x, E (((SCH).map t').appTop.hom x) = φA (AddMonoidAlgebra.single 0 x))
    (a : gRing P T) :
    SDR4_ω L E (SDR4_toG _ V' (specRing (specPr (SDR3Orbit_OM L) V' ≫ t') (SDR3Orbit_c₀ L δ c' hL) a)) =
      AddMonoidAlgebra.mapRingHom Γ' φA ((monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ a) := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, map_add, ha, hb]
  | single n x =>
    have hσ : (monCoact (R := Γ((SCH).obj T, ⊤)) δ).σ (AddMonoidAlgebra.single n x) =
        AddMonoidAlgebra.single (δ n) (AddMonoidAlgebra.single n x) := monσ_single _ _ _
    have hsp : (AddMonoidAlgebra.single n x : gRing P T) =
        AddMonoidAlgebra.single 0 x * AddMonoidAlgebra.single n 1 := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    have hφ : φA (AddMonoidAlgebra.single n x) =
        E (((SCH).map t').appTop.hom x) * E (SDR4_cast c' (Multiplicative.ofAdd n)) := by
      rw [hsp, map_mul, ht, hmono]
    rw [hσ, SDR4_toG_specRing, AddMonoidAlgebra.mapRingHom_single, hφ]
    split_ifs with h
    · rw [SDR4_ω_single, map_mul]
      rfl
    · have e4 : SDR4_cast c' (Multiplicative.ofAdd n) = 0 := hL _ h
      rw [e4, map_zero, map_zero, mul_zero, AddMonoidAlgebra.single_zero]

end Formula

section Kernel

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] {Vo W₀ Orb : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)] [IsAffine ((BigFppfOver.toScheme B S hS).obj Orb)]

/-- The universal character and the projection compute `Γ(𝔸(Λ)_Orb) = Γ(Orb)[Λ]`. -/
lemma SDR4_lift_spec {F₁ : Type u} [CommRing F₁] (ζ : F₁ →+* Γ((SCH).obj Orb, ⊤)) (a : AddMonoidAlgebra F₁ Λ) :
    SDR3Coact_lift (((SCH).map (specPr Λ Orb)).appTop.hom.comp ζ) (SDR4_cast (specPt Λ Orb)) a =
      SDR4_ofG Λ Orb (AddMonoidAlgebra.mapRingHom Λ ζ a) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single d x =>
    rw [SDR3Coact_lift_single, AddMonoidAlgebra.mapRingHom_single]
    have e1 : (AddMonoidAlgebra.single d (ζ x) : gRing Λ Orb) =
        AddMonoidAlgebra.single 0 (ζ x) * AddMonoidAlgebra.single d 1 := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [e1, map_mul, RingHom.comp_apply, SDR4_pr_eq]
    rfl

/-- If a map `so : Orb → Vo` commutes with the action up to `m` on `𝔸(Λ)_Orb`, the kernel of `so^*` is homogeneous. -/
theorem SDR4_ker_hom (actV : AAction (fppfO B S hS) Λ (yoneda.obj Vo)) (r : Vo ⟶ W₀) {c : Coact Γ((SCH).obj Vo, ⊤) Λ}
    (hc : ∀ y, SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) (c.σ y) =
      ((SCH).map (SDR3Coact_a actV r)).appTop.hom y) (so : Orb ⟶ Vo) (m : specObj Λ Orb ⟶ Orb)
    (hm : m ≫ so = actV.smul (U := op (specObj Λ Orb)) (specPt Λ Orb) (specPr Λ Orb ≫ so))
    (z : Γ((SCH).obj Vo, ⊤)) (hz : ((SCH).map so).appTop.hom z = 0) (d : Λ) :
    ((SCH).map so).appTop.hom (c.comp d z) = 0 := by
  have h1 : ((SCH).map (actV.smul (U := op (specObj Λ Orb)) (specPt Λ Orb) (specPr Λ Orb ≫ so))).appTop.hom z =
      SDR3Coact_lift ((SCH).map (specPr Λ Orb ≫ so)).appTop.hom (SDR4_cast (specPt Λ Orb)) (c.σ z) :=
    SDR4_smul_apply actV r hc (specPr Λ Orb ≫ so) (specPt Λ Orb) z
  rw [← hm, SDR4_app_comp, hz, map_zero] at h1
  have e : ((SCH).map (specPr Λ Orb ≫ so)).appTop.hom =
      ((SCH).map (specPr Λ Orb)).appTop.hom.comp ((SCH).map so).appTop.hom :=
    RingHom.ext fun y => SDR4_app_comp _ _ y
  rw [e, SDR4_lift_spec] at h1
  have h4 := congrArg (SDR4_toG Λ Orb) h1
  rw [map_zero, SDR4_toG_ofG] at h4
  have h5 := congrArg (fun y => y.coeff d) h4
  simp only [AddMonoidAlgebra.coeff_mapRingHom] at h5
  exact h5.symm

end Kernel

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_formula
#print axioms AlgMag.SD.SDR4_ker_hom
