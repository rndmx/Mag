/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FixesFact26
import AlgMag.Sec3Leftover2F

/-!
# Algebraic Magnetism, Fact 2.6 (ii): the bialgebra of `𝔸(N)_B` on charts

For a chart `V → B`, the base change of `𝔸(N)_B → B` to `V` is `𝔸(N)_V`, so Fact 2.6 (i) with `S := V`
gives the bialgebra `𝒪_V[N]` on `V`. These identifications are compatible with morphisms of charts and
with the multiplication of `𝔸(N)_S`.

* `AlgMag.GB.unitA_eq_one`: `unitA` is the unit of the monoid object `𝔸(N)_S`.
* `AlgMag.GB.isPullback_baseA`: `𝔸(N)_V = 𝔸(N)_S ×_S V`.
* `AlgMag.GB.chart_iso`: any base change of `𝔸(N)_S` to `V` is `𝔸(N)_V`.
* `AlgMag.GB.baseHom_mul`: the map `𝔸(N)_V → 𝔸(N)_S` respects the multiplications.
* `AlgMag.GB.evalU_baseA`: `𝒪_V(U)[N] → q_* 𝒪` is natural in `V`.
* `AlgMag.OverB.fact26_ii_chart`: the statement on charts of `B`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory TopologicalSpace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

noncomputable section

namespace AlgMag.GB

variable (N : Type u) [AddCommMonoid N]

lemma isPullback_A (S : Scheme.{u}) :
    IsPullback (toAZ N S) (A N S).hom (terminal.from (AZ N)) (terminal.from S) :=
  (IsPullback.of_hasPullback (terminal.from S) (terminal.from (AZ N))).flip

/-- `unitA` is the unit of the monoid object `𝔸(N)_S`, as used in Fact 2.6 (i). -/
theorem unitA_eq_one (S : Scheme.{u}) : (monObjA N S).one = unitA N S := rfl

variable {S V : Scheme.{u}} (v : V ⟶ S)

/-- The map `𝔸(N)_V → 𝔸(N)_S` over `v`. -/
def baseA : (A N V).left ⟶ (A N S).left :=
  (isPullback_A N S).lift (toAZ N V) ((A N V).hom ≫ v) (terminal.hom_ext _ _)

lemma baseA_toAZ : baseA N v ≫ toAZ N S = toAZ N V := (isPullback_A N S).lift_fst _ _ _

lemma baseA_hom : baseA N v ≫ (A N S).hom = (A N V).hom ≫ v := (isPullback_A N S).lift_snd _ _ _

/-- **Fact 2.6 (ii)**, base change: `𝔸(N)_V = 𝔸(N)_S ×_S V`. -/
theorem isPullback_baseA : IsPullback (baseA N v) (A N V).hom (A N S).hom v := by
  refine IsPullback.of_right (h₁₂ := toAZ N S) (h₂₂ := terminal.from S)
    (v₁₃ := terminal.from (AZ N)) ?_ (baseA_hom N v) (isPullback_A N S)
  rw [baseA_toAZ, show v ≫ terminal.from S = terminal.from V from terminal.hom_ext _ _]
  exact isPullback_A N V

/-- Any base change `W → V` of `𝔸(N)_S → S` along `v` is `𝔸(N)_V`, over `V` and over `𝔸(N)_S`. -/
theorem chart_iso {W : Scheme.{u}} {k : W ⟶ V} {q : W ⟶ (A N S).left}
    (hP : IsPullback q k (A N S).hom v) :
    ∃ φ : W ≅ (A N V).left, φ.hom ≫ (A N V).hom = k ∧ φ.hom ≫ baseA N v = q :=
  ⟨hP.isoIsPullback _ _ (isPullback_baseA N v), IsPullback.isoIsPullback_hom_snd _ _ _ _,
    IsPullback.isoIsPullback_hom_fst _ _ _ _⟩

/-- A scheme over `V`, as a scheme over `S`. -/
abbrev toS (T : Over V) : Over S := Over.mk (T.hom ≫ v)

/-- A point of `𝔸(N)_V`, as a point of `𝔸(N)_S`. -/
def baseHom {T : Over V} (x : T ⟶ A N V) : toS v T ⟶ A N S :=
  Over.homMk (x.left ≫ baseA N v) (by
    change (x.left ≫ baseA N v) ≫ (A N S).hom = T.hom ≫ v
    rw [Category.assoc, baseA_hom, ← Category.assoc, Over.w x])

lemma pts_baseHom {T : Over V} (x : T ⟶ A N V) : pts (toS v T) (baseHom N v x) = pts T x := by
  change ptsZ T.left ((x.left ≫ baseA N v) ≫ toAZ N S) = ptsZ T.left (x.left ≫ toAZ N V)
  rw [Category.assoc, baseA_toAZ]

/-- **Fact 2.6 (ii)**, the comultiplication: `𝔸(N)_V → 𝔸(N)_S` respects the multiplications. -/
theorem baseHom_mul {T : Over V} (x y : T ⟶ A N V) :
    baseHom N v (CartesianMonoidalCategory.lift x y ≫ mul N V) =
      CartesianMonoidalCategory.lift (baseHom N v x) (baseHom N v y) ≫ mul N S := by
  apply (pts (toS v T)).injective
  rw [pts_mul, pts_baseHom, pts_baseHom, pts_baseHom, pts_mul]
  rfl

variable {N}

lemma preimage_baseA (U : S.Opens) :
    (A N V).hom ⁻¹ᵁ (v ⁻¹ᵁ U) ≤ baseA N v ⁻¹ᵁ ((A N S).hom ⁻¹ᵁ U) := by
  intro p hp
  change ((baseA N v ≫ (A N S).hom) p) ∈ U
  rw [baseA_hom]
  exact hp

/-- **Fact 2.6 (ii)**, compatibility of charts: the maps `𝒪_V(U)[N] → q_* 𝒪` of Fact 2.6 (i) are natural in
`V`: for `v : V → S` and `U ⊆ S` open, restricting `𝒪_S(U)[N]` to `𝒪_V(v⁻¹ U)[N]` and evaluating
agrees with evaluating and pulling back along `𝔸(N)_V → 𝔸(N)_S`. -/
theorem evalU_baseA (U : S.Opens) :
    ((baseA N v).appLE _ _ (preimage_baseA v U)).hom.comp (evalU N (A N S) (univ N S) U) =
      (evalU N (A N V) (univ N V) (v ⁻¹ᵁ U)).comp (AddMonoidAlgebra.mapRingHom N (v.app U).hom) := by
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
  · simp only [RingHom.comp_apply, evalU_single_zero, AddMonoidAlgebra.mapRingHom_single]
    have h : (A N S).hom.app U ≫ (baseA N v).appLE _ _ (preimage_baseA v U) =
        v.app U ≫ (A N V).hom.app (v ⁻¹ᵁ U) := by
      rw [Scheme.Hom.app_eq_appLE (f := (A N S).hom), Scheme.Hom.app_eq_appLE (f := (A N V).hom),
        Scheme.Hom.app_eq_appLE (f := v), Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr (baseA_hom N v) _ _ _ _
    exact congrArg (fun k => k.hom r) h
  · simp only [RingHom.comp_apply, evalU_single_one, AddMonoidAlgebra.mapRingHom_single, map_one]
    have hp : pts (A N V) (𝟙 _) (Multiplicative.ofAdd n) =
        (baseA N v).appTop.hom (pts (A N S) (𝟙 _) (Multiplicative.ofAdd n)) := by
      change ptsZ _ (Over.Hom.left (𝟙 (A N V)) ≫ toAZ N V) _ = _
      rw [Over.id_left, Category.id_comp, ← baseA_toAZ, ptsZ_comp]
      change _ = (baseA N v).appTop.hom (ptsZ _ (Over.Hom.left (𝟙 (A N S)) ≫ toAZ N S) _)
      rw [Over.id_left, Category.id_comp]
      rfl
    change ((baseA N v).appLE _ _ (preimage_baseA v U)).hom
      (((A N S).left.presheaf.map (homOfLE le_top).op).hom _) =
      ((A N V).left.presheaf.map (homOfLE le_top).op).hom (pts (A N V) (𝟙 _) _)
    rw [hp]
    have h : (A N S).left.presheaf.map (homOfLE le_top).op ≫
          (baseA N v).appLE _ _ (preimage_baseA v U) =
        (baseA N v).appTop ≫ (A N V).left.presheaf.map (homOfLE le_top).op := by
      have ht : (baseA N v).appTop = (baseA N v).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
      rw [ht, Scheme.Hom.map_appLE]
      exact (Scheme.Hom.appLE_map _ _ _).symm
    exact congrArg (fun k => k.hom (pts (A N S) (𝟙 _) (Multiplicative.ofAdd n))) h

end AlgMag.GB

namespace AlgMag.OverB

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (Bs : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (N : Type u) [AddCommMonoid N] (hN : B.Contains (GB.A N S).left)

local notation "SCH" => BigFppfOver.toScheme B S hS

include hN in
/-- **Fact 2.6 (ii)**, on charts: for `V → B`, `V` a scheme of the site, the base change of `𝔸(N)_B → B` to
`V` is `𝔸(N)_V`, as schemes over `V`. So by Fact 2.6 (i) with `S := V` its bialgebra is `𝒪_V[N]`. -/
theorem fact26_ii_chart (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ Bs) :
    ∃ (W : BigFppfOver B S hS) (k : W ⟶ V) (w : yoneda.obj W ⟶ AB Bs N)
      (φ : (SCH).obj W ≅ (GB.A N ((SCH).obj V)).left),
      IsPullback w (yoneda.map k) (pr Bs N) v ∧
        φ.hom ≫ (GB.A N ((SCH).obj V)).hom = (SCH).map k := by
  let c : V ⟶ T0 B S hS := Over.homMk V.hom (by simp)
  have ec : v ≫ toT0 Bs = yoneda.map c := by
    refine NatTrans.ext (funext fun U => ?_)
    refine ConcreteCategory.hom_ext _ _ fun x => hom_T0_ext _ _
  have sq := IsPullback.of_hasPullback c (strS hN)
  have sqY := sq.map (yoneda (C := BigFppfOver B S hS))
  have R := isPullback_AB Bs N hN
  let w : yoneda.obj (pullback c (strS hN)) ⟶ AB Bs N :=
    R.lift (yoneda.map (pullback.fst c (strS hN)) ≫ v) (yoneda.map (pullback.snd c (strS hN))) (by
      rw [Category.assoc, ec, ← Functor.map_comp, ← Functor.map_comp, pullback.condition])
  have hw1 : w ≫ pr Bs N = yoneda.map (pullback.fst c (strS hN)) ≫ v := R.lift_fst _ _ _
  have hw2 : w ≫ prY Bs hN = yoneda.map (pullback.snd c (strS hN)) := R.lift_snd _ _ _
  have hP : IsPullback ((SCH).map (pullback.snd c (strS hN))) ((SCH).map (pullback.fst c (strS hN)))
      (GB.A N S).hom ((SCH).map c) := (sq.map (SCH)).flip
  obtain ⟨φ, h1, -⟩ := GB.chart_iso N ((SCH).map c) hP
  refine ⟨pullback c (strS hN), pullback.fst _ _, w, φ, ?_, h1⟩
  refine IsPullback.of_right (h₁₂ := prY Bs hN) (h₂₂ := toT0 Bs) (v₁₃ := yoneda.map (strS hN))
    ?_ hw1 R.flip
  rw [hw2, ec]
  exact sqY.flip

end AlgMag.OverB

#print axioms AlgMag.GB.unitA_eq_one
#print axioms AlgMag.GB.isPullback_baseA
#print axioms AlgMag.GB.chart_iso
#print axioms AlgMag.GB.baseHom_mul
#print axioms AlgMag.GB.evalU_baseA
#print axioms AlgMag.OverB.fact26_ii_chart
