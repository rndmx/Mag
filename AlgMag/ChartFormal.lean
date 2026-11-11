/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartMain
import AlgMag.ChartS5Spec

/-!
# From the tower of §2 to `Spec C → X` (§§3–4 of the chart-lemma proof)

The object `Spec C` of the site, for `C` the graded completion of an affine tower, its action, and
the ring maps `Γ(X_n) → Γ(V(mⁿ))`. The maps to `X` and the application of Theorem 4.1 are not done.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace AlgMag.ChartAssembly

open ChartMain ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M] [IsAffine S]

local notation "SCH" => BigFppfOver.toScheme B S hS
local notation "TOP" => siteTop (B := B) (S := S) (hS := hS)

/-- The structure map from `S` is in degree `0`. -/
theorem toTop_mem_homog_zero {T : BigFppfOver B S hS} [IsAffine ((SCH).obj T)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (a : RT TOP) :
    ((SCH).map (toTop' T)).appTop.hom a ∈ homog actT 0 := by
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

/-- For `v : V → Spec R'` over `S`, the image of `ρ s`. -/
lemma rSec_structure {R' : Type u} [CommRing R'] (ρ : RT TOP →+* R') (hC : B.Contains (Spec (.of R')))
    {V : BigFppfOver B S hS} (v : V ⟶ rObj ρ hC) (s : RT TOP) :
    ((SCH).map v).appTop.hom (rSec ρ hC (ρ s)) = ((SCH).map (toTop' V)).appTop.hom s := by
  have e2 : rSec ρ hC (ρ s) = ((SCH).map (spToT _ ρ hC)).appTop.hom s :=
    (spToT_appTop _ ρ hC s).symm
  have e3 : v ≫ spToT _ ρ hC = toTop' V := Over.mkIdTerminal.hom_ext _ _
  rw [e2, ← e3, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

variable (Y : AffineTower B S hS M)

lemma toTop_compat (a : RT TOP) (n : ℕ) :
    ((SCH).map (Y.j n)).appTop.hom (((SCH).map (toTop' (Y.U (n + 1)))).appTop.hom a) =
      ((SCH).map (toTop' (Y.U n))).appTop.hom a := by
  have e : (SCH).map (Y.j n) ≫ (SCH).map (toTop' (Y.U (n + 1))) = (SCH).map (toTop' (Y.U n)) := by
    rw [← Functor.map_comp]
    exact congrArg _ (Over.mkIdTerminal.hom_ext _ _)
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

/-- `Γ(S) → C`. -/
noncomputable def rhoC : RT TOP →+* Y.toThickeningSystem.C where
  toFun a := ⟨fun n => ((SCH).map (toTop' (Y.U n))).appTop.hom a,
    ChartGraded.glim_le_gL _ _ 0 ⟨fun n => toTop_compat Y a n,
      fun n => toTop_mem_homog_zero (Y.act n) a⟩⟩
  map_one' := Subtype.ext (funext fun n => map_one _)
  map_mul' a b := Subtype.ext (funext fun n => map_mul _ a b)
  map_zero' := Subtype.ext (funext fun n => map_zero _)
  map_add' a b := Subtype.ext (funext fun n => map_add _ a b)

theorem rhoC_mem (a : RT TOP) : rhoC Y a ∈ Y.toThickeningSystem.𝒞 0 :=
  ⟨fun n => toTop_compat Y a n, fun n => toTop_mem_homog_zero (Y.act n) a⟩

/-- `Spec C` is in the site. -/
theorem contains_specC : B.Contains (Spec (.of Y.toThickeningSystem.C)) := by
  have hs : ∀ n, Cardinal.mk (RT (Y.U n)) < B.cutoff := fun n =>
    (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩).trans_lt (Y.U n).left.2
  have hsup : (⨆ n, Cardinal.mk (RT (Y.U n))) < B.cutoff :=
    Cardinal.lift_iSup_lt_of_lt_cof_ord (by simpa using B.aleph0_lt_cutoff_cof) hs
  have ht : max (⨆ n, Cardinal.mk (RT (Y.U n))) Cardinal.aleph0 < B.cutoff :=
    max_lt hsup B.aleph0_lt_cutoff
  set t := max (⨆ n, Cardinal.mk (RT (Y.U n))) Cardinal.aleph0 with htd
  have hc : Cardinal.mk Y.toThickeningSystem.C ≤ (2 : Cardinal) ^ t := by
    have h1 : Cardinal.mk Y.toThickeningSystem.C ≤ Cardinal.mk (∀ n, RT (Y.U n)) :=
      Cardinal.mk_subtype_le _
    refine h1.trans ?_
    have hinf : Cardinal.aleph0 ≤ t := le_max_right _ _
    have hb : ∀ n, Cardinal.mk (RT (Y.U n)) ≤ t := fun n =>
      (le_ciSup (Cardinal.bddAbove_of_small) n).trans (le_max_left _ _)
    calc Cardinal.mk (∀ n, RT (Y.U n)) = Cardinal.prod (fun n => Cardinal.mk (RT (Y.U n))) := by
          simp [Cardinal.mk_pi]
      _ ≤ Cardinal.prod (fun _ : ℕ => t) := Cardinal.prod_le_prod _ _ hb
      _ = t ^ Cardinal.aleph0 := by
          conv_lhs => rw [← Cardinal.mk_out t]
          rw [Cardinal.prod_const]
          simp
      _ ≤ ((2 : Cardinal) ^ t) ^ Cardinal.aleph0 :=
          Cardinal.power_le_power_right (Cardinal.cantor t).le
      _ = (2 : Cardinal) ^ t := by rw [← Cardinal.power_mul, Cardinal.mul_aleph0_eq hinf]
  have h2t : (2 : Cardinal) ^ t < B.cutoff := B.cutoff_isStrongPrelimit ht
  show (Spec _).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hc.trans_lt h2t)

/-- `T = Spec C`. -/
noncomputable abbrev Tob : BigFppfOver B S hS := rObj (rhoC Y) (contains_specC Y)

/-- The action on `Spec C`. -/
noncomputable def actTob : AAction (fppfO B S hS) M (yoneda.obj (Tob Y)) :=
  rAct (rhoC Y) (contains_specC Y) Y.toThickeningSystem.𝒞 (rhoC_mem Y)

/-- The ideal of `O` in `Spec C`. -/
noncomputable abbrev mTob : Ideal Γ((SCH).obj (Tob Y), ⊤) :=
  Y.toThickeningSystem.m.map (rSec (rhoC Y) (contains_specC Y)).toRingHom

/-- `Γ(T) → Γ(V(mⁿ))`, on `C`. -/
noncomputable abbrev gTrunc (n : ℕ) :
    Y.toThickeningSystem.C →+* Γ((SCH).obj (Chart.immObj (Tob Y)
      (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n))), ⊤) :=
  (((SCH).map (Chart.immι (Tob Y) (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n)))).appTop.hom).comp
    (rSec (rhoC Y) (contains_specC Y)).toRingHom

lemma gTrunc_ker (hK : ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1))
    (n : ℕ) : ∀ u ∈ RingHom.ker (Y.toThickeningSystem.ev n), gTrunc Y n u = 0 := by
  intro u hu
  rw [hK n] at hu
  have h1 : (rSec (rhoC Y) (contains_specC Y)).toRingHom u ∈ mTob Y ^ n := by
    rw [mTob, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) hu)
  exact closedι_appTop_of_mem _ h1

/-- `Γ(X_n) → Γ(V(mⁿ))`. -/
noncomputable def aRing (hK : ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1))
    (n : ℕ) : RT (Y.U n) →+* Γ((SCH).obj (Chart.immObj (Tob Y)
      (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n))), ⊤) :=
  (Y.toThickeningSystem.ev n).liftOfSurjective (Y.toThickeningSystem.ev_surj n)
    ⟨gTrunc Y n, fun u hu => gTrunc_ker Y hK n u hu⟩

lemma aRing_ev (hK : ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1))
    (n : ℕ) (u : Y.toThickeningSystem.C) :
    aRing Y hK n (Y.toThickeningSystem.ev n u) = gTrunc Y n u :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ u

lemma hom_appTop (V : BigFppfOver B S hS) (s : RT TOP) :
    (V.hom.hom).appTop.hom s = ((SCH).map (toTop' V)).appTop.hom s := by
  have e : (SCH).map (toTop' V) ≫ 𝟙 S = V.hom.hom := congrArg (fun z => z.hom) (Over.w (toTop' V))
  exact congrArg (fun z => z.appTop.hom s) (e.symm.trans (Category.comp_id _))

variable (hK : ∀ n, RingHom.ker (Y.toThickeningSystem.ev n) = Y.toThickeningSystem.m ^ (n + 1))

lemma ev_rhoC (n : ℕ) (s : RT TOP) :
    Y.toThickeningSystem.ev n (rhoC Y s) = ((SCH).map (toTop' (Y.U n))).appTop.hom s := rfl

lemma gTrunc_rhoC (n : ℕ) (s : RT TOP) :
    gTrunc Y n (rhoC Y s) = ((SCH).map (toTop' (Chart.immObj (Tob Y)
      (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n))))).appTop.hom s :=
  rSec_structure (rhoC Y) (contains_specC Y)
    (Chart.immι (Tob Y) (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n))) s

lemma aRing_structure (n : ℕ) (s : RT TOP) :
    aRing Y hK n (((SCH).map (toTop' (Y.U n))).appTop.hom s) =
      ((SCH).map (toTop' (Chart.immObj (Tob Y)
        (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n))))).appTop.hom s := by
  rw [← ev_rhoC, aRing_ev, gTrunc_rhoC]

/-- `V(mⁿ) → X_n`. -/
noncomputable def aMap (n : ℕ) : Chart.immObj (Tob Y)
    (Chart.closedι ((SCH).obj (Tob Y)) (mTob Y ^ n)) ⟶ Y.U n :=
  haveI : IsAffine (B.obj hS).obj := ‹IsAffine S›
  siteHom (toAffine (aRing Y hK n)) (toAffine_comp _ _ _ (RingHom.ext fun s =>
    (congrArg (aRing Y hK n) (hom_appTop (Y.U n) s)).trans
      ((aRing_structure Y hK n s).trans (hom_appTop _ s).symm)))

end AlgMag.ChartAssembly
