/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedInt

/-!
# The two computations of the coefficient at `0`

Mayeux, *Algebraic Magnetism*, Proposition 9.13 for `L`: `∫` commutes with the action of the first
variable, and `∫` of `x(m, m)` or `x(0, m)` is the coefficient at `0` of `x`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {M : Type u} [AddCommGroup M]
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
  (hρφ : (mr M φ).comp ρ = ρ₀.comp φ)
variable {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y}
variable (ay : AbsAct M Y) (az : AbsAct M Z)
  (hf : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    ay.smul h x ≫ f = az.smul h (x ≫ f))
  (ha : IsEq ay ρ₀ a)
variable {P : Type u} [AddCommGroup P]

section Equiv

/-- The ring-level identity for the action of the first variable. -/
lemma cur_sig {W : Type u} [CommRing W] (ϱ : W →+* AddMonoidAlgebra W M) (g : M →+ P) :
    (cur W P M).comp (sig ϱ ((ι₁ P M).comp g)) = (mr M (sig ϱ g)).comp (cur W P M) := by
  have hc : (cur W P M).comp (md W ((ι₁ P M).comp g)) = (cs _ M).comp (md W g) := by
    refine rh_ext ?_ fun k => ?_
    · rw [RingHom.comp_assoc, md_cs, cur_cs, RingHom.comp_assoc, md_cs]
    · simp only [RingHom.comp_apply]
      rw [md_single, md_single, cur_of]
      rfl
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, sig_cs, ← RingHom.comp_assoc, hc]
    refine RingHom.ext fun x => ?_
    have a1 := RingHom.congr_fun (cur_cs (W := W) (P := P) (M := M)) x
    have a2 := RingHom.congr_fun (sig_cs ϱ g) x
    have a3 := RingHom.congr_fun (mr_cs (P := M) (sig ϱ g)) (cs W P x)
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a3, a2]
  · simp only [RingHom.comp_apply]
    rw [sig_of, cur_of, mr_single, sig_of]

/-- `σ` on `avgRing`. -/
noncomputable def avgSig (g : M →+ P) :
    avgRing (M := M) (ph (A := A) (RingHom.ker φ) P) →+* avgRing (M := M) (ph (A := A) (RingHom.ker φ) P) :=
  avgMap _ _ (sig ρ₀ g) (mr M (sig (ϱN hs hN hq ρ ρ₀ hρφ) g)) (fun p => by
    have e := mr_sig (P := P) (sFst (A := A) (RingHom.ker φ)) (ϱN hs hN hq ρ ρ₀ hρφ) ρ₀
      (fst_ϱN hs hN hq ρ ρ₀ hρφ).symm g
    rw [← RingHom.comp_apply, mr_comp, e, ← mr_comp, RingHom.comp_apply, avg_prop, map_cst])

/-- `∫` commutes with the action of the first variable. -/
theorem L.int_act (g : M →+ P) (x : L f a (RingHom.ker φ) (P × M)) :
    L.int (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha ((ι₁ P M).comp g) x) =
      L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g (L.int x) := by
  let σ := avgSig hs hN hq ρ ρ₀ hρφ (P := P) (-g)
  let ϱ := ϱN hs hN hq ρ ρ₀ hρφ
  let e : Multiplicative M →* avgRing (M := M) (ph (A := A) (RingHom.ker φ) P) :=
    (avgCst _).toMonoidHom.comp (gl1 _ g)
  have hneg : -((ι₁ P M).comp g) = (ι₁ P M).comp (-g) := by exact AddMonoidHom.ext fun m => Prod.ext rfl (by simp [ι₁])
  have key : gI (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha ((ι₁ P M).comp g) x) =
      ay.smul (eG e) (sp σ ≫ gI x) := by
    refine avg_ext ?_ ?_
    · have e₁ : (avgSnd (ph (A := A) (RingHom.ker φ) P)).toMonoidHom.comp e = (cst (AddMonoidAlgebra (Sq A (RingHom.ker φ)) P) M).toMonoidHom.comp (gl1 (Sq A (RingHom.ker φ)) g) := rfl
      have e₂ : (cur (Sq A (RingHom.ker φ)) P M).toMonoidHom.comp (gl1 _ ((ι₁ P M).comp g)) =
          (cst (AddMonoidAlgebra (Sq A (RingHom.ker φ)) P) M).toMonoidHom.comp (gl1 (Sq A (RingHom.ker φ)) g) := by
        refine MonoidHom.ext fun m => ?_
        change cur _ P M (AddMonoidAlgebra.single _ 1) = _
        rw [cur_of]
        rfl
      have e₃ : (avgSnd (ph (A := A) (RingHom.ker φ) P)).comp σ = (mr M (sig ϱ (-g))).comp (avgSnd _) := rfl
      rw [gI_1, L.act_val, Sec10Printed.act, ay.comp, res_eG, e₂, ay.comp, res_eG, e₁]
      congr 1
      have e₄ : sp (avgSnd (ph (A := A) (RingHom.ker φ) P)) ≫ sp σ =
          sp (mr M (sig ϱ (-g))) ≫ sp (avgSnd _) := by rw [← sp_comp, e₃, sp_comp]
      rw [hneg, ← Category.assoc, ← sp_comp, cur_sig]
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ gI x) e₄.symm)
      rw [sp_comp, Category.assoc, Category.assoc, gI_1]
    · have e₁ : (avgFst (ph (A := A) (RingHom.ker φ) P)).toMonoidHom.comp e = gl1 _ g := by
        refine MonoidHom.ext fun m => ?_
        change mr P (sFst _) (AddMonoidAlgebra.single _ 1) = _
        rw [mr_single, map_one]
        rfl
      have e₃ : (avgFst (ph (A := A) (RingHom.ker φ) P)).comp σ = (sig ρ₀ (-g)).comp (avgFst _) := rfl
      rw [gI_2, ay.comp, res_eG]
      have e₄ := act_of_isEq ay ρ₀ a ha g
      rw [Sec10Printed.act] at e₄
      refine e₄.symm.trans ?_
      have e₅ : (gl1 A g : Multiplicative M →* AddMonoidAlgebra A P) =
          (avgFst (ph (A := A) (RingHom.ker φ) P)).toMonoidHom.comp e := e₁.symm
      rw [e₅, ← Category.assoc (sp _) (sp σ), ← sp_comp, e₃, sp_comp, Category.assoc, gI_2]
  refine L.ext' ?_
  have e₁ : (avgInt _ (ph_sq (RingHom.ker φ))).toMonoidHom.comp e = gl1 _ g := by
    refine MonoidHom.ext fun m => ?_
    exact RingHom.congr_fun (avgInt_cst _ (ph_sq (RingHom.ker φ))) _
  have e₂ : (avgInt _ (ph_sq (RingHom.ker φ))).comp σ = (sig ϱ (-g)).comp (avgInt _ (ph_sq (RingHom.ker φ))) := by
    refine RingHom.ext fun t => ?_
    change (mr M (sig ϱ (-g)) (avgSnd _ t)).coeff 0 = sig ϱ (-g) ((avgSnd _ t).coeff 0)
    rw [coeff_mr]
  rw [L.int_val, key, ay.comp, res_eG, e₁, L.act_val, Sec10Printed.act, L.int_val, ← Category.assoc (sp _) (sp σ),
    ← sp_comp, e₂, sp_comp, Category.assoc]

end Equiv

section Eval

variable {N : Type u} [AddCommGroup N] [Module A N]

/-- The pair `(x, a)` over `avgRing` of `A[N] → A`. -/
noncomputable def gI₀ (x : L f a N M) :
    Spec (CommRingCat.of (avgRing (M := M) (sFst (A := A) N))) ⟶ Y :=
  gl (milnor_avg _ sFst_surjective) (avgFst_surjective _ sFst_surjective) x.1 a (by
    have h := x.2.1
    exact h)

lemma gI₀_1 (x : L f a N M) : sp (avgSnd _) ≫ gI₀ x = x.1 := gl_p (milnor_avg _ sFst_surjective) _ _ _ _
lemma gI₀_2 (x : L f a N M) : sp (avgFst _) ≫ gI₀ x = a := gl_q (milnor_avg _ sFst_surjective) _ _ _ _

/-- The coefficient at `0` of `x`, on `Spec A[N]`. -/
noncomputable def co₀ (x : L f a N M) : Spec (CommRingCat.of (Sq A N)) ⟶ Y :=
  sp (avgInt _ (sq_zero_sFst N)) ≫ gI₀ x

lemma coeff_cur_md (h₁ : M →+ M) (w : AddMonoidAlgebra (Sq A N) M) :
    (cur _ M M (md _ (prH h₁) w)).coeff 0 =
      AddMonoidAlgebra.single 0 (w.coeff 0) := by
  classical
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.single_add]
  | single m r =>
    rw [md_single, cur_single]
    by_cases hm : m = 0
    · subst hm
      simp
    · have h₁' : (AddMonoidAlgebra.single (prH h₁ m).2
          (AddMonoidAlgebra.single (prH h₁ m).1 r) :
            AddMonoidAlgebra (AddMonoidAlgebra (Sq A N) M) M).coeff 0 = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hm)
      have h₂ : (AddMonoidAlgebra.single m r : AddMonoidAlgebra (Sq A N) M).coeff 0 = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hm)
      rw [h₁', h₂, AddMonoidAlgebra.single_zero]

/-- `avgRing` to `avgRing`, along `w ↦ cur (h w)`. -/
noncomputable def avgξ (h₁ : M →+ M) :
    avgRing (M := M) (sFst (A := A) N) →+* avgRing (M := M) (ph (A := A) N M) :=
  avgMap _ _ (cs A M) ((cur _ M M).comp (md _ (prH h₁))) (fun p => by
    have e₀ := cur_natural (M := M) (P := M) (sFst (A := A) N)
    have e₁ : mr M (mr M (sFst (A := A) N)) (cur _ M M (md _ (prH h₁) (avgSnd _ p))) =
        cur A M M (mr (M × M) (sFst N) (md _ (prH h₁) (avgSnd _ p))) :=
      RingHom.congr_fun e₀ _
    have e₂ := RingHom.congr_fun (mr_md (sFst (A := A) N) (prH h₁)) (avgSnd _ p)
    simp only [RingHom.comp_apply] at e₂
    have e₃ := avg_prop (sFst (A := A) N) p
    have e₄ := RingHom.congr_fun (md_cs (W := A) (prH h₁)) (avgFst _ p)
    have e₅ := RingHom.congr_fun (cur_cs (W := A) (P := M) (M := M)) (avgFst _ p)
    simp only [RingHom.comp_apply] at e₄ e₅
    rw [RingHom.comp_apply, e₁, e₂, e₃]
    refine (congrArg (cur A M M) ?_).trans e₅
    exact e₄)

/-- `∫ x(h₁ m, m)` is the coefficient at `0` of `x`, constant in the first variable. -/
theorem L.int_eval (h₁ : M →+ M) (x : L f a N M) :
    (L.int (x.mapP (prH h₁))).1 = sp (cs _ M) ≫ co₀ x := by
  have key : gI (x.mapP (prH h₁)) = sp (avgξ h₁) ≫ gI₀ x := by
    refine avg_ext ?_ ?_
    · have e₁ : (avgSnd (ph (A := A) N M)).comp (avgξ (N := N) h₁) =
          ((cur (Sq A N) M M).comp (md (Sq A N) (prH h₁))).comp (avgSnd (M := M) (sFst (A := A) N)) := rfl
      have e₂ : sp (avgSnd (ph (A := A) N M)) ≫ sp (avgξ (N := N) h₁) =
          sp (cur (Sq A N) M M) ≫ sp (md (Sq A N) (prH h₁)) ≫ sp (avgSnd (M := M) (sFst (A := A) N)) := by
        rw [← sp_comp, e₁, sp_comp, sp_comp, Category.assoc]
      refine (gI_1 _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ gI₀ x) e₂.symm)
      rw [L.mapP_val]
      simp only [Category.assoc]
      rw [gI₀_1]
    · have e₁ : (avgFst (ph (A := A) N M)).comp (avgξ (N := N) h₁) = (cs A M).comp (avgFst (M := M) (sFst (A := A) N)) := rfl
      have e₂ : sp (avgFst (ph (A := A) N M)) ≫ sp (avgξ (N := N) h₁) = sp (cs A M) ≫ sp (avgFst (M := M) (sFst (A := A) N)) := by
        rw [← sp_comp, e₁, sp_comp]
      refine (gI_2 _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ gI₀ x) e₂.symm)
      rw [Category.assoc, gI₀_2]
  have e₂ : (avgInt (M := M) (ph (A := A) N M) (ph_sq N)).comp (avgξ (N := N) h₁) =
      (cs (Sq A N) M).comp (avgInt (M := M) (sFst (A := A) N) (sq_zero_sFst N)) := by
    refine RingHom.ext fun t => ?_
    have e₀ : avgSnd (ph (A := A) N M) (avgξ (N := N) h₁ t) = cur (Sq A N) M M (md (Sq A N) (prH h₁) (avgSnd (M := M) (sFst (A := A) N) t)) := rfl
    exact (congrArg (fun z => z.coeff 0) e₀).trans (coeff_cur_md h₁ _)
  have e₃ : sp (avgInt (M := M) (ph (A := A) N M) (ph_sq N)) ≫ sp (avgξ (N := N) h₁) =
      sp (cs (Sq A N) M) ≫ sp (avgInt (M := M) (sFst (A := A) N) (sq_zero_sFst N)) :=
    (sp_comp _ _).symm.trans ((congrArg sp e₂).trans (sp_comp _ _))
  refine (congrArg (sp (avgInt (M := M) (ph (A := A) N M) (ph_sq N)) ≫ ·) key).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ gI₀ x) e₃).trans (Category.assoc _ _ _))

end Eval

end AlgMag.Sec10Printed
