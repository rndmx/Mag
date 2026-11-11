/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR4Chart

/-!
# Lemma D, final bridge: reading the action on `Γ(Z)`

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Steps 2, 3, 9. From the coaction of
`SDR3Coact_main`: the formula for the action on functions, the action on field-valued points (`SDR3Asm_ActsOnPoints`,
with no size condition on the field, through the scheme pullback), degree `0` for invariant maps, and the base change of
an action.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Ring

variable {Λ : Type u} [AddCommGroup Λ]

lemma SDR4_lift_eq_sum {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S') (g : Multiplicative Λ →* S')
    (a : AddMonoidAlgebra R' Λ) :
    SDR3Coact_lift f g a = a.coeff.sum fun d x => g (Multiplicative.ofAdd d) * f x := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, ha, hb, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index' (by simp) (by intros; rw [map_add, mul_add])]
  | single d r =>
    rw [SDR3Coact_lift_single, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp), mul_comm]

lemma SDR4_comp_lift {R' S' S'' : Type u} [CommRing R'] [CommRing S'] [CommRing S''] (f : R' →+* S')
    (g : Multiplicative Λ →* S') (κ : S' →+* S'') (a : AddMonoidAlgebra R' Λ) :
    κ (SDR3Coact_lift f g a) = SDR3Coact_lift (κ.comp f) ((κ : S' →* S'').comp g) a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | single d r => simp [SDR3Coact_lift_single]

lemma SDR4_iso_app (L : Type u) [CommRing L] (x : L) :
    (Scheme.ΓSpecIso (.of L)).hom.hom ((Scheme.ΓSpecIso (.of L)).inv.hom x) = x :=
  congrArg (fun k : CommRingCat.of L ⟶ CommRingCat.of L => k.hom x) (Scheme.ΓSpecIso (.of L)).inv_hom_id

lemma SDR4_iso_app' (L : Type u) [CommRing L] (x : Γ(Spec (.of L), ⊤)) :
    (Scheme.ΓSpecIso (.of L)).inv.hom ((Scheme.ΓSpecIso (.of L)).hom.hom x) = x :=
  congrArg (fun k : Γ(Spec (.of L), ⊤) ⟶ Γ(Spec (.of L), ⊤) => k.hom x) (Scheme.ΓSpecIso (.of L)).hom_inv_id

end Ring

section Formula

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] {W Z : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- Injectivity of `Γ(Z)[Λ] → Γ(D(Λ) × Z)`. -/
theorem SDR4_lift_inj (r : Z ⟶ W) :
    Function.Injective (SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom
      (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))) := by
  have hbase := SDR3Coact_base_bijective (SDR3Coact_schemePb (Λ := Λ) r)
  have h := SDR3Coact_φ_injective hbase ⊤
  have e : ⇑(SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))) =
      ⇑(SDR3Coact_φ ((SCH).map (SDR3Coact_π Λ r)) (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) ⊤) :=
    funext fun a => (SDR3Coact_φ_top _ _ a).symm
  rw [e]
  exact h

variable (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W) {c : Coact Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) Λ}
  (hc : ∀ y, SDR3Coact_lift ((BigFppfOver.toScheme B S hS).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) (c.σ y) =
    ((BigFppfOver.toScheme B S hS).map (SDR3Coact_a actZ r)).appTop.hom y)

include hc in
/-- The action on functions: `(g • t)^* z = Σ t^*(z_d) g(d)`. -/
theorem SDR4_smul_apply {T : BigFppfOver B S hS} (t : T ⟶ Z) (g : APt (fppfO B S hS) Λ (op T)) (z : Γ((SCH).obj Z, ⊤)) :
    ((SCH).map (actZ.smul (U := op T) g t)).appTop.hom z = SDR3Coact_lift ((SCH).map t).appTop.hom g (c.σ z) := by
  have e := SDR3Coact_pt_a actZ r t g
  let pt : T ⟶ SDR3Coact_Y Λ r := SDR3Coact_pt (r := r) t g
  have h1 : ((SCH).map (actZ.smul (U := op T) g t)).appTop.hom z =
      ((SCH).map pt).appTop.hom (((SCH).map (SDR3Coact_a actZ r)).appTop.hom z) :=
    (SDR3Coact_app (by rw [← Functor.map_comp, e]) z).symm
  rw [h1, ← hc, SDR4_comp_lift]
  congr 2
  · refine RingHom.ext fun y => ?_
    exact SDR3Coact_app (by rw [← Functor.map_comp, SDR3Coact_pt_π]) y
  · refine MonoidHom.ext fun d => ?_
    have := congrArg (fun k => k d) (SDR3Coact_pt_χ (r := r) t g)
    exact this

include hc in
/-- **`SDR3Asm_ActsOnPoints`**: the action on field-valued points read on `Γ(Z)`. -/
theorem SDR4_acts : SDR3Asm_ActsOnPoints c := by
  intro L _ v χ
  let O := Γ((SCH).obj W, ⊤)
  have hpb := SDR3Coact_schemePb (Λ := Λ) r
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (v ≫ (SCH).map r ≫ ((SCH).obj W).isoSpec.hom)
  let m : Spec (.of L) ⟶ Spec (.of (AddMonoidAlgebra O Λ)) :=
    Spec.map (CommRingCat.ofHom (SDR3Coact_lift ρ.hom χ))
  have hm : m ≫ SDR3Coact_str O Λ = v ≫ (SCH).map r ≫ ((SCH).obj W).isoSpec.hom := by
    rw [← hρ, ← Spec.map_comp]
    congr 1
    ext y
    change SDR3Coact_lift ρ.hom χ (AddMonoidAlgebra.single 0 y) = _
    rw [SDR3Coact_lift_single]
    have : χ (Multiplicative.ofAdd (0 : Λ)) = 1 := map_one χ
    rw [this, mul_one]
  let l := hpb.lift m v hm
  have hl1 : l ≫ SDR3Coact_g (Λ := Λ) r = m := hpb.lift_fst _ _ _
  have hl2 : l ≫ (SCH).map (SDR3Coact_π Λ r) = v := hpb.lift_snd _ _ _
  refine ⟨l ≫ (SCH).map (SDR3Coact_a actZ r), fun z => ?_⟩
  have h1 : SDR3Asm_ev (l ≫ (SCH).map (SDR3Coact_a actZ r)) z =
      SDR3Asm_ev l (((SCH).map (SDR3Coact_a actZ r)).appTop.hom z) := by
    simp only [SDR3Asm_ev, Scheme.Hom.comp_appTop]
    rfl
  rw [h1, ← hc, SDR4_comp_lift, SDR4_lift_eq_sum]
  refine Finsupp.sum_congr fun d _ => ?_
  congr 1
  · change ((Scheme.ΓSpecIso (.of L)).hom.hom) (l.appTop.hom ((SDR3Coact_g (Λ := Λ) r).appTop.hom _)) = _
    rw [SDR3Coact_app hl1]
    have := appTop_sp_inv (SDR3Coact_lift ρ.hom χ) (AddMonoidAlgebra.single (Multiplicative.toAdd (Multiplicative.ofAdd d)) (1 : O))
    refine (congrArg _ this).trans ?_
    rw [SDR4_iso_app, SDR3Coact_lift_single, map_one, one_mul]
    rfl
  · change ((Scheme.ΓSpecIso (.of L)).hom.hom) (l.appTop.hom (((SCH).map (SDR3Coact_π Λ r)).appTop.hom _)) = _
    rw [SDR3Coact_app hl2]
    rfl

include hc in
/-- Step 9 input: a morphism invariant on points of the site pulls functions back into degree `0`. -/
theorem SDR4_isHom_zero {U : BigFppfOver B S hS} (s : Z ⟶ U)
    (hs : ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (t : T ⟶ Z), actZ.smul (U := op T) g t ≫ s = t ≫ s)
    (y : Γ((SCH).obj U, ⊤)) : c.IsHom 0 (((SCH).map s).appTop.hom y) :=
  SDR3Coact_isHom_zero actZ r hc (SDR4_lift_inj r) s (hs _ _) y

include hc in
/-- Graded: if `a^*` is computed by a coaction on `B`, the map `B → Γ(Z)` is graded. -/
theorem SDR4_graded {B₀ : Type u} [CommRing B₀] (cB : Coact B₀ Λ) (fs : B₀ →+* Γ((SCH).obj Z, ⊤))
    (h : ∀ b, ((SCH).map (SDR3Coact_a actZ r)).appTop.hom (fs b) =
      SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))
        (AddMonoidAlgebra.mapRingHom Λ fs (cB.σ b))) (d : Λ) (b : B₀) :
    c.comp d (fs b) = fs (cB.comp d b) := by
  have h1 := SDR4_lift_inj (Λ := Λ) r ((hc (fs b)).trans (h b))
  change (c.σ (fs b)).coeff d = _
  rw [h1, AddMonoidAlgebra.coeff_mapRingHom]
  rfl

end Formula

section Pb

variable {Λ : Type u} [AddCommGroup Λ] {W' Q Qr : BigFppfOver B S hS}

/-- The base change `W' ×_Q Qr` of an action on `W'` for which `h : W' → Q` is invariant. -/
noncomputable def SDR4_pbAct (act : AAction (fppfO B S hS) Λ (yoneda.obj W')) (h : W' ⟶ Q) (e : Qr ⟶ Q)
    (hinv : ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (l : T ⟶ W'),
      act.smul (U := op T) g l ≫ h = l ≫ h) :
    AAction (fppfO B S hS) Λ (yoneda.obj (Limits.pullback h e)) where
  smul {U} g l := pullback.lift (act.smul (U := U) g (l ≫ pullback.fst h e)) (l ≫ pullback.snd h e) (by
    refine (hinv (T := U.unop) g _).trans ?_
    rw [Category.assoc, Category.assoc, pullback.condition])
  one_smul {U} l := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      exact act.one_smul (U := U) _
    · rw [pullback.lift_snd]
  mul_smul {U} g g' l := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
      exact act.mul_smul (U := U) g g' _
    · rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  map_smul {U V} f g l := by
    refine pullback.hom_ext ?_ ?_
    · change (f.unop ≫ pullback.lift _ _ _) ≫ _ = pullback.lift _ _ _ ≫ _
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      have := act.map_smul f g (l ≫ pullback.fst h e)
      refine Eq.trans this ?_
      congr 1
    · change (f.unop ≫ pullback.lift _ _ _) ≫ _ = pullback.lift _ _ _ ≫ _
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact (Category.assoc _ _ _).symm

lemma SDR4_pbAct_fst (act : AAction (fppfO B S hS) Λ (yoneda.obj W')) (h : W' ⟶ Q) (e : Qr ⟶ Q)
    (hinv : ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (l : T ⟶ W'),
      act.smul (U := op T) g l ≫ h = l ≫ h) {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T))
    (l : T ⟶ Limits.pullback h e) :
    (SDR4_pbAct act h e hinv).smul (U := op T) g l ≫ pullback.fst h e = act.smul (U := op T) g (l ≫ pullback.fst h e) :=
  pullback.lift_fst _ _ _

lemma SDR4_pbAct_snd (act : AAction (fppfO B S hS) Λ (yoneda.obj W')) (h : W' ⟶ Q) (e : Qr ⟶ Q)
    (hinv : ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (l : T ⟶ W'),
      act.smul (U := op T) g l ≫ h = l ≫ h) {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T))
    (l : T ⟶ Limits.pullback h e) :
    (SDR4_pbAct act h e hinv).smul (U := op T) g l ≫ pullback.snd h e = l ≫ pullback.snd h e :=
  pullback.lift_snd _ _ _

end Pb

end AlgMag.SD

#print axioms AlgMag.SD.SDR4_acts
