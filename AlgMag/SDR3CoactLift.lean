/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDR3CoactSection

/-!
# Lemma D, Step 2: the action on the chart `W' = W ×_X U`, its restriction to a saturated open

`W = 𝔸(P)_T` carries the action `g • c = g^δ c`. If `x` over `W` is invariant, the action
lifts to `W'`, with `W' → U` invariant (`SDR3Coact_liftAction`). A saturated open `V` of an object with an action is an
object with an action (`SDR3Coact_restrict`), and `Γ(U) → Γ(V)` lands in degree `0` (`SDR3Coact_isHom_zero`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Lift

variable {P Λ : Type u} [AddCommMonoid P] [Countable P] [AddCommGroup Λ] (δ : P →+ Λ) {T : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The action `g • c = g^δ c` on `W = 𝔸(P)_T`, on points. -/
noncomputable def SDR3Coact_smulW {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T')) (t : T' ⟶ specObj P T) :
    T' ⟶ specObj P T :=
  specLift (t ≫ specPr P T) (g.comp (AddMonoidHom.toMultiplicative δ) * APt.res t.op (specPt P T))

omit [AddCommGroup Λ] in
lemma SDR3Coact_eta {T' : BigFppfOver B S hS} (t : T' ⟶ specObj P T) :
    specLift (t ≫ specPr P T) (APt.res t.op (specPt P T)) = t :=
  (specLift_uniq _ _ t rfl rfl).symm

lemma SDR3Coact_smulW_one {T' : BigFppfOver B S hS} (t : T' ⟶ specObj P T) :
    SDR3Coact_smulW δ (1 : APt (fppfO B S hS) Λ (op T')) t = t := by
  rw [SDR3Coact_smulW, MonoidHom.one_comp, one_mul, SDR3Coact_eta]

lemma SDR3Coact_smulW_mul {T' : BigFppfOver B S hS} (g h : APt (fppfO B S hS) Λ (op T')) (t : T' ⟶ specObj P T) :
    SDR3Coact_smulW δ (g * h) t = SDR3Coact_smulW δ g (SDR3Coact_smulW δ h t) := by
  rw [SDR3Coact_smulW, SDR3Coact_smulW, SDR3Coact_smulW, specLift_pr, res_specLift, MonoidHom.mul_comp, mul_assoc]

lemma SDR3Coact_smulW_map {T₁ T₂ : BigFppfOver B S hS} (f : T₂ ⟶ T₁) (h : APt (fppfO B S hS) Λ (op T₁))
    (t : T₁ ⟶ specObj P T) :
    f ≫ SDR3Coact_smulW δ h t = SDR3Coact_smulW δ (APt.res f.op h) (f ≫ t) := by
  refine specLift_uniq _ _ _ ?_ ?_
  · rw [Category.assoc, SDR3Coact_smulW, specLift_pr, Category.assoc]
  · rw [op_comp, APt.res_comp, SDR3Coact_smulW, res_specLift, APt.res_mul, op_comp, APt.res_comp]
    rfl

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {δ}

lemma SDR3Coact_inv_smulW {x : X.obj (op (specObj P T))} (hx : IsInvPt X δ x) {T' : BigFppfOver B S hS}
    (g : APt (fppfO B S hS) Λ (op T')) (t : T' ⟶ specObj P T) :
    X.map (SDR3Coact_smulW δ g t).op x = X.map t.op x := by
  have := hx (t ≫ specPr P T) g (APt.res t.op (specPt P T))
  rwa [SDR3Coact_eta] at this

/-- **Step 2**: the action on `W' = W ×_X U`, lifting the one on `W`, and fixing the projection to `U`. -/
theorem SDR3Coact_liftAction {U W' : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X) {x : X.obj (op (specObj P T))}
    (hx : IsInvPt X δ x) (p : W' ⟶ specObj P T) (s : W' ⟶ U) (hps : f.app (op W') s = X.map p.op x)
    (hu : ∀ {T : BigFppfOver B S hS} (a : T ⟶ specObj P _) (b : T ⟶ U), X.map a.op x = f.app (op T) b →
        ∃! l : T ⟶ W', l ≫ p = a ∧ l ≫ s = b) :
    ∃ act : AAction (fppfO B S hS) Λ (yoneda.obj W'), ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T'))
      (l : T' ⟶ W'), act.smul (U := op T') g l ≫ p = SDR3Coact_smulW δ g (l ≫ p) ∧
        act.smul (U := op T') g l ≫ s = l ≫ s := by
  have hex : ∀ {T' : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T')) (l : T' ⟶ W'),
      ∃! l' : T' ⟶ W', l' ≫ p = SDR3Coact_smulW δ g (l ≫ p) ∧ l' ≫ s = l ≫ s := fun g l =>
    SDLocS_lift_action f p s hps hu (l ≫ p) _ (SDR3Coact_inv_smulW hx g _).symm l rfl
  choose sm hsm huniq using @hex
  refine ⟨⟨fun {V} g l => sm (T' := V.unop) g l, ?_, ?_, ?_⟩, fun g l => hsm g l⟩
  · intro V l
    refine (huniq (T' := V.unop) 1 l l ⟨?_, rfl⟩).symm
    exact (SDR3Coact_smulW_one δ _).symm
  · intro V g h l
    refine (huniq (T' := V.unop) (g * h) l _ ⟨?_, ?_⟩).symm
    · rw [(hsm (T' := V.unop) g _).1, (hsm (T' := V.unop) h l).1, SDR3Coact_smulW_mul]
    · rw [(hsm (T' := V.unop) g _).2, (hsm (T' := V.unop) h l).2]
  · intro V V' f' h l
    change f'.unop ≫ sm (T' := V.unop) h l = sm (T' := V'.unop) (APt.res f' h) (f'.unop ≫ l)
    refine huniq (T' := V'.unop) (APt.res f' h) (f'.unop ≫ l) _ ⟨?_, ?_⟩
    · rw [Category.assoc, (hsm (T' := V.unop) h l).1, SDR3Coact_smulW_map, Category.assoc]
      rfl
    · rw [Category.assoc, (hsm (T' := V.unop) h l).2, Category.assoc]

end Lift

section Restrict

variable {Λ : Type u} [AddCommGroup Λ] [Countable Λ] {W Z : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]

/-- **Step 2**: a saturated open `V` of `Z`, as an object of the site (G4) with the restricted action. -/
theorem SDR3Coact_restrict (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W) (V : ((SCH).obj Z).Opens)
    (hV : ∀ y, (SCH).map (SDR3Coact_a actZ r) y ∈ V ↔ (SCH).map (SDR3Coact_π Λ r) y ∈ V) :
    ∃ (Vo : BigFppfOver B S hS) (k : Vo ⟶ Z) (actV : AAction (fppfO B S hS) Λ (yoneda.obj Vo)),
      IsOpenImmersion ((SCH).map k) ∧ Set.range ((SCH).map k) = V ∧
      ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (t : T ⟶ Vo),
        actV.smul (U := op T) g t ≫ k = actZ.smul (U := op T) g (t ≫ k) := by
  have hC : B.Contains (V : Scheme.{u}) := B.contains_of_mono V.ι Z.left.2
  let Vo : BigFppfOver B S hS := siteObject B S hS hC (V.ι ≫ Z.hom.hom)
  let k : Vo ⟶ Z := overHom V.ι rfl
  have hkim : IsOpenImmersion ((SCH).map k) := inferInstanceAs (IsOpenImmersion V.ι)
  have hrange : Set.range ((SCH).map k) = V := V.range_ι
  have hmono : ∀ {T : BigFppfOver B S hS} {a b : T ⟶ Vo}, a ≫ k = b ≫ k → a = b := by
    intro T a b h
    refine toScheme_map_injective ?_
    have h' := congrArg (SCH).map h
    rw [Functor.map_comp, Functor.map_comp] at h'
    exact (cancel_mono ((SCH).map k)).1 h'
  have hlift : ∀ {T : BigFppfOver B S hS} (g : APt (fppfO B S hS) Λ (op T)) (t : T ⟶ Vo),
      ∃ l : T ⟶ Vo, l ≫ k = actZ.smul (U := op T) g (t ≫ k) := by
    intro T g t
    let q : T ⟶ Z := actZ.smul (U := op T) g (t ≫ k)
    have hq : Set.range ((SCH).map q) ⊆ Set.range ((SCH).map k) := by
      rintro _ ⟨x, rfl⟩
      rw [hrange]
      have e : q = SDR3Coact_pt (r := r) (t ≫ k) g ≫ SDR3Coact_a actZ r := (SDR3Coact_pt_a actZ r _ _).symm
      have e1 : (SCH).map q x = (SCH).map (SDR3Coact_a actZ r) ((SCH).map (SDR3Coact_pt (r := r) (t ≫ k) g) x) := by
        rw [e, Functor.map_comp]; rfl
      rw [e1]
      refine (hV _).2 ?_
      have e0 : (SCH).map (SDR3Coact_pt (r := r) (t ≫ k) g) ≫ (SCH).map (SDR3Coact_π Λ r) = (SCH).map (t ≫ k) := by
        rw [← Functor.map_comp, SDR3Coact_pt_π]
      have e2 : (SCH).map (SDR3Coact_π Λ r) ((SCH).map (SDR3Coact_pt (r := r) (t ≫ k) g) x) =
          (SCH).map (t ≫ k) x := congrArg (fun z : (SCH).obj T ⟶ (SCH).obj Z => z x) e0
      rw [e2, ← SetLike.mem_coe, ← hrange, Functor.map_comp]
      exact ⟨(SCH).map t x, rfl⟩
    refine ⟨overHom (IsOpenImmersion.lift ((SCH).map k) ((SCH).map q) hq) ?_, ?_⟩
    · have h1 : IsOpenImmersion.lift ((SCH).map k) ((SCH).map q) hq ≫ (SCH).map k = (SCH).map q :=
        IsOpenImmersion.lift_fac _ _ _
      have h2 : (SCH).map k ≫ Z.hom.hom = Vo.hom.hom := rfl
      rw [← h2, ← Category.assoc, h1]
      exact congrArg (fun z => z.hom) (Over.w q)
    · refine toScheme_map_injective ?_
      rw [Functor.map_comp, map_overHom]
      exact IsOpenImmersion.lift_fac _ _ _
  choose sm hsm using @hlift
  refine ⟨Vo, k, ⟨fun {T} g t => sm (T := T.unop) g t, ?_, ?_, ?_⟩, hkim, hrange, fun g t => hsm g t⟩
  · intro T t
    refine hmono ?_
    rw [hsm (T := T.unop)]
    exact actZ.one_smul (U := T) _
  · intro T g h t
    refine hmono ?_
    rw [hsm (T := T.unop), hsm (T := T.unop), hsm (T := T.unop)]
    exact actZ.mul_smul (U := T) g h _
  · intro T T' f h t
    refine hmono ?_
    change (f.unop ≫ sm (T := T.unop) h t) ≫ k = sm (T := T'.unop) _ (f.unop ≫ t) ≫ k
    rw [Category.assoc, hsm (T := T.unop), hsm (T := T'.unop)]
    have := actZ.map_smul f h (t ≫ k)
    rw [Category.assoc f.unop t k]
    exact this

variable (actZ : AAction (fppfO B S hS) Λ (yoneda.obj Z)) (r : Z ⟶ W)

/-- Step 9 input: a morphism `s` out of `Z` with `a ≫ s = π ≫ s` pulls functions back into degree `0`. -/
theorem SDR3Coact_isHom_zero {c : Coact Γ((SCH).obj Z, ⊤) Λ}
    (hc : ∀ y, SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) (c.σ y) =
        ((SCH).map (SDR3Coact_a actZ r)).appTop.hom y)
    (hφ : Function.Injective (SDR3Coact_lift ((SCH).map (SDR3Coact_π Λ r)).appTop.hom
        (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r))))
    {U : BigFppfOver B S hS} (s : Z ⟶ U) (hs : SDR3Coact_a actZ r ≫ s = SDR3Coact_π Λ r ≫ s) (y : Γ((SCH).obj U, ⊤)) :
    c.IsHom 0 (((SCH).map s).appTop.hom y) := by
  apply hφ
  rw [hc, SDR3Coact_lift_single]
  have h1 : (SDR3Coact_chi (SDR3Coact_g (Λ := Λ) r)) (Multiplicative.ofAdd 0) = 1 := map_one _
  rw [h1, mul_one]
  refine (SDR3Coact_app (by rw [← Functor.map_comp]) y).trans (SDR3Coact_app (by rw [← Functor.map_comp, hs]) y).symm

end Restrict

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Coact_liftAction
#print axioms AlgMag.SD.SDR3Coact_restrict
#print axioms AlgMag.SD.SDR3Coact_isHom_zero
