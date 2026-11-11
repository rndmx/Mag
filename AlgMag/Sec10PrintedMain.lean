/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedVanish
import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction

/-!
# Proposition 10.1 and Corollary 10.3, by the printed cocycle

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1, on the test objects `T = D(P)` for `P` a
commutative group. They are flat over `ℤ`, so `P` is a torsor under `F = L`; the object `G = D(M)` and
`G × G = D(M × M)` are among them. This is `LiftTorsor` of `AlgMag.Sec10PrintedCore`, and the end of the
proof is `LiftTorsor.exists_invariant`. Proposition 9.13 for `F` is `H¹_vanish`: `F` is functorial in
all `A`-linear maps of the coefficients, and the coefficient at `0` is one such.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts AlgMag.S9

attribute [local instance] Stacks.Smooth.moduleMulOpposite

/-- The test objects: `D(P)`, for `P` a commutative group. -/
abbrev CC := AddCommGrpCat.{u}ᵒᵖ

/-- The coefficients of the modules on the test objects. -/
noncomputable def oo : CC.{u}ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ))

variable (M : Type u) [AddCommGroup M]

/-- `D(M)` on the test objects: a point of `D(M)` over `D(P)` is a morphism `M → P`. -/
noncomputable def HH : CC.{u}ᵒᵖ ⥤ MonCat.{u} where
  obj U := MonCat.of (Multiplicative (M →+ U.unop.unop))
  map f := MonCat.ofHom
    { toFun := fun g => Multiplicative.ofAdd (f.unop.unop.hom.comp (Multiplicative.toAdd g))
      map_one' := by
        refine congrArg Multiplicative.ofAdd (AddMonoidHom.ext fun m => ?_)
        exact map_zero f.unop.unop.hom
      map_mul' := fun g g' => by
        refine congrArg Multiplicative.ofAdd (AddMonoidHom.ext fun m => ?_)
        exact map_add f.unop.unop.hom _ _ }

variable {M}

variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
  (hρφ : (mr M φ).comp ρ = ρ₀.comp φ)
  (hco : ∀ x, mr M ρ (ρ x) = Lifts.diag A₁ M (ρ x)) (hc : (aug A₁ M).comp ρ = RingHom.id _)
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
  (b : Spec (CommRingCat.of A₁) ⟶ Z)
variable (ay : AbsAct M Y) (az : AbsAct M Z)
  (hf : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    ay.smul h x ≫ f = az.smul h (x ≫ f))
  (ha : IsEq ay ρ₀ a) (hb : IsEq az ρ b) (w : a ≫ f = sp φ ≫ b)

/-- `F = p_* Hom(a^*Ω, C)` on the test objects. -/
noncomputable def FF : PMod oo.{u} where
  obj U := L f a (RingHom.ker φ) U.unop.unop
  grp U := inferInstance
  mod U := Module.compHom _ ((ULift.ringEquiv.{0, u} : ULift ℤ ≃+* ℤ).toRingHom)
  map g := L.mapPHom g.unop.unop.hom
  map_smul g r x := map_zsmul (L.mapPHom g.unop.unop.hom) r.down x
  map_id U x := L.ext' (by
    change sp (md _ (AddMonoidHom.id _)) ≫ x.1 = x.1
    rw [md_id, sp_id', Category.id_comp])
  map_comp g h x := L.ext' (by
    change sp (md _ (h.unop.unop.hom.comp g.unop.unop.hom)) ≫ x.1 =
      sp (md _ h.unop.unop.hom) ≫ sp (md _ g.unop.unop.hom) ≫ x.1
    rw [← md_comp, sp_comp, Category.assoc])

lemma FF_map_val {U V : CC.{u}ᵒᵖ} (g : U ⟶ V) (x : L f a (RingHom.ker φ) U.unop.unop) :
    ((FF (φ := φ) f a).map g x : L f a (RingHom.ker φ) V.unop.unop) = L.mapP g.unop.unop.hom x := rfl

/-- The action of `D(M)` on `F`. -/
noncomputable def AA : HModule (HH M) (FF (φ := φ) f a) where
  smul {U} g x := L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (Multiplicative.toAdd g) x
  one_smul {U} x := L.ext' (act_zero ay _ (hcN hs hN hq ρ ρ₀ hρφ hc) x.1)
  mul_smul {U} g h x := L.ext' (act_add ay _ (hcoN hs hN hq ρ ρ₀ hρφ hco) _ _ x.1)
  smul_add {U} g x y := L.act_add hs hN hq ρ ρ₀ hρφ ay az hf ha _ x y
  smul_smul {U} g r x :=
    map_zsmul (AddMonoidHom.mk' (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (P := U.unop.unop) (Multiplicative.toAdd g))
      (L.act_add hs hN hq ρ ρ₀ hρφ ay az hf ha _)) r.down x
  map_smul {U V} g h x := L.ext' (act_md ay _ g.unop.unop.hom _ x.1)

/-- The base point: `S` itself, i.e. `D(0)`. -/
noncomputable abbrev VV : CC.{u} := op (AddCommGrpCat.of PUnit.{u + 1})

lemma V_ext {T : CC.{u}} (s t : T ⟶ VV) : s = t := by
  refine Quiver.Hom.unop_inj (AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_))
  have : x = 0 := rfl
  rw [this]
  exact (map_zero _).trans (map_zero _).symm

lemma coprod_ι₁ {Q : Type u} [AddCommGroup Q] (g g' : M →+ Q) : (g.coprod g').comp (ι₁ M M) = g :=
  AddMonoidHom.ext fun m => by
    change g m + g' 0 = g m
    rw [map_zero, add_zero]

lemma coprod_prH {Q : Type u} [AddCommGroup Q] (g g' : M →+ Q) :
    (g.coprod g').comp (prH (0 : M →+ M)) = g' :=
  AddMonoidHom.ext fun m => by
    change g 0 + g' m = g' m
    rw [map_zero, zero_add]

/-- The torsor of the printed proof, on the test objects. -/
noncomputable def TT : LiftTorsor (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) (VV) where
  Flat _ := True
  P :=
    { obj := fun U => Pl φ f a b U.unop.unop
      map := fun g => ↾ (Pl.mapP g.unop.unop.hom)
      map_id := fun U => by
        ext x
        refine Pl.ext' ?_
        change sp (md _ (AddMonoidHom.id _)) ≫ x.1 = x.1
        rw [md_id, sp_id', Category.id_comp]
      map_comp := fun g h => by
        ext x
        refine Pl.ext' ?_
        change sp (md _ (h.unop.unop.hom.comp g.unop.unop.hom)) ≫ x.1 =
          sp (md _ h.unop.unop.hom) ≫ sp (md _ g.unop.unop.hom) ≫ x.1
        rw [← md_comp, sp_comp, Category.assoc] }
  act g x := Pl.act ρ ρ₀ hρφ ay az hf ha hb (Multiplicative.toAdd g) x
  act_mul g g' x := Pl.ext' (act_add ay ρ hco _ _ x.1)
  act_map s g x := Pl.ext' (act_md ay ρ s.unop.hom _ x.1)
  diff _ x y := diffL hs hN hq w x y
  diff_add _ x y z := diffL_add hs hN hq w x y z
  diff_eq _ x y h := Pl_eq_of_diffL hs hN hq w x y h
  diff_act _ g x y := diffL_act hs hN hq ρ ρ₀ hρφ ay az hf ha hb w _ x y
  diff_map _ _ s x y := diffL_mapP hs hN hq w s.unop.hom x y
  G := op (AddCommGrpCat.of M)
  π := (AddCommGrpCat.ofHom 0).op
  flatG := trivial
  u := Multiplicative.ofAdd (AddMonoidHom.id M)
  cls {T} _ g := (AddCommGrpCat.ofHom (Multiplicative.toAdd g)).op
  cls_π _ _ := V_ext _ _
  cls_u _ g := rfl
  cls_uniq t g k _ h := by
    refine Quiver.Hom.unop_inj (AddCommGrpCat.hom_ext ?_)
    subst h
    rfl
  G₂ := op (AddCommGrpCat.of (M × M))
  π₂ := (AddCommGrpCat.ofHom 0).op
  flatG₂ := trivial
  u₁ := Multiplicative.ofAdd (ι₁ M M)
  u₂ := Multiplicative.ofAdd (prH (0 : M →+ M))
  cls₂ {T} _ g g' := (AddCommGrpCat.ofHom ((Multiplicative.toAdd g).coprod (Multiplicative.toAdd g'))).op
  cls₂_π _ _ _ := V_ext _ _
  cls₂_u₁ _ g g' := congrArg Multiplicative.ofAdd (coprod_ι₁ _ _)
  cls₂_u₂ _ g g' := congrArg Multiplicative.ofAdd (coprod_prH _ _)

/-- **Proposition 9.13 for `F`**: a cocycle is a coboundary, with `v` minus the coefficient at `0` of its
universal value. -/
theorem coboundary_of_cocycle (c : Cochain (HH M) (FF (φ := φ) f a) VV 1)
    (hz : c ∈ Zn (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) VV 1) :
    ∃ v : (FF (φ := φ) f a).obj (op VV), ∀ {T : CC.{u}} (t : T ⟶ VV) (g : (HH M).obj (op T)),
      c.app t ![g] = (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha).smul g ((FF (φ := φ) f a).map t.op v) -
        (FF (φ := φ) f a).map t.op v := by
  let G : CC.{u} := op (AddCommGrpCat.of M)
  let π : G ⟶ VV := (AddCommGrpCat.ofHom 0).op
  let X : L f a (RingHom.ker φ) M := c.app π ![Multiplicative.ofAdd (AddMonoidHom.id M)]
  have form : ∀ {T : CC.{u}} (t : T ⟶ VV) (g : (HH M).obj (op T)),
      c.app t ![g] = L.mapP (Multiplicative.toAdd g) X := by
    intro T t g
    let s : T ⟶ G := (AddCommGrpCat.ofHom (Multiplicative.toAdd g)).op
    have n := c.naturality s π ![Multiplicative.ofAdd (AddMonoidHom.id M)]
    have e₁ : s ≫ π = t := V_ext _ _
    rw [e₁] at n
    have e₂ : (fun i => ((HH M).map s.op).hom ((![Multiplicative.ofAdd (AddMonoidHom.id M)] : Fin 1 → (HH M).obj (op G)) i)) = ![g] := by
      funext i
      fin_cases i
      rfl
    rw [e₂] at n
    exact n
  let G₂ : CC.{u} := op (AddCommGrpCat.of (M × M))
  let t₂ : G₂ ⟶ VV := (AddCommGrpCat.ofHom 0).op
  have Zc := (mem_Z1_iff (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) c).1 hz t₂
    (Multiplicative.ofAdd (ι₁ M M)) (Multiplicative.ofAdd (prH (0 : M →+ M)))
  have hd : Multiplicative.toAdd (Multiplicative.ofAdd (ι₁ M M) * Multiplicative.ofAdd (prH (0 : M →+ M))) =
      prH (AddMonoidHom.id M) :=
    AddMonoidHom.ext fun m => Prod.ext (add_zero m) (zero_add m)
  have Z₁ : L.mapP (prH (AddMonoidHom.id M)) X = L.mapP (ι₁ M M) X +
      L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (ι₁ M M) (L.mapP (prH (0 : M →+ M)) X) := by
    rw [← hd]
    exact (form t₂ _).symm.trans (Zc.trans (congrArg₂ (· + ·) (form t₂ _)
      (congrArg ((AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha).smul _) (form t₂ _))))
  let K := L.int (M := M) (L.mapP (prH (0 : M →+ M)) X)
  have hK₀ : K.1 = sp (cs _ M) ≫ co₀ X := L.int_eval _ X
  have hK₁ : L.int (M := M) (L.mapP (prH (AddMonoidHom.id M)) X) = K :=
    L.ext' ((L.int_eval _ X).trans hK₀.symm)
  have hK : K = X + L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (AddMonoidHom.id M) K := by
    have := congrArg (L.int (M := M)) Z₁
    rw [hK₁, L.int_add, L.int_inl] at this
    refine this.trans (congrArg (X + ·) ?_)
    exact L.int_act hs hN hq ρ ρ₀ hρφ ay az hf ha (AddMonoidHom.id M) _
  -- the coefficient at `0`
  have sa : sp (aug A M) ≫ sp (cs A M) = 𝟙 _ := (sp_comp _ _).symm.trans ((congrArg sp aug_cs).trans sp_id')
  have sa' : sp (aug (Sq A (RingHom.ker φ)) M) ≫ sp (cs _ M) = 𝟙 _ :=
    (sp_comp _ _).symm.trans ((congrArg sp aug_cs).trans sp_id')
  have c₁ : sp (sFst (RingHom.ker φ)) ≫ co₀ X = a := by
    have h := K.2.1
    rw [hK₀, sp_cs_map] at h
    have := congrArg (sp (aug A M) ≫ ·) h
    beta_reduce at this
    rwa [← Category.assoc, sa, Category.id_comp, ← Category.assoc, sa, Category.id_comp] at this
  have c₂ : co₀ X ≫ f = sp (sInl (RingHom.ker φ)) ≫ a ≫ f := by
    have h := K.2.2
    rw [hK₀, Category.assoc, sp_cs_map] at h
    have := congrArg (sp (aug (Sq A (RingHom.ker φ)) M) ≫ ·) h
    beta_reduce at this
    rwa [← Category.assoc, sa', Category.id_comp, ← Category.assoc, sa', Category.id_comp] at this
  let v₀ : L f a (RingHom.ker φ) PUnit.{u + 1} :=
    ⟨sp (cs _ _) ≫ co₀ X, by rw [sp_cs_map, c₁], by rw [Category.assoc, c₂, sp_cs_map]⟩
  let e : PUnit.{u + 1} →+ M := 0
  have hKv : K = L.mapP e v₀ := L.ext' (hK₀.trans (sp_md_cs e _).symm)
  refine ⟨-v₀, fun {T} t g => ?_⟩
  let gg : M →+ T.unop := Multiplicative.toAdd g
  let aH := AddMonoidHom.mk' (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (P := T.unop) gg)
    (L.act_add hs hN hq ρ ρ₀ hρφ ay az hf ha _)
  let w : L f a (RingHom.ker φ) T.unop := L.mapP t.unop.hom v₀
  have hw : L.mapP gg K = w := by
    rw [hKv]
    refine L.ext' ?_
    change sp (md _ gg) ≫ sp (md _ e) ≫ _ = sp (md _ t.unop.hom) ≫ _
    rw [← Category.assoc, ← sp_comp, md_comp]
    have : gg.comp e = t.unop.hom := AddMonoidHom.ext fun x => by
      have hx : x = 0 := rfl
      rw [hx, map_zero, map_zero]
    rw [this]
  have hact : L.mapP gg (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha (AddMonoidHom.id M) K) = aH w := by
    rw [← hw]
    exact L.ext' (act_md ay _ gg _ K.1)
  have hX : L.mapP gg X = w - aH w := by
    have h₃ := congrArg (L.mapP gg) hK
    rw [L.mapP_add, hact, hw] at h₃
    exact eq_sub_of_add_eq h₃.symm
  refine (form t g).trans (hX.trans ?_)
  change w - aH w = aH (L.mapPHom t.unop.hom (-v₀)) - L.mapPHom t.unop.hom (-v₀)
  rw [map_neg, map_neg]
  change w - aH w = -aH w - -w
  rw [sub_neg_eq_add, ← sub_eq_neg_add]

theorem H1_vanish : Subsingleton (Hn (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) VV 1) :=
  Hn_subsingleton_of _ VV 0 fun c hd => by
    obtain ⟨v, hv⟩ := coboundary_of_cocycle hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha c hd
    exact (mem_B1_iff (AA hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) c).2 ⟨v, hv⟩

include hs hN hq hρφ hco hc hf ha hb in
/-- **Proposition 10.1 / Corollary 10.3** on `Spec` rings, along the printed proof: from a lift `α`, the
torsor `TT`, the cocycle `g · α - α`, its vanishing, and `β = α - v`. -/
theorem exists_invariant_lift (w : a ≫ f = sp φ ≫ b) (α : Spec (CommRingCat.of A₁) ⟶ Y)
    (h₁ : sp φ ≫ α = a) (h₂ : α ≫ f = b) :
    ∃ l : Spec (CommRingCat.of A₁) ⟶ Y, sp φ ≫ l = a ∧ l ≫ f = b ∧ IsEq ay ρ l := by
  let TL := TT hs hN hq ρ ρ₀ hρφ hco hc f a b ay az hf ha hb w
  let a' : Pl φ f a b PUnit.{u + 1} := ⟨sp (cs _ _) ≫ α, by rw [sp_cs_map, h₁], by rw [Category.assoc, h₂]⟩
  obtain ⟨β, hβ⟩ := LiftTorsor.exists_invariant TL a' trivial
    (H1_vanish hs hN hq ρ ρ₀ hρφ hco hc f a ay az hf ha) (fun v => by
      refine ⟨addL hs hN hq w a' (-v), ?_⟩
      have e₁ := diffL_addL hs hN hq w a' (-v)
      have e₂ := diffL_add hs hN hq w a' (addL hs hN hq w a' (-v)) a'
      rw [e₁, diffL_self] at e₂
      exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact e₂))
  have hu := hβ (T := op (AddCommGrpCat.of M)) (AddCommGrpCat.ofHom 0).op (Multiplicative.ofAdd (AddMonoidHom.id M))
  let β' : Pl φ f a b PUnit.{u + 1} := β
  let e : PUnit.{u + 1} →+ M := 0
  have hmd : md A₁ e = (cs A₁ M).comp (aug A₁ PUnit.{u + 1}) := by
    refine rh_ext ?_ fun k => ?_
    · rw [md_cs, RingHom.comp_assoc, aug_cs, RingHom.comp_id]
    · rw [md_single, RingHom.comp_apply, aug_of]; rfl
  let l := sp (aug A₁ PUnit.{u + 1}) ≫ β'.1
  have hl : (Pl.mapP e β').1 = sp (cs A₁ M) ≫ l := by
    change sp (md A₁ e) ≫ β'.1 = _
    rw [hmd, sp_comp, Category.assoc]
  refine ⟨l, ?_, ?_, isEq_of_act ay ρ l ?_⟩
  · have e₀ : φ.comp (aug A₁ PUnit.{u + 1}) = (aug A PUnit.{u + 1}).comp (mr _ φ) := (aug_mr φ).symm
    change sp φ ≫ sp _ ≫ β'.1 = a
    rw [← Category.assoc, ← sp_comp, e₀, sp_comp, Category.assoc, β'.2.1, ← Category.assoc, ← sp_comp, aug_cs,
      sp_id', Category.id_comp]
  · change (sp _ ≫ β'.1) ≫ f = b
    rw [Category.assoc, β'.2.2, ← Category.assoc, ← sp_comp, aug_cs, sp_id', Category.id_comp]
  · rw [← hl]
    exact congrArg Subtype.val hu

end AlgMag.Sec10Printed
