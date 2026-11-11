/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedPl

/-!
# The action on `P` and on `L`, and the coefficient at `0`

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1 and Proposition 9.13. The vanishing of `H¹`
is the functional "coefficient at `0` of the last variable" `L(P × M) → L(P)`, which commutes with the
action of the first variable. It is read on the Milnor square of `avgRing`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1500000

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

/-- Keeps one additive structure on `P × M`, the one of the group. -/
@[reducible] instance (priority := 2000) prodACM (P M : Type u) [AddCommGroup P] [AddCommGroup M] :
    AddCommMonoid (P × M) := (inferInstance : AddCommGroup (P × M)).toAddCommMonoid

/-- `p ↦ (p, 0)`. -/
def ι₁ (P M : Type u) [AddCommGroup P] [AddCommGroup M] : P →+ P × M where
  toFun p := (p, 0)
  map_zero' := rfl
  map_add' x y := Prod.ext rfl (add_zero 0).symm

/-- `m ↦ (h m, m)`. -/
def prH {M : Type u} [AddCommGroup M] (h : M →+ M) : M →+ M × M where
  toFun m := (h m, m)
  map_zero' := Prod.ext (map_zero h) rfl
  map_add' x y := Prod.ext (map_add h x y) rfl

section Cur

variable {M : Type u} [AddCommGroup M] {P : Type u} [AddCommGroup P]
  {W W₁ : Type u} [CommRing W] [CommRing W₁]

/-- `W[P × M] = W[P][M]`. -/
noncomputable def cur (W : Type u) [CommRing W] (P M : Type u) [AddCommGroup P] [AddCommGroup M] :
    AddMonoidAlgebra W (P × M) →+* AddMonoidAlgebra (AddMonoidAlgebra W P) M :=
  lft ((cs _ M).comp (cs W P))
    { toFun := fun k => AddMonoidAlgebra.single (Multiplicative.toAdd k).2
        (AddMonoidAlgebra.single (Multiplicative.toAdd k).1 1)
      map_one' := rfl
      map_mul' := fun x y => by
        rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, mul_one]
        rfl }

lemma cur_cs : (cur W P M).comp (cs W (P × M)) = (cs _ M).comp (cs W P) := lft_cs _ _

lemma cur_of (k : P × M) : cur W P M (AddMonoidAlgebra.single k 1) =
    AddMonoidAlgebra.single k.2 (AddMonoidAlgebra.single k.1 1) := lft_of _ _ k

lemma cur_single (k : P × M) (r : W) : cur W P M (AddMonoidAlgebra.single k r) =
    AddMonoidAlgebra.single k.2 (AddMonoidAlgebra.single k.1 r) := by
  have e : (AddMonoidAlgebra.single k r : AddMonoidAlgebra W (P × M)) =
      cs W _ r * AddMonoidAlgebra.single k 1 := by
    change _ = AddMonoidAlgebra.single 0 r * _
    rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rw [e, map_mul, cur_of, ← RingHom.comp_apply, cur_cs]
  change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 r) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, zero_add, zero_add,
    mul_one]

lemma cur_natural (w : W →+* W₁) :
    (mr M (mr P w)).comp (cur W P M) = (cur W₁ P M).comp (mr (P × M) w) := by
  refine rh_ext ?_ fun k => ?_
  · refine RingHom.ext fun x => ?_
    change mr M (mr P w) (cur W P M (AddMonoidAlgebra.single 0 x)) =
      cur W₁ P M (mr (P × M) w (AddMonoidAlgebra.single 0 x))
    rw [cur_single, mr_single, mr_single, mr_single, cur_single]
  · simp only [RingHom.comp_apply]
    rw [cur_of, mr_single, mr_single, mr_single, map_one, cur_of]

end Cur

section Act

variable {M : Type u} [AddCommGroup M]
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
  (ρ : A₁ →+* AddMonoidAlgebra A₁ M) (ρ₀ : A →+* AddMonoidAlgebra A M)
  (hρφ : (mr M φ).comp ρ = ρ₀.comp φ)
variable {Y Z : Scheme.{u}} {f : Y ⟶ Z} {a : Spec (CommRingCat.of A) ⟶ Y}
  {b : Spec (CommRingCat.of A₁) ⟶ Z}
variable (ay : AbsAct M Y) (az : AbsAct M Z)
  (hf : ∀ {T : Scheme.{u}} (h : Multiplicative M →* Γ(T, ⊤)) (x : T ⟶ Y),
    ay.smul h x ≫ f = az.smul h (x ≫ f))
  (ha : IsEq ay ρ₀ a) (hb : IsEq az ρ b)
variable {P P₁ : Type u} [AddCommGroup P] [AddCommGroup P₁]

/-- `g · a`. -/
noncomputable def Pl.act (g : M →+ P) (x : Pl φ f a b P) : Pl φ f a b P :=
  ⟨Sec10Printed.act ay ρ g x.1, by
    rw [act_mr ay φ ρ ρ₀ hρφ.symm, x.2.1, act_of_isEq ay ρ₀ a ha], by
    rw [act_comp_f ay az f hf, x.2.2, act_of_isEq az ρ b hb]⟩

include hf ha in
lemma isEq_af : IsEq az ρ₀ (a ≫ f) := by
  have e := congrArg (· ≫ f) ha
  beta_reduce at e
  rw [Category.assoc, hf, Category.assoc] at e
  exact e

include ha in
lemma L_act_1 (g : M →+ P) (l : Spec (CommRingCat.of (AddMonoidAlgebra (Sq A (RingHom.ker φ)) P)) ⟶ Y)
    (h : sp (mr P (sFst (RingHom.ker φ))) ≫ l = sp (cs A P) ≫ a) :
    sp (mr P (sFst (RingHom.ker φ))) ≫ Sec10Printed.act ay (ϱN hs hN hq ρ ρ₀ hρφ) g l = sp (cs A P) ≫ a := by
  rw [act_mr ay (sFst _) (ϱN hs hN hq ρ ρ₀ hρφ) ρ₀ (fst_ϱN hs hN hq ρ ρ₀ hρφ).symm, h,
    act_of_isEq ay ρ₀ a ha]

include ha hf in
lemma L_act_2 (g : M →+ P) (l : Spec (CommRingCat.of (AddMonoidAlgebra (Sq A (RingHom.ker φ)) P)) ⟶ Y)
    (h : l ≫ f = sp (mr P (sInl (RingHom.ker φ))) ≫ sp (cs A P) ≫ a ≫ f) :
    Sec10Printed.act ay (ϱN hs hN hq ρ ρ₀ hρφ) g l ≫ f =
      sp (mr P (sInl (RingHom.ker φ))) ≫ sp (cs A P) ≫ a ≫ f := by
  have e := act_mr az (P := P) (sInl (RingHom.ker φ)) ρ₀ (ϱN hs hN hq ρ ρ₀ hρφ)
    (ϱN_inl hs hN hq ρ ρ₀ hρφ) g (sp (cs A P) ≫ a ≫ f)
  rw [act_of_isEq az ρ₀ (a ≫ f) (isEq_af ρ₀ ay az hf ha)] at e
  rw [act_comp_f ay az f hf, h]
  exact e.symm

/-- `g · v`. -/
noncomputable def L.act (g : M →+ P) (x : L f a (RingHom.ker φ) P) : L f a (RingHom.ker φ) P :=
  ⟨Sec10Printed.act ay (ϱN hs hN hq ρ ρ₀ hρφ) g x.1,
    L_act_1 hs hN hq ρ ρ₀ hρφ ay ha g x.1 x.2.1, L_act_2 hs hN hq ρ ρ₀ hρφ ay az hf ha g x.1 x.2.2⟩

lemma L.act_val (g : M →+ P) (x : L f a (RingHom.ker φ) P) :
    (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g x).1 = Sec10Printed.act ay (ϱN hs hN hq ρ ρ₀ hρφ) g x.1 := rfl

lemma L.act_add (g : M →+ P) (x y : L f a (RingHom.ker φ) P) :
    L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g (x + y) =
      L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g x + L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g y := by
  have hp : Sec10Printed.act ay (ϱ₂ hs hN hq ρ ρ₀ hρφ) g (L.pair x y).1 =
      (L.pair (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g x) (L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g y)).1 := by
    refine milnor_ext (milnor_map milnor_prod P) ?_ ?_
    · rw [act_mr ay _ _ _ (ϱ₂_1 hs hN hq ρ ρ₀ hρφ).symm]
      refine Eq.trans ?_ (congrArg Subtype.val (L.map_fst_pair _ _)).symm
      exact congrArg _ (congrArg Subtype.val (L.map_fst_pair x y))
    · rw [act_mr ay _ _ _ (ϱ₂_2 hs hN hq ρ ρ₀ hρφ).symm]
      refine Eq.trans ?_ (congrArg Subtype.val (L.map_snd_pair _ _)).symm
      exact congrArg _ (congrArg Subtype.val (L.map_snd_pair x y))
  refine L.ext' ?_
  change Sec10Printed.act ay (ϱN hs hN hq ρ ρ₀ hρφ) g (sp (mr P (sMap (LinearMap.fst A _ _ + LinearMap.snd A _ _))) ≫
      (L.pair x y).1) = sp (mr P (sMap (LinearMap.fst A _ _ + LinearMap.snd A _ _))) ≫ _
  rw [← act_mr ay _ _ _ (ϱ_add hs hN hq ρ ρ₀ hρφ), hp]

/-- `g · b - g · c = g · (b - c)`. -/
lemma diffL_act (w : a ≫ f = sp φ ≫ b) (g : M →+ P) (x y : Pl φ f a b P) :
    diffL hs hN hq w (Pl.act ρ ρ₀ hρφ ay az hf ha hb g x) (Pl.act ρ ρ₀ hρφ ay az hf ha hb g y) =
      L.act hs hN hq ρ ρ₀ hρφ ay az hf ha g (diffL hs hN hq w x y) := by
  refine L.ext' ?_
  have e : gD hs (Pl.act ρ ρ₀ hρφ ay az hf ha hb g x) (Pl.act ρ ρ₀ hρφ ay az hf ha hb g y) =
      Sec10Printed.act ay (ϱD hs ρ ρ₀ hρφ) g (gD hs x y) := by
    refine gD_ext hs ?_ ?_
    · rw [gD_1, act_mr ay _ _ _ (ϱD_1 hs ρ ρ₀ hρφ).symm, gD_1]
      rfl
    · rw [gD_2, act_mr ay _ _ _ (ϱD_2 hs ρ ρ₀ hρφ).symm, gD_2]
      rfl
  rw [diffL_val, e, L.act_val, diffL_val, act_mr ay _ _ _ (ϱN_q hs hN hq ρ ρ₀ hρφ)]

/-! ### The coefficient at `0` -/

section Int

variable (N N₁ : Type u) [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]

lemma sq_zero_sFst (x y : Sq A N) (hx : sFst N x = 0) (hy : sFst N y = 0) : x * y = 0 := by
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  refine sq_ext ?_ ?_ <;> simp [hx', hy']

/-- `φ' = (A[N] → A)[P]`. -/
noncomputable abbrev ph (P : Type u) [AddCommGroup P] :
    AddMonoidAlgebra (Sq A N) P →+* AddMonoidAlgebra A P := mr P (sFst N)

lemma ph_surj : Function.Surjective (ph (A := A) N P) := mr_surjective _ sFst_surjective

lemma ph_sq : ∀ x y, ph (A := A) N P x = 0 → ph (A := A) N P y = 0 → x * y = 0 :=
  map_sq_zero (sFst N) (sq_zero_sFst N)

variable {N N₁}

lemma gI_hs (l : Spec (CommRingCat.of (AddMonoidAlgebra (Sq A N) (P × M))) ⟶ Y)
    (h : sp (mr (P × M) (sFst N)) ≫ l = sp (cs A (P × M)) ≫ a) :
    sp (AddMonoidAlgebra.mapRingHom M (ph (A := A) N P)) ≫ sp (cur (Sq A N) P M) ≫ l =
      sp (cst (AddMonoidAlgebra A P) M) ≫ sp (cs A P) ≫ a := by
  have e₁ := cur_natural (M := M) (P := P) (sFst (A := A) N)
  have e₂ := cur_cs (W := A) (P := P) (M := M)
  calc _ = sp ((mr M (mr P (sFst (A := A) N))).comp (cur (Sq A N) P M)) ≫ l := by
        rw [sp_comp, Category.assoc]
    _ = sp (cur A P M) ≫ sp (mr (P × M) (sFst N)) ≫ l := by rw [e₁, sp_comp, Category.assoc]
    _ = sp ((cur A P M).comp (cs A (P × M))) ≫ a := by rw [h, sp_comp, Category.assoc]
    _ = _ := by rw [e₂, sp_comp, Category.assoc]

/-- The pair `(x, a)` on `Spec` of `avgRing`. -/
noncomputable def gI (x : L f a N (P × M)) :
    Spec (CommRingCat.of (avgRing (M := M) (ph (A := A) N P))) ⟶ Y :=
  gl (milnor_avg _ (ph_surj N)) (avgFst_surjective _ (ph_surj N)) (sp (cur _ P M) ≫ x.1) (sp (cs A P) ≫ a)
    (gI_hs x.1 x.2.1)

lemma gI_1 (x : L f a N (P × M)) : sp (avgSnd _) ≫ gI x = sp (cur _ P M) ≫ x.1 :=
  gl_p (milnor_avg _ (ph_surj N)) _ _ _ _

lemma gI_2 (x : L f a N (P × M)) : sp (avgFst _) ≫ gI x = sp (cs A P) ≫ a :=
  gl_q (milnor_avg _ (ph_surj N)) _ _ _ _

lemma avg_ext {T : Scheme.{u}} {r s : Spec (CommRingCat.of (avgRing (M := M) (ph (A := A) N P))) ⟶ T}
    (h₁ : sp (avgSnd _) ≫ r = sp (avgSnd _) ≫ s) (h₂ : sp (avgFst _) ≫ r = sp (avgFst _) ≫ s) : r = s :=
  milnor_ext (milnor_avg _ (ph_surj N)) h₁ h₂

/-- **The coefficient at `0`** of the last variable. -/
noncomputable def L.int (x : L f a N (P × M)) : L f a N P :=
  ⟨sp (avgInt _ (ph_sq N)) ≫ gI x, by
    rw [← Category.assoc, ← sp_comp, φ_avgInt, gI_2], by
    let k : A →+* avgRing (M := M) (ph (A := A) N P) :=
      (avgCst _).comp ((mr P (sInl N)).comp (cs A P))
    have e : gI x ≫ f = sp k ≫ a ≫ f := by
      refine avg_ext ?_ ?_
      · have e₁ : (avgSnd (ph (A := A) N P)).comp k =
            (cur _ P M).comp ((mr (P × M) (sInl N)).comp (cs A (P × M))) := by
          refine RingHom.ext fun t => ?_
          change cs _ M (mr P (sInl N) (cs A P t)) = cur _ P M (mr (P × M) (sInl N) (cs A (P × M) t))
          have e₂ := RingHom.congr_fun (mr_cs (P := P × M) (sInl (A := A) N)) t
          have e₃ := RingHom.congr_fun (mr_cs (P := P) (sInl (A := A) N)) t
          simp only [RingHom.comp_apply] at e₂ e₃
          rw [e₂, e₃, ← RingHom.comp_apply (cur _ P M), cur_cs]
          rfl
        have e₃ : sp (avgSnd (ph (A := A) N P)) ≫ sp k =
            sp (cur _ P M) ≫ sp (mr (P × M) (sInl N)) ≫ sp (cs A (P × M)) := by
          rw [← sp_comp, e₁, sp_comp, sp_comp]
        rw [← Category.assoc, gI_1, Category.assoc, x.2.2, ← Category.assoc (sp _) (sp k), e₃]
        simp only [Category.assoc]
      · have e₁ : (avgFst (ph (A := A) N P)).comp k = cs A P := by
          refine RingHom.ext fun t => ?_
          change mr P (sFst N) (mr P (sInl N) (cs A P t)) = _
          rw [← RingHom.comp_apply, mr_comp, sFst_inl, mr_id]
          rfl
        have e₃ : sp (avgFst (ph (A := A) N P)) ≫ sp k = sp (cs A P) := by rw [← sp_comp, e₁]
        rw [← Category.assoc, gI_2, ← Category.assoc (sp _) (sp k), e₃, Category.assoc]
    have e₂ : (avgInt _ (ph_sq N)).comp k = (mr P (sInl N)).comp (cs A P) := by
      rw [← RingHom.comp_assoc, avgInt_cst, RingHom.id_comp]
    rw [Category.assoc, e, ← Category.assoc (sp _) (sp k), ← sp_comp, e₂, sp_comp, Category.assoc]⟩

lemma L.int_val (x : L f a N (P × M)) : (L.int x).1 = sp (avgInt _ (ph_sq N)) ≫ gI x := rfl

/-- `avgRing` on `sMap`. -/
noncomputable def avgN (u : N →ₗ[A] N₁) (P : Type u) [AddCommGroup P] :
    avgRing (M := M) (ph (A := A) N P) →+* avgRing (M := M) (ph (A := A) N₁ P) :=
  avgMap _ _ (RingHom.id _) (mr M (mr P (sMap u))) (fun p => by
    rw [← RingHom.comp_apply, mr_comp, mr_comp, sFst_map]
    exact avg_prop _ p)

lemma L.int_map (u : N →ₗ[A] N₁) (x : L f a N (P × M)) : L.int (x.map u) = (L.int x).map u := by
  refine L.ext' ?_
  have e : gI (x.map u) = sp (avgN u P) ≫ gI x := by
    refine avg_ext ?_ ?_
    · have e₁ : (avgSnd (ph (A := A) N₁ P)).comp (avgN (M := M) u P) =
          (mr M (mr P (sMap u))).comp (avgSnd _) := rfl
      have e₂ : sp (avgSnd (ph (A := A) N₁ P)) ≫ sp (avgN (M := M) u P) =
          sp (mr M (mr P (sMap u))) ≫ sp (avgSnd _) := by rw [← sp_comp, e₁, sp_comp]
      have e₃ : sp (cur (Sq A N₁) P M) ≫ sp (mr (P × M) (sMap u)) =
          sp (mr M (mr P (sMap u))) ≫ sp (cur (Sq A N) P M) := by
        rw [← sp_comp, ← cur_natural, sp_comp]
      refine (gI_1 _).trans ?_
      rw [← Category.assoc (sp (avgSnd (ph (A := A) N₁ P))) (sp (avgN (M := M) u P)), e₂, Category.assoc, gI_1, L.map_val, ← Category.assoc, e₃,
        Category.assoc]
    · have e₁ : (avgFst (ph (A := A) N₁ P)).comp (avgN (M := M) u P) = avgFst _ := rfl
      have e₂ : sp (avgFst (ph (A := A) N₁ P)) ≫ sp (avgN (M := M) u P) = sp (avgFst _) := by
        rw [← sp_comp, e₁]
      refine (gI_2 _).trans ?_
      rw [← Category.assoc (sp (avgFst (ph (A := A) N₁ P))) (sp (avgN (M := M) u P)), e₂, gI_2]
  have e₂ : (avgInt _ (ph_sq N₁)).comp (avgN (M := M) u P) = (mr P (sMap u)).comp (avgInt _ (ph_sq N)) := by
    refine RingHom.ext fun t => ?_
    change (mr M (mr P (sMap u)) (avgSnd _ t)).coeff 0 = mr P (sMap u) ((avgSnd _ t).coeff 0)
    rw [coeff_mr]
  rw [L.int_val, e, ← Category.assoc, ← sp_comp, e₂, sp_comp, L.map_val, L.int_val, Category.assoc]

lemma L.int_add (x y : L f a N (P × M)) : L.int (x + y) = L.int x + L.int y := by
  have e : L.pair (L.int x) (L.int y) = L.int (L.pair x y) := by
    refine L.pair_eq ?_ ?_
    · rw [← L.int_map, L.map_fst_pair]
    · rw [← L.int_map, L.map_snd_pair]
  rw [L.add_def, L.add_def, e, L.int_map]

/-- `∫ x(p) = x` on elements not depending on the last variable. -/
lemma cur_md_inl (W : Type u) [CommRing W] (P M : Type u) [AddCommGroup P] [AddCommGroup M] :
    (cur W P M).comp (md W (ι₁ P M)) = cs _ M := by
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, md_cs, cur_cs]
  · simp only [RingHom.comp_apply]
    rw [md_single, cur_of]
    rfl

lemma L.int_inl (x : L f a N P) : L.int (x.mapP (ι₁ P M)) = x := by
  refine L.ext' ?_
  obtain ⟨l, hl₁, hl₂⟩ := x
  have hc := cur_md_inl (Sq A N) P M
  have h₁ : sp (avgSnd (ph (A := A) N P)) ≫ sp (avgCst (M := M) (ph (A := A) N P)) = sp (cs _ M) :=
    (sp_comp _ _).symm.trans (congrArg sp (avgSnd_cst _))
  have h₁' : sp (avgFst (M := M) (ph (A := A) N P)) ≫ sp (avgCst (M := M) (ph (A := A) N P)) = sp (ph (A := A) N P) :=
    (sp_comp _ _).symm.trans (congrArg sp (avgFst_cst _))
  have h₂ : sp (cur (Sq A N) P M) ≫ sp (md (Sq A N) (ι₁ P M)) = sp (cs _ M) :=
    (sp_comp _ _).symm.trans (congrArg sp hc)
  have e : gI (L.mapP (ι₁ P M) (⟨l, hl₁, hl₂⟩ : L f a N P)) = sp (avgCst (M := M) (ph (A := A) N P)) ≫ l := by
    refine avg_ext ?_ ?_
    · refine (gI_1 _).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ l) (h₂.trans h₁.symm)).trans (Category.assoc _ _ _))
    · refine (gI_2 _).trans ?_
      exact hl₁.symm.trans ((congrArg (· ≫ l) h₁'.symm).trans (Category.assoc _ _ _))
  have h₃ : sp (avgInt (M := M) (ph (A := A) N P) (ph_sq N)) ≫ sp (avgCst (M := M) (ph (A := A) N P)) = 𝟙 _ :=
    (sp_comp _ _).symm.trans ((congrArg sp (avgInt_cst _ _)).trans sp_id')
  refine (congrArg (sp _ ≫ ·) e).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ l) h₃).trans (Category.id_comp _))

end Int

end Act

end AlgMag.Sec10Printed
