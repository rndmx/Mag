/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10PrintedDiff

/-!
# The sheaf `P` of the printed proof on the test objects, and its difference map

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1. `Pl` is `P` on `D(P)`: morphisms
`X' ×_S D(P) → Y` over `Z` lifting `a`. `diffL b c` is `b - c`, a section of `L = Hom(a^*Ω, C)`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

variable {M : Type u} [AddCommGroup M]
variable {A₁ A : Type u} [CommRing A₁] [CommRing A] {φ : A₁ →+* A} (hs : Function.Surjective φ)
  [Module A (RingHom.ker φ)]
  (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
  (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0)
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
  (b : Spec (CommRingCat.of A₁) ⟶ Z) (φ)

variable (P : Type u) [AddCommGroup P]

/-- `P` on `D(P)`: lifts over `Z` of `a`. -/
def Pl : Type u :=
  {l : Spec (CommRingCat.of (AddMonoidAlgebra A₁ P)) ⟶ Y //
    sp (mr P φ) ≫ l = sp (cs A P) ≫ a ∧ l ≫ f = sp (cs A₁ P) ≫ b}

variable {φ f a b P}
variable {P₁ : Type u} [AddCommGroup P₁]

lemma Pl.ext' {x y : Pl φ f a b P} (h : x.1 = y.1) : x = y := Subtype.ext h

lemma sp_cs_map {W W₁ : Type u} [CommRing W] [CommRing W₁] (w : W →+* W₁) {T : Scheme.{u}}
    (x : Spec (CommRingCat.of W) ⟶ T) :
    sp (mr P w) ≫ sp (cs W P) ≫ x = sp (cs W₁ P) ≫ sp w ≫ x := by
  rw [← Category.assoc, ← sp_comp, mr_cs, sp_comp, Category.assoc]

lemma sp_md_mr {W W₁ : Type u} [CommRing W] [CommRing W₁] (w : W →+* W₁) (u : P →+ P₁) {T : Scheme.{u}}
    (x : Spec (CommRingCat.of (AddMonoidAlgebra W P)) ⟶ T) :
    sp (md W₁ u) ≫ sp (mr P w) ≫ x = sp (mr P₁ w) ≫ sp (md W u) ≫ x := by
  rw [← Category.assoc, ← sp_comp, ← mr_md, sp_comp, Category.assoc]

lemma sp_md_cs {W : Type u} [CommRing W] (u : P →+ P₁) {T : Scheme.{u}}
    (x : Spec (CommRingCat.of W) ⟶ T) : sp (md W u) ≫ sp (cs W P) ≫ x = sp (cs W P₁) ≫ x := by
  rw [← Category.assoc, ← sp_comp, md_cs]

/-- Change of test object for `P`. -/
noncomputable def Pl.mapP (u : P →+ P₁) (x : Pl φ f a b P) : Pl φ f a b P₁ :=
  ⟨sp (md A₁ u) ≫ x.1, by
    rw [← Category.assoc, ← sp_comp, mr_md, sp_comp, Category.assoc, x.2.1, sp_md_cs], by
    rw [Category.assoc, x.2.2, sp_md_cs]⟩

lemma Pl.mapP_val (u : P →+ P₁) (x : Pl φ f a b P) : (x.mapP u).1 = sp (md A₁ u) ≫ x.1 := rfl

lemma md_comp {W P₂ : Type u} [CommRing W] [AddCommGroup P₂] (u : P →+ P₁) (v : P₁ →+ P₂) :
    (md W v).comp (md W u) = md W (v.comp u) := by
  refine rh_ext ?_ fun k => ?_
  · rw [RingHom.comp_assoc, md_cs, md_cs, md_cs]
  · simp only [RingHom.comp_apply]
    rw [md_single, md_single, md_single]
    rfl

lemma md_id {W : Type u} [CommRing W] : md W (AddMonoidHom.id P) = RingHom.id _ := by
  refine rh_ext ?_ fun k => ?_
  · exact md_cs _
  · rw [md_single]; rfl

/-- Change of test object for `L`. -/
noncomputable def L.mapP {N : Type u} [AddCommGroup N] [Module A N] (u : P →+ P₁) (x : L f a N P) :
    L f a N P₁ :=
  ⟨sp (md (Sq A N) u) ≫ x.1, by
    rw [← Category.assoc, ← sp_comp, mr_md, sp_comp, Category.assoc, x.2.1, sp_md_cs], by
    rw [Category.assoc, x.2.2, sp_md_mr, sp_md_cs]⟩

lemma L.mapP_val {N : Type u} [AddCommGroup N] [Module A N] (u : P →+ P₁) (x : L f a N P) :
    (x.mapP u).1 = sp (md (Sq A N) u) ≫ x.1 := rfl

lemma L.mapP_map {N N₁ : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]
    (u : P →+ P₁) (v : N →ₗ[A] N₁) (x : L f a N P) : (x.map v).mapP u = (x.mapP u).map v :=
  L.ext' (sp_md_mr _ u x.1)

lemma L.mapP_pair {N N₁ : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]
    (u : P →+ P₁) (x : L f a N P) (y : L f a N₁ P) :
    (L.pair x y).mapP u = L.pair (x.mapP u) (y.mapP u) := by
  symm
  refine L.pair_eq ?_ ?_
  · rw [← L.mapP_map, L.map_fst_pair]
  · rw [← L.mapP_map, L.map_snd_pair]

lemma L.mapP_add {N : Type u} [AddCommGroup N] [Module A N] (u : P →+ P₁) (x y : L f a N P) :
    (x + y).mapP u = x.mapP u + y.mapP u := by
  rw [L.add_def, L.add_def, L.mapP_map, L.mapP_pair]

/-- `mapP` as an additive map. -/
noncomputable def L.mapPHom {N : Type u} [AddCommGroup N] [Module A N] (u : P →+ P₁) :
    L f a N P →+ L f a N P₁ :=
  AddMonoidHom.mk' (L.mapP u) (L.mapP_add u)

section Glue

variable (x y : Pl φ f a b P)

/-- `(b, c)` on `Spec (A₁ ×_A A₁)[P]`. -/
noncomputable def gD (hs : Function.Surjective φ) (x y : Pl φ f a b P) :
    Spec (CommRingCat.of (AddMonoidAlgebra (Dd φ) P)) ⟶ Y :=
  gl (milnor_map (milnor_D φ hs) P) (mr_surjective _ (d₂_surj φ)) x.1 y.1 (x.2.1.trans y.2.1.symm)

lemma gD_1 (hs : Function.Surjective φ) (x y : Pl φ f a b P) : sp (mr P (d₁ φ)) ≫ gD hs x y = x.1 :=
  gl_p (milnor_map (milnor_D φ hs) P) _ _ _ _

lemma gD_2 (hs : Function.Surjective φ) (x y : Pl φ f a b P) : sp (mr P (d₂ φ)) ≫ gD hs x y = y.1 :=
  gl_q (milnor_map (milnor_D φ hs) P) _ _ _ _

lemma gD_ext (hs : Function.Surjective φ) {T : Scheme.{u}}
    {r s : Spec (CommRingCat.of (AddMonoidAlgebra (Dd φ) P)) ⟶ T}
    (h₁ : sp (mr P (d₁ φ)) ≫ r = sp (mr P (d₁ φ)) ≫ s) (h₂ : sp (mr P (d₂ φ)) ≫ r = sp (mr P (d₂ φ)) ≫ s) :
    r = s := milnor_ext (milnor_map (milnor_D φ hs) P) h₁ h₂

lemma gD_f (hs : Function.Surjective φ) (x y : Pl φ f a b P) :
    gD hs x y ≫ f = sp (mr P (dΔ φ)) ≫ sp (cs A₁ P) ≫ b := by
  refine gD_ext hs ?_ ?_
  · rw [← Category.assoc, gD_1, x.2.2, sp_mr_assoc, d₁_Δ, mr_id, sp_id', Category.id_comp]
  · rw [← Category.assoc, gD_2, y.2.2, sp_mr_assoc, d₂_Δ, mr_id, sp_id', Category.id_comp]

variable (w : a ≫ f = sp φ ≫ b)

/-- **The difference** `b - c`. -/
noncomputable def diffL (hs : Function.Surjective φ)
    (hN : ∀ (x : A₁) (n : RingHom.ker φ), ((φ x • n : RingHom.ker φ) : A₁) = x * n)
    (hq : ∀ x y, φ x = 0 → φ y = 0 → x * y = 0) (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) :
    L f a (RingHom.ker φ) P :=
  ⟨sp (mr P (qq hN hq)) ≫ gD hs x y, by
    rw [sp_mr_assoc, sFst_qq, ← sp_mr_assoc, gD_1]
    exact x.2.1, by
    rw [Category.assoc, gD_f, sp_mr_assoc, qq_Δ, ← sp_mr_assoc, sp_cs_map, w]⟩

lemma diffL_val (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) :
    (diffL hs hN hq w x y).1 = sp (mr P (qq hN hq)) ≫ gD hs x y := rfl

/-- `(b, c, d)` on the triple product. -/
noncomputable def gT (x y z : Pl φ f a b P) :
    Spec (CommRingCat.of (AddMonoidAlgebra (Dt (φ := φ)) P)) ⟶ Y :=
  gl (milnor_map milnor_t P) (mr_surjective _ t₂_surj) (gD hs x y) (gD hs y z) (by
    rw [gD_2, gD_1])

lemma gT_1 (x y z : Pl φ f a b P) : sp (mr P (t₁ (φ := φ))) ≫ gT hs x y z = gD hs x y :=
  gl_p (milnor_map milnor_t P) _ _ _ _
lemma gT_2 (x y z : Pl φ f a b P) : sp (mr P (t₂ (φ := φ))) ≫ gT hs x y z = gD hs y z :=
  gl_q (milnor_map milnor_t P) _ _ _ _

lemma gT_t (x y z : Pl φ f a b P) : sp (mr P (tt (φ := φ))) ≫ gT hs x y z = gD hs x z := by
  refine gD_ext hs ?_ ?_
  · rw [sp_mr_assoc, d₁_tt, ← sp_mr_assoc, gT_1, gD_1, gD_1]
  · rw [sp_mr_assoc, d₂_tt, ← sp_mr_assoc, gT_2, gD_2, gD_2]

/-- `(b - c) + (c - d) = b - d`. -/
theorem diffL_add (w : a ≫ f = sp φ ≫ b) (x y z : Pl φ f a b P) :
    diffL hs hN hq w x y + diffL hs hN hq w y z = diffL hs hN hq w x z := by
  have h₁ : sp (mr P (sMap (LinearMap.fst A (RingHom.ker φ) (RingHom.ker φ)))) ≫ sp (mr P (q₃ hN hq)) ≫
      gT hs x y z = (diffL hs hN hq w x y).1 := by
    rw [sp_mr_assoc, fst_q₃, ← sp_mr_assoc, gT_1]
    rfl
  have h₂ : sp (mr P (sMap (LinearMap.snd A (RingHom.ker φ) (RingHom.ker φ)))) ≫ sp (mr P (q₃ hN hq)) ≫
      gT hs x y z = (diffL hs hN hq w y z).1 := by
    rw [sp_mr_assoc, snd_q₃, ← sp_mr_assoc, gT_2]
    rfl
  let t : L f a (RingHom.ker φ × RingHom.ker φ) P :=
    ⟨sp (mr P (q₃ hN hq)) ≫ gT hs x y z, by
      have e : sFst (A := A) (RingHom.ker φ × RingHom.ker φ) =
          (sFst (RingHom.ker φ)).comp (sMap (LinearMap.fst A _ _)) := (sFst_map _).symm
      rw [e, ← sp_mr_assoc, h₁]
      exact (diffL hs hN hq w x y).2.1, by
      refine milnor_ext (milnor_map milnor_prod P) ?_ ?_
      · refine (Category.assoc _ _ _).symm.trans ?_
        rw [h₁, L.sp_inl_map]
        exact (diffL hs hN hq w x y).2.2
      · refine (Category.assoc _ _ _).symm.trans ?_
        rw [h₂, L.sp_inl_map]
        exact (diffL hs hN hq w y z).2.2⟩
  have e : L.pair (diffL hs hN hq w x y) (diffL hs hN hq w y z) = t := by
    exact L.pair_eq (L.ext' h₁) (L.ext' h₂)
  rw [L.add_def, e]
  refine L.ext' ?_
  change sp _ ≫ sp _ ≫ _ = _
  rw [sp_mr_assoc, add_q₃, ← sp_mr_assoc, gT_t]
  rfl

/-- `(c, v)` on `Spec (A₁ ×_A A[N])[P]`. -/
noncomputable def gA (x : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    Spec (CommRingCat.of (AddMonoidAlgebra (Da (φ := φ)) P)) ⟶ Y :=
  gl (milnor_map (milnor_a hs) P) (mr_surjective _ (a₂_surj hs)) x.1 v.1 (x.2.1.trans v.2.1.symm)

lemma gA_1 (x : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    sp (mr P (a₁ (φ := φ))) ≫ gA hs x v = x.1 := gl_p (milnor_map (milnor_a hs) P) _ _ _ _
lemma gA_2 (x : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    sp (mr P (a₂ (φ := φ))) ≫ gA hs x v = v.1 := gl_q (milnor_map (milnor_a hs) P) _ _ _ _

/-- `x ↦ (x, inl (φ x))`. -/
noncomputable def aΔ : A₁ →+* Da (φ := φ) :=
  RingHom.codRestrict ((RingHom.id A₁).prod ((sInl _).comp φ)) _ (fun _ => rfl)

lemma ss_aΔ : (ss hN hq).comp (aΔ (φ := φ)) = RingHom.id _ :=
  RingHom.ext fun x => by
    change x + ((0 : RingHom.ker φ) : A₁) = x
    simp

/-- **The sum** `c + v`. -/
noncomputable def addL (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    Pl φ f a b P :=
  ⟨sp (mr P (ss hN hq)) ≫ gA hs x v, by
    rw [sp_mr_assoc, φ_ss, ← sp_mr_assoc, gA_1]
    exact x.2.1, by
    have e : gA hs x v ≫ f = sp (mr P (aΔ (φ := φ))) ≫ sp (cs A₁ P) ≫ b := by
      refine milnor_ext (milnor_map (milnor_a hs) P) ?_ ?_
      · rw [← Category.assoc, gA_1, x.2.2, sp_mr_assoc]
        have : (a₁ (φ := φ)).comp (aΔ (φ := φ)) = RingHom.id _ := rfl
        rw [this, mr_id, sp_id', Category.id_comp]
      · rw [← Category.assoc, gA_2, v.2.2, sp_mr_assoc]
        have : (a₂ (φ := φ)).comp (aΔ (φ := φ)) = (sInl _).comp φ := rfl
        rw [this, ← sp_mr_assoc, sp_cs_map φ b, w]
    rw [Category.assoc, e, sp_mr_assoc, ss_aΔ, mr_id, sp_id', Category.id_comp]⟩

lemma addL_val (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    (addL hs hN hq w x v).1 = sp (mr P (ss hN hq)) ≫ gA hs x v := rfl

/-- `c + (b - c) = b`. -/
lemma addL_diffL (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) :
    addL hs hN hq w y (diffL hs hN hq w x y) = x := by
  refine Pl.ext' ?_
  have e : gA hs y (diffL hs hN hq w x y) = sp (mr P (nn hN hq)) ≫ gD hs x y := by
    refine milnor_ext (milnor_map (milnor_a hs) P) ?_ ?_
    · rw [gA_1, sp_mr_assoc, a₁_nn, gD_2]
    · rw [gA_2, sp_mr_assoc, a₂_nn]
      rfl
  rw [addL_val, e, sp_mr_assoc, ss_nn, gD_1]

/-- `(c + v) - c = v`. -/
lemma diffL_addL (w : a ≫ f = sp φ ≫ b) (y : Pl φ f a b P) (v : L f a (RingHom.ker φ) P) :
    diffL hs hN hq w (addL hs hN hq w y v) y = v := by
  refine L.ext' ?_
  have e : gD hs (addL hs hN hq w y v) y = sp (mr P (mm hN hq)) ≫ gA hs y v := by
    refine gD_ext hs ?_ ?_
    · rw [gD_1, sp_mr_assoc, d₁_mm]
      rfl
    · rw [gD_2, sp_mr_assoc, d₂_mm, gA_1]
  rw [diffL_val, e, sp_mr_assoc, qq_mm, gA_2]

lemma diffL_self (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) : diffL hs hN hq w x x = 0 :=
  left_eq_add.mp (diffL_add hs hN hq w x x x).symm

lemma addL_zero (w : a ≫ f = sp φ ≫ b) (x : Pl φ f a b P) : addL hs hN hq w x 0 = x := by
  have := addL_diffL hs hN hq w x x
  rwa [diffL_self] at this

lemma Pl_eq_of_diffL (w : a ≫ f = sp φ ≫ b) (x y : Pl φ f a b P) (h : diffL hs hN hq w x y = 0) :
    x = y := by
  have := addL_diffL hs hN hq w x y
  rw [h, addL_zero] at this
  exact this.symm

lemma diffL_mapP (w : a ≫ f = sp φ ≫ b) (u : P →+ P₁) (x y : Pl φ f a b P) :
    diffL hs hN hq w (x.mapP u) (y.mapP u) = (diffL hs hN hq w x y).mapP u := by
  refine L.ext' ?_
  have e : gD hs (x.mapP u) (y.mapP u) = sp (md (Dd φ) u) ≫ gD hs x y := by
    refine gD_ext hs ?_ ?_
    · rw [gD_1, ← Category.assoc, ← sp_comp, mr_md, sp_comp, Category.assoc, gD_1]
      rfl
    · rw [gD_2, ← Category.assoc, ← sp_comp, mr_md, sp_comp, Category.assoc, gD_2]
      rfl
  rw [diffL_val, e, L.mapP_val, diffL_val]
  exact (sp_md_mr _ u _).symm

end Glue

end AlgMag.Sec10Printed
