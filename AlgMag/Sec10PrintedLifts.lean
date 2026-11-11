/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec10LiftsCore
import AlgMag.Sec10PrintedCore
import StacksFrontier.AlgebraicGeometry.Smooth.SqZeroAlgebra

/-!
# The sections of `p_* Hom(a^*Ω, C)`, as lifts

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1. A section of `Hom(a^*Ω_{Y/Z}, N)` over the
test object `D(P)` is a morphism `Spec (A[N])[P] → Y` over `Z` extending `a`, where `A[N]` is the
trivial square zero extension. The group law comes from the Milnor square `A[N × N']`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgMag.Sec10Printed

open AlgMag.GB AlgMag.Lifts

attribute [local instance] Stacks.Smooth.moduleMulOpposite

section Rings

variable {R' B C D : Type u} [CommRing R'] [CommRing B] [CommRing C] [CommRing D]

/-- `R[P]` on ring maps. -/
noncomputable abbrev mr (P : Type u) [AddCommMonoid P] {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) : AddMonoidAlgebra R P →+* AddMonoidAlgebra S P :=
  AddMonoidAlgebra.mapRingHom P g

/-- The constants. -/
noncomputable abbrev cs (R : Type u) [CommRing R] (P : Type u) [AddCommMonoid P] :
    R →+* AddMonoidAlgebra R P := AddMonoidAlgebra.singleZeroRingHom

/-- `R[P] → R[P']`. -/
noncomputable abbrev md {P P' : Type u} [AddCommMonoid P] [AddCommMonoid P'] (R : Type u)
    [CommRing R] (h : P →+ P') : AddMonoidAlgebra R P →+* AddMonoidAlgebra R P' :=
  AddMonoidAlgebra.mapDomainRingHom R h

variable {P : Type u} [AddCommMonoid P]

lemma coeff_mr {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (x : AddMonoidAlgebra R P)
    (k : P) : (mr P g x).coeff k = g (x.coeff k) := by
  simp [AddMonoidAlgebra.coeff_mapRingHom]

lemma mr_single {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (k : P) (r : R) :
    mr P g (AddMonoidAlgebra.single k r) = AddMonoidAlgebra.single k (g r) :=
  AddMonoidAlgebra.mapRingHom_single _ _ _

lemma mr_comp {R S W : Type u} [CommRing R] [CommRing S] [CommRing W] (g : S →+* W) (h : R →+* S) :
    (mr P g).comp (mr P h) = mr P (g.comp h) :=
  RingHom.ext fun x => AddMonoidAlgebra.ext (Finsupp.ext fun k => by
    rw [RingHom.comp_apply, coeff_mr, coeff_mr, coeff_mr]; rfl)

lemma mr_id {R : Type u} [CommRing R] : mr P (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => AddMonoidAlgebra.ext (Finsupp.ext fun k => by
    rw [coeff_mr]; rfl)

lemma sp_mr {R S W : Type u} [CommRing R] [CommRing S] [CommRing W] (g : S →+* W) (h : R →+* S) :
    sp (mr P g) ≫ sp (mr P h) = sp (mr P (g.comp h)) := by
  rw [← sp_comp, mr_comp]

lemma mr_surjective {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S)
    (hs : Function.Surjective g) : Function.Surjective (mr P g) := by
  intro y
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨p₁, rfl⟩ := hp
    obtain ⟨q₁, rfl⟩ := hq
    exact ⟨p₁ + q₁, map_add _ _ _⟩
  | single n r =>
    obtain ⟨s, rfl⟩ := hs r
    exact ⟨AddMonoidAlgebra.single n s, mr_single _ _ _⟩

variable {p : R' →+* B} {q : R' →+* C} {i : B →+* D} {j : C →+* D}

/-- A Milnor square stays one after `(-)[P]`. -/
theorem milnor_map (H : MilnorData p q i j) (P : Type u) [AddCommMonoid P] :
    MilnorData (mr P p) (mr P q) (mr P i) (mr P j) where
  comm z := by
    ext k
    simp only [coeff_mr, H.comm]
  surj := mr_surjective i H.surj
  inj z h₁ h₂ := by
    ext k
    have e₁ : p (z.coeff k) = 0 := by simpa [coeff_mr] using congrArg (fun w => w.coeff k) h₁
    have e₂ : q (z.coeff k) = 0 := by simpa [coeff_mr] using congrArg (fun w => w.coeff k) h₂
    simpa using congrArg (fun w => w) (H.inj _ e₁ e₂)
  ex x y h := by
    classical
    have hc : ∀ k, i (x.coeff k) = j (y.coeff k) := fun k => by
      simpa [coeff_mr] using congrArg (fun w => w.coeff k) h
    choose z hz₁ hz₂ using fun k => H.ex _ _ (hc k)
    let z' : P → R' := fun k => if x.coeff k = 0 ∧ y.coeff k = 0 then 0 else z k
    have hz'₁ : ∀ k, p (z' k) = x.coeff k := fun k => by
      by_cases h0 : x.coeff k = 0 ∧ y.coeff k = 0
      · simp [z', h0]
      · simp [z', h0, hz₁]
    have hz'₂ : ∀ k, q (z' k) = y.coeff k := fun k => by
      by_cases h0 : x.coeff k = 0 ∧ y.coeff k = 0
      · simp [z', h0]
      · simp [z', h0, hz₂]
    let w : P →₀ R' := Finsupp.onFinset (x.coeff.support ∪ y.coeff.support) z' (fun k hk => by
      by_contra hn
      simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hn
      exact hk (by simp [z', hn.1, hn.2]))
    refine ⟨AddMonoidAlgebra.ofCoeff w, ?_, ?_⟩
    · ext k
      rw [coeff_mr]
      exact hz'₁ k
    · ext k
      rw [coeff_mr]
      exact hz'₂ k

/-- The kernel condition of `milnor_desc`, from the square. -/
lemma hker' (H : MilnorData p q i j) (y : B) (hy : i y = 0) : ∃ z, p z = y ∧ q z = 0 :=
  H.ex y 0 (by rw [hy, map_zero])

/-- The glued morphism of a Milnor square. -/
noncomputable def gl {Y : Scheme.{u}} (H : MilnorData p q i j) (hq : Function.Surjective q)
    (f : Spec (CommRingCat.of B) ⟶ Y) (g : Spec (CommRingCat.of C) ⟶ Y)
    (hs : sp i ≫ f = sp j ≫ g) : Spec (CommRingCat.of R') ⟶ Y :=
  (milnor_desc H hq (hker' H) f g hs).choose

lemma gl_p {Y : Scheme.{u}} (H : MilnorData p q i j) (hq : Function.Surjective q)
    (f : Spec (CommRingCat.of B) ⟶ Y) (g : Spec (CommRingCat.of C) ⟶ Y)
    (hs : sp i ≫ f = sp j ≫ g) : sp p ≫ gl H hq f g hs = f :=
  (milnor_desc H hq (hker' H) f g hs).choose_spec.1.1

lemma gl_q {Y : Scheme.{u}} (H : MilnorData p q i j) (hq : Function.Surjective q)
    (f : Spec (CommRingCat.of B) ⟶ Y) (g : Spec (CommRingCat.of C) ⟶ Y)
    (hs : sp i ≫ f = sp j ≫ g) : sp q ≫ gl H hq f g hs = g :=
  (milnor_desc H hq (hker' H) f g hs).choose_spec.1.2

end Rings

section Sq

variable {A : Type u} [CommRing A]

/-- `A[N]`. -/
abbrev Sq (A : Type u) [CommRing A] (N : Type u) [AddCommGroup N] [Module A N] := TrivSqZeroExt A N

/-- All ring maps of `A[N]` are stated for the structure coming from `CommRing`; unifying it with the
direct `TrivSqZeroExt.nonAssocSemiring` is otherwise very slow. -/
@[reducible] noncomputable instance (priority := 2000) sqNAS (A : Type u) [CommRing A] (N : Type u)
    [AddCommGroup N] [Module A N] : NonAssocSemiring (TrivSqZeroExt A N) :=
  (inferInstance : CommRing (TrivSqZeroExt A N)).toCommSemiring.toNonAssocSemiring

variable (N N₁ N₂ : Type u) [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂]

/-- `A[N] → A`. -/
noncomputable def sFst : Sq A N →+* A where
  toFun := TrivSqZeroExt.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `A → A[N]`. -/
noncomputable def sInl : A →+* Sq A N where
  toFun := TrivSqZeroExt.inl
  map_one' := rfl
  map_mul' := TrivSqZeroExt.inl_mul N
  map_zero' := TrivSqZeroExt.inl_zero N
  map_add' := TrivSqZeroExt.inl_add N

variable {N N₁ N₂}

/-- `A[N] → A[N₁]`. -/
noncomputable def sMap (u : N →ₗ[A] N₁) : Sq A N →+* Sq A N₁ :=
  Stacks.Smooth.sqZeroMap (RingHom.id A) u.toAddMonoidHom (fun r m => u.map_smul r m)

@[simp] lemma sMap_fst (u : N →ₗ[A] N₁) (x : Sq A N) : (sMap u x).fst = x.fst :=
  Stacks.Smooth.sqZeroMap_fst _ _ _ x
@[simp] lemma sMap_snd (u : N →ₗ[A] N₁) (x : Sq A N) : (sMap u x).snd = u x.snd :=
  Stacks.Smooth.sqZeroMap_snd _ _ _ x
@[simp] lemma sFst_apply (x : Sq A N) : sFst N x = x.fst := rfl
@[simp] lemma sInl_fst (r : A) : (sInl N r).fst = r := rfl
@[simp] lemma sInl_snd (r : A) : (sInl N r).snd = 0 := rfl

lemma sq_ext {x y : Sq A N} (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  TrivSqZeroExt.ext h₁ h₂

lemma sMap_comp (u : N →ₗ[A] N₁) (v : N₁ →ₗ[A] N₂) : (sMap v).comp (sMap u) = sMap (v ∘ₗ u) :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp)

lemma sMap_id : sMap (LinearMap.id : N →ₗ[A] N) = RingHom.id _ :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp)

lemma sFst_map (u : N →ₗ[A] N₁) : (sFst N₁).comp (sMap u) = sFst N :=
  RingHom.ext fun _ => by simp

lemma sMap_inl (u : N →ₗ[A] N₁) : (sMap u).comp (sInl N) = sInl N₁ :=
  RingHom.ext fun _ => sq_ext (by simp) (by simp)

lemma sFst_inl : (sFst N).comp (sInl N) = RingHom.id A := RingHom.ext fun _ => rfl

lemma sFst_surjective : Function.Surjective (sFst (A := A) N) := fun r => ⟨sInl N r, rfl⟩

/-- The Milnor square of `A[N × N₁]`. -/
theorem milnor_prod : MilnorData (sMap (LinearMap.fst A N N₁)) (sMap (LinearMap.snd A N N₁))
    (sFst N) (sFst N₁) where
  comm z := by simp
  surj := sFst_surjective
  inj z h₁ h₂ := by
    have e₁ := congrArg TrivSqZeroExt.snd h₁
    have e₂ := congrArg TrivSqZeroExt.snd h₂
    have e₃ := congrArg TrivSqZeroExt.fst h₁
    simp only [sMap_snd, sMap_fst, TrivSqZeroExt.snd_zero, TrivSqZeroExt.fst_zero] at e₁ e₂ e₃
    exact sq_ext e₃ (Prod.ext e₁ e₂)
  ex x y h := by
    refine ⟨TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (x.snd, y.snd), sq_ext ?_ ?_, sq_ext ?_ ?_⟩
    · simp
    · simp
    · simpa using h
    · simp

end Sq

section L

variable {A : Type u} [CommRing A] {Y Z : Scheme.{u}} (f : Y ⟶ Z) (a : Spec (CommRingCat.of A) ⟶ Y)
variable (N N₁ N₂ N₃ : Type u) [AddCommGroup N] [Module A N] [AddCommGroup N₁] [Module A N₁]
  [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃]
variable (P : Type u) [AddCommMonoid P]

/-- The sections over `D(P)` of `Hom(a^*Ω_{Y/Z}, N)`: lifts `Spec A[N][P] → Y` over `Z` of `a`. -/
def L : Type u :=
  {l : Spec (CommRingCat.of (AddMonoidAlgebra (Sq A N) P)) ⟶ Y //
    sp (mr P (sFst N)) ≫ l = sp (cs A P) ≫ a ∧
      l ≫ f = sp (mr P (sInl N)) ≫ sp (cs A P) ≫ a ≫ f}

variable {f a N N₁ N₂ N₃ P}

namespace L

lemma ext' {x y : L f a N P} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- Functoriality in `N`. -/
noncomputable def map (u : N →ₗ[A] N₁) (x : L f a N P) : L f a N₁ P :=
  ⟨sp (mr P (sMap u)) ≫ x.1, by
    rw [← Category.assoc, sp_mr, sFst_map]; exact x.2.1, by
    rw [Category.assoc, x.2.2, ← Category.assoc, sp_mr, sMap_inl]⟩

lemma map_val (u : N →ₗ[A] N₁) (x : L f a N P) : (x.map u).1 = sp (mr P (sMap u)) ≫ x.1 := rfl

lemma map_map (u : N →ₗ[A] N₁) (v : N₁ →ₗ[A] N₂) (x : L f a N P) :
    (x.map u).map v = x.map (v ∘ₗ u) := by
  refine ext' ?_
  simp only [map_val]
  rw [← Category.assoc, sp_mr, sMap_comp]

lemma map_id (x : L f a N P) : x.map LinearMap.id = x := by
  refine ext' ?_
  rw [map_val, sMap_id, mr_id, sp_id', Category.id_comp]

/-- The zero section. -/
noncomputable def zero : L f a N P :=
  ⟨sp (mr P (sInl N)) ≫ sp (cs A P) ≫ a, by
    rw [← Category.assoc, sp_mr, sFst_inl, mr_id, sp_id', Category.id_comp], by
    simp only [Category.assoc]⟩

lemma map_zero' (u : N →ₗ[A] N₁) : (zero : L f a N P).map u = zero := by
  refine ext' ?_
  change sp (mr P (sMap u)) ≫ sp (mr P (sInl N)) ≫ sp (cs A P) ≫ a = sp (mr P (sInl N₁)) ≫ sp (cs A P) ≫ a
  rw [← Category.assoc, sp_mr, sMap_inl]

lemma map_zero_hom (x : L f a N P) : x.map (0 : N →ₗ[A] N₁) = zero := by
  refine ext' ?_
  have e : sMap (0 : N →ₗ[A] N₁) = (sInl N₁).comp (sFst N) :=
    RingHom.ext fun _ => sq_ext (by simp) (by simp)
  rw [map_val, e, ← sp_mr, Category.assoc, x.2.1]
  rfl

lemma hsMilnor (x : L f a N P) (y : L f a N₁ P) :
    sp (mr P (sFst N)) ≫ x.1 = sp (mr P (sFst N₁)) ≫ y.1 := x.2.1.trans y.2.1.symm

lemma sp_inl_map (u : N →ₗ[A] N₁) {W : Scheme.{u}}
    (w : Spec (CommRingCat.of (AddMonoidAlgebra A P)) ⟶ W) :
    sp (mr P (sMap u)) ≫ sp (mr P (sInl N)) ≫ w = sp (mr P (sInl N₁)) ≫ w := by
  rw [← Category.assoc, sp_mr, sMap_inl]

lemma sSnd_surj : Function.Surjective (sMap (LinearMap.snd A N N₁)) := fun y =>
  ⟨TrivSqZeroExt.inl y.fst + TrivSqZeroExt.inr (0, y.snd), sq_ext (by simp) (by simp)⟩

/-- The pair: `L` preserves products. -/
noncomputable def pair (x : L f a N P) (y : L f a N₁ P) : L f a (N × N₁) P :=
  ⟨gl (milnor_map milnor_prod P) (mr_surjective _ sSnd_surj) x.1 y.1 (hsMilnor x y), by
    have e : (sFst (A := A) (N × N₁)) = (sFst N).comp (sMap (LinearMap.fst A N N₁)) := (sFst_map _).symm
    rw [e, ← sp_mr, Category.assoc, gl_p]
    exact x.2.1, by
    refine milnor_ext (milnor_map milnor_prod P) ?_ ?_
    · rw [sp_inl_map, ← Category.assoc, gl_p, x.2.2]
    · rw [sp_inl_map, ← Category.assoc, gl_q, y.2.2]⟩

lemma map_fst_pair (x : L f a N P) (y : L f a N₁ P) :
    (pair x y).map (LinearMap.fst A N N₁) = x := ext' (gl_p (milnor_map milnor_prod P) (mr_surjective _ sSnd_surj) x.1 y.1 (hsMilnor x y))

lemma map_snd_pair (x : L f a N P) (y : L f a N₁ P) :
    (pair x y).map (LinearMap.snd A N N₁) = y := ext' (gl_q (milnor_map milnor_prod P) (mr_surjective _ sSnd_surj) x.1 y.1 (hsMilnor x y))

lemma prod_ext {x y : L f a (N × N₁) P}
    (h₁ : x.map (LinearMap.fst A N N₁) = y.map (LinearMap.fst A N N₁))
    (h₂ : x.map (LinearMap.snd A N N₁) = y.map (LinearMap.snd A N N₁)) : x = y :=
  ext' (milnor_ext (milnor_map milnor_prod P) (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

lemma pair_eq {x : L f a N P} {y : L f a N₁ P} {z : L f a (N × N₁) P}
    (h₁ : z.map (LinearMap.fst A N N₁) = x) (h₂ : z.map (LinearMap.snd A N N₁) = y) : pair x y = z :=
  prod_ext ((map_fst_pair x y).trans h₁.symm) ((map_snd_pair x y).trans h₂.symm)

/-- The addition. -/
noncomputable def add' (x y : L f a N P) : L f a N P :=
  (pair x y).map (LinearMap.fst A N N + LinearMap.snd A N N)

lemma map_pair (u : N →ₗ[A] N₂) (v : N₁ →ₗ[A] N₃) (x : L f a N P) (y : L f a N₁ P) :
    pair (x.map u) (y.map v) = (pair x y).map (u.prodMap v) := by
  refine pair_eq ?_ ?_
  · rw [map_map, show (LinearMap.fst A N₂ N₃) ∘ₗ (u.prodMap v) = u ∘ₗ LinearMap.fst A N N₁ from rfl,
      ← map_map, map_fst_pair]
  · rw [map_map, show (LinearMap.snd A N₂ N₃) ∘ₗ (u.prodMap v) = v ∘ₗ LinearMap.snd A N N₁ from rfl,
      ← map_map, map_snd_pair]

lemma map_add' (u : N →ₗ[A] N₁) (x y : L f a N P) : (add' x y).map u = add' (x.map u) (y.map u) := by
  rw [add', add', map_pair, map_map, map_map]
  congr 1
  ext <;> simp

lemma add_comm' (x y : L f a N P) : add' x y = add' y x := by
  have e : pair y x = (pair x y).map (LinearMap.prod (LinearMap.snd A N N) (LinearMap.fst A N N)) := by
    refine pair_eq ?_ ?_
    · rw [map_map]; exact map_snd_pair x y
    · rw [map_map]; exact map_fst_pair x y
  rw [add', add', e, map_map]
  congr 1
  ext <;> simp [add_comm]

lemma add_zero' (x : L f a N P) : add' x zero = x := by
  have e : pair x (zero : L f a N P) = x.map (LinearMap.inl A N N) := by
    refine pair_eq ?_ ?_
    · rw [map_map]; exact map_id x
    · rw [map_map, show LinearMap.snd A N N ∘ₗ LinearMap.inl A N N = 0 from rfl, map_zero_hom]
  rw [add', e, map_map]
  have : (LinearMap.fst A N N + LinearMap.snd A N N) ∘ₗ LinearMap.inl A N N = LinearMap.id := by
    ext; simp
  rw [this, map_id]

lemma add_assoc' (x y z : L f a N P) : add' (add' x y) z = add' x (add' y z) := by
  let t := pair (pair x y) z
  have e₁ : pair (add' x y) z = t.map ((LinearMap.fst A N N + LinearMap.snd A N N).prodMap LinearMap.id) := by
    have := map_pair (LinearMap.fst A N N + LinearMap.snd A N N) LinearMap.id (pair x y) z
    rwa [map_id] at this
  have e₂ : pair x (add' y z) = t.map (LinearMap.prod
      (LinearMap.fst A N N ∘ₗ LinearMap.fst A (N × N) N)
      ((LinearMap.snd A N N ∘ₗ LinearMap.fst A (N × N) N) + LinearMap.snd A (N × N) N)) := by
    refine pair_eq ?_ ?_
    · rw [map_map, show LinearMap.fst A N N ∘ₗ LinearMap.prod (LinearMap.fst A N N ∘ₗ LinearMap.fst A (N × N) N)
        ((LinearMap.snd A N N ∘ₗ LinearMap.fst A (N × N) N) + LinearMap.snd A (N × N) N) =
          LinearMap.fst A N N ∘ₗ LinearMap.fst A (N × N) N from rfl, ← map_map, map_fst_pair, map_fst_pair]
    · have : pair y z = t.map (LinearMap.prod (LinearMap.snd A N N ∘ₗ LinearMap.fst A (N × N) N)
          (LinearMap.snd A (N × N) N)) := by
        refine pair_eq ?_ ?_
        · rw [map_map, show LinearMap.fst A N N ∘ₗ LinearMap.prod (LinearMap.snd A N N ∘ₗ LinearMap.fst A (N × N) N)
            (LinearMap.snd A (N × N) N) = LinearMap.snd A N N ∘ₗ LinearMap.fst A (N × N) N from rfl,
            ← map_map, map_fst_pair, map_snd_pair]
        · rw [map_map]; exact map_snd_pair _ _
      rw [map_map, add', this, map_map]
      congr 1
  change (pair (add' x y) z).map _ = (pair x (add' y z)).map _
  rw [e₁, e₂, map_map, map_map]
  congr 1
  ext <;> simp [add_assoc]

lemma neg_add' (x : L f a N P) : add' (x.map (-LinearMap.id)) x = zero := by
  have e : pair (x.map (-LinearMap.id)) x = x.map (LinearMap.prod (-LinearMap.id) LinearMap.id) := by
    refine pair_eq ?_ ?_
    · rw [map_map]; rfl
    · rw [map_map]; exact map_id x
  rw [add', e, map_map]
  have : (LinearMap.fst A N N + LinearMap.snd A N N) ∘ₗ LinearMap.prod (-LinearMap.id) LinearMap.id =
      (0 : N →ₗ[A] N) := by
    ext; simp
  rw [this, map_zero_hom]

noncomputable instance : AddCommGroup (L f a N P) :=
  letI : Add (L f a N P) := ⟨add'⟩
  letI : Zero (L f a N P) := ⟨zero⟩
  letI : Neg (L f a N P) := ⟨fun x => x.map (-LinearMap.id)⟩
  { add_assoc := add_assoc'
    zero_add := fun x => (add_comm' _ _).trans (add_zero' x)
    add_zero := add_zero'
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := neg_add'
    add_comm := add_comm' }

lemma add_def (x y : L f a N P) : x + y = (pair x y).map (LinearMap.fst A N N + LinearMap.snd A N N) := rfl
lemma zero_val : (0 : L f a N P).1 = sp (mr P (sInl N)) ≫ sp (cs A P) ≫ a := rfl
lemma map_add'' (u : N →ₗ[A] N₁) (x y : L f a N P) : (x + y).map u = x.map u + y.map u := map_add' u x y

end L

end L

end AlgMag.Sec10Printed
