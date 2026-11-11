/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec12PrintedSchemes
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Divisible

/-!
# Theorem 12.4: "Since the action is Zariski locally linearizable, we reduce to `X` affine over `S`"

The step the printed proof does not spell out: for `W ⊆ X` a stable open and `N` finitely generated,
a point of `X^N` whose image in `X^{N^×}` lies in `W` is a point of `W^N`. The paper would use Prop 5.1,
whose hypothesis includes `X` separated; for an open `W` no separation is needed (the `X` of
Theorem 12.4 is not assumed separated). The proof uses the deformation `n ↦ a(n) t^{w(n)}`, `w` the
weight of `N` of Ogus, Prop. 2.2.1.

* `exists_ext_units`: characters of a magnet extend, with divisible units.
* `mem_range_of_vertex`: the main lemma.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

section Ext

variable {M : Type u} [AddCommGroup M] {E : Type u} [CommRing E]

/-- A morphism from a magnet `N` of `M` to a group with divisible units extends to `M`. -/
theorem exists_ext_units (hdiv : ∀ (u : Eˣ) (n : ℕ), n ≠ 0 → ∃ v : Eˣ, v ^ n = u) (N : AddSubmonoid M)
    (ξ : Multiplicative N →* Eˣ) :
    ∃ χ : Multiplicative M →* Eˣ, ∀ n : N, χ (Multiplicative.ofAdd (n : M)) = ξ (Multiplicative.ofAdd n) := by
  let A := Additive Eˣ
  let dn : DivisibleBy A ℕ :=
    { div := fun a n => if h : n = 0 then 0 else Additive.ofMul (hdiv a.toMul n h).choose
      div_zero := fun a => dif_pos rfl
      div_cancel := fun {n} a hn => by
        rw [dif_neg hn]
        exact congrArg Additive.ofMul (hdiv a.toMul n hn).choose_spec }
  let dz : DivisibleBy A ℤ := AddGroup.divisibleByIntOfDivisibleByNat A
  -- `ξ` on `N` in additive form
  let x : N →+ A :=
    { toFun := fun n => Additive.ofMul (ξ (Multiplicative.ofAdd n))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add] }
  let G : AddSubgroup M := AddSubgroup.closure (N : Set M)
  have hG : ∀ g : G, ∃ a b : N, (g : M) = a - b := by
    rintro ⟨g, hg⟩
    induction hg using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨⟨x, hx⟩, 0, by simp⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, e⟩ := hx
      obtain ⟨c, d, e'⟩ := hy
      refine ⟨a + c, b + d, ?_⟩
      simp only [AddSubmonoid.coe_add] at e e' ⊢
      rw [e, e']
      abel
    | neg x _ hx =>
      obtain ⟨a, b, e⟩ := hx
      refine ⟨b, a, ?_⟩
      simp only at e ⊢
      rw [e]
      abel
  have hwd : ∀ a b c d : N, (a : M) - b = c - d → x a - x b = x c - x d := by
    intro a b c d e
    have : a + d = c + b := Subtype.ext (by
      simp only [AddSubmonoid.coe_add]
      have : (a : M) + d = c + b + ((a : M) - b - (c - d)) := by abel
      rw [this, e]
      abel)
    have h := congrArg x this
    rw [map_add, map_add] at h
    rw [sub_eq_sub_iff_add_eq_add]
    exact h
  let xt : G →+ A := AddMonoidHom.mk' (fun g => x (hG g).choose - x (hG g).choose_spec.choose) (by
    intro g g'
    have e₁ := (hG g).choose_spec.choose_spec
    have e₂ := (hG g').choose_spec.choose_spec
    have e₃ := (hG (g + g')).choose_spec.choose_spec
    set a := (hG g).choose
    set b := (hG g).choose_spec.choose
    set c := (hG g').choose
    set d := (hG g').choose_spec.choose
    have := hwd (hG (g + g')).choose (hG (g + g')).choose_spec.choose (a + c) (b + d) (by
      rw [← e₃]
      simp only [AddSubgroup.coe_add, AddSubmonoid.coe_add]
      rw [e₁, e₂]
      abel)
    rw [this, map_add, map_add]
    abel)
  have hxt : ∀ n : N, xt ⟨n, AddSubgroup.subset_closure n.2⟩ = x n := by
    intro n
    have e := (hG ⟨n, AddSubgroup.subset_closure n.2⟩).choose_spec.choose_spec
    have := hwd _ _ n 0 (by rw [← e]; simp)
    change x _ - x _ = x n
    rw [this, map_zero, sub_zero]
  have hmono : Mono (AddCommGrpCat.ofHom G.subtype) :=
    (AddCommGrpCat.mono_iff_injective _).2 G.subtype_injective
  let fext := Injective.factorThru (J := AddCommGrpCat.of A) (AddCommGrpCat.ofHom xt)
    (AddCommGrpCat.ofHom G.subtype)
  have hfext : AddCommGrpCat.ofHom G.subtype ≫ fext = AddCommGrpCat.ofHom xt :=
    Injective.comp_factorThru _ _
  let χ : Multiplicative M →* Eˣ :=
    { toFun := fun m => (fext.hom (Multiplicative.toAdd m) : A).toMul
      map_one' := congrArg Additive.toMul (map_zero fext.hom)
      map_mul' := fun a b => congrArg Additive.toMul
        (map_add fext.hom (Multiplicative.toAdd a) (Multiplicative.toAdd b)) }
  refine ⟨χ, fun n => ?_⟩
  have := congrArg (fun k => k.hom ⟨n, AddSubgroup.subset_closure n.2⟩) hfext
  have e : fext.hom (n : M) = x n := this.trans (hxt n)
  exact congrArg Additive.toMul e

end Ext

section Vertex

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M] {X W : Over S}
  {aX : AAction (overO S) M (yoneda.obj X)} {aW : AAction (overO S) M (yoneda.obj W)} (j : W ⟶ X)
  [IsOpenImmersion j.left]
  (hj : ∀ {T : Over S} (h : APt (overO S) M (op T)) (x : T ⟶ W), sm aW h x ≫ j = sm aX h (x ≫ j))

/-- `Spec D` over `T`, along `t : Spec D → T`. -/
abbrev spO {T : Over S} {D : CommRingCat.{u}} (t : Spec D ⟶ T.left) : Over S := Over.mk (t ≫ T.hom)

/-- A morphism of affine schemes over `T`. -/
abbrev spM {T : Over S} {D E : CommRingCat.{u}} (f : D ⟶ E) (t : Spec D ⟶ T.left) :
    spO (T := T) (Spec.map f ≫ t) ⟶ spO (T := T) t :=
  Over.homMk (Spec.map f) (by simp)

lemma units_div_of_field {K : Type u} [Field K] [IsAlgClosed K] {T : Scheme.{u}} (e : Γ(T, ⊤) ≃+* K) :
    ∀ (u : Γ(T, ⊤)ˣ) (n : ℕ), n ≠ 0 → ∃ v : Γ(T, ⊤)ˣ, v ^ n = u := by
  intro u n hn
  have hne : e u ≠ 0 := (Units.map (e : Γ(T, ⊤) →* K) u).ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact hne hz.symm
  let v : Γ(T, ⊤)ˣ := Units.map (e.symm : K →* Γ(T, ⊤)) (Units.mk0 z hz0)
  refine ⟨v, Units.ext ?_⟩
  apply e.injective
  simp [v, hz]

/-- `Spec K` has one point, for `K` a field. -/
lemma spec_field_subsingleton (K : Type u) [Field K] : Subsingleton (Spec (CommRingCat.of K)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

variable {N : AddSubmonoid M} {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)
  (w : N →+ ℕ) (hw : ∀ n : N, w n = 0 ↔ (n : M) ∈ F)

include hj hw in
/-- The main lemma, over an algebraically closed field: the value at `a₀` of a point of `X^N` whose
vertex lies in `W` lies in `W`. -/
theorem mem_range_field {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) (K : Type u) [Field K] [IsAlgClosed K]
    (tk : Spec (CommRingCat.of K) ⟶ T.left) (a₀ : APt (overO S) N (op (spO (T := T) tk)))
    (x : Spec (CommRingCat.of K)) :
    (φ.app (T' := spO (T := T) tk) (Over.homMk tk rfl) a₀).left x ∈ Set.range j.left := by
  classical
  let Pk : CommRingCat.{u} := CommRingCat.of K
  let P : CommRingCat.{u} := CommRingCat.of (Polynomial K)
  let fC : Pk ⟶ P := CommRingCat.ofHom Polynomial.C
  let f0 : P ⟶ Pk := CommRingCat.ofHom (Polynomial.evalRingHom 0)
  have hf0C : fC ≫ f0 = 𝟙 _ := by
    exact CommRingCat.hom_ext (RingHom.ext fun r => Polynomial.eval_C)
  let L : Type u := AlgebraicClosure (FractionRing (Polynomial K))
  let fL : P ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap (Polynomial K) L)
  have hfLinj : Function.Injective fL.hom := by
    have : Function.Injective (algebraMap (Polynomial K) L) := by
      rw [IsScalarTower.algebraMap_eq (Polynomial K) (FractionRing (Polynomial K)) L]
      exact (algebraMap (FractionRing (Polynomial K)) L).injective.comp
        (IsFractionRing.injective _ _)
    exact this
  let Tk : Over S := spO (T := T) tk
  let tP : Spec P ⟶ T.left := Spec.map fC ≫ tk
  let TP : Over S := spO (T := T) tP
  let p : TP ⟶ Tk := spM (T := T) fC tk
  let i₀ : Tk ⟶ TP := Over.homMk (Spec.map f0) (by
    change Spec.map f0 ≫ (Spec.map fC ≫ tk) ≫ T.hom = tk ≫ T.hom
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, hf0C, Spec.map_id, Category.id_comp])
  have hi₀p : i₀ ≫ p = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    change Spec.map f0 ≫ Spec.map fC = 𝟙 _
    rw [← Spec.map_comp, hf0C, Spec.map_id]
  let TL : Over S := spO (T := T) (Spec.map fL ≫ tP)
  let η : TL ⟶ TP := spM (T := T) fL tP
  let s : Tk ⟶ T := Over.homMk tk rfl
  let Xt : Γ(TP.left, ⊤) := (Scheme.ΓSpecIso P).inv.hom Polynomial.X
  have hX₀ : i₀.left.appTop.hom Xt = 0 := by
    have h := congrArg (fun k => k.hom Polynomial.X) (Scheme.ΓSpecIso_inv_naturality f0)
    have h' : (Scheme.ΓSpecIso Pk).inv.hom (f0.hom Polynomial.X) = i₀.left.appTop.hom Xt := h
    rw [← h']
    change (Scheme.ΓSpecIso Pk).inv.hom (Polynomial.eval 0 Polynomial.X) = 0
    rw [Polynomial.eval_X, map_zero]
  let τ : Γ(TL.left, ⊤) := η.left.appTop.hom Xt
  have hτ : τ = (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (fL.hom Polynomial.X) :=
    (congrArg (fun k => k.hom Polynomial.X) (Scheme.ΓSpecIso_inv_naturality fL)).symm
  let eK : Γ(Tk.left, ⊤) ≃+* K := (Scheme.ΓSpecIso Pk).commRingCatIsoToRingEquiv
  let eL : Γ(TL.left, ⊤) ≃+* L := (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv
  have hτ0 : eL τ ≠ 0 := by
    have : eL τ = fL.hom Polynomial.X := by
      rw [hτ]
      exact (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.apply_symm_apply _
    rw [this]
    intro h0
    exact Polynomial.X_ne_zero (hfLinj (h0.trans (map_zero _).symm))
  -- the deformation `n ↦ a₀(n) X^{w(n)}`
  let a₁ : Multiplicative N →* Γ(Tk.left, ⊤) := a₀
  let c : APt (overO S) N (op TP) :=
    { toFun := fun n => p.left.appTop.hom (a₁ n) * Xt ^ w (Multiplicative.toAdd n)
      map_one' := by
        have e0 : w (Multiplicative.toAdd (1 : Multiplicative N)) = 0 := map_zero w
        rw [map_one a₁, map_one, e0, pow_zero]
        exact mul_one _
      map_mul' := fun a b => by
        rw [map_mul a₁, map_mul, show Multiplicative.toAdd (a * b) =
          Multiplicative.toAdd a + Multiplicative.toAdd b from rfl, map_add, pow_add]
        exact mul_mul_mul_comm _ _ _ _ }
  let aF : APt (overO S) F.toAddSubmonoid (op Tk) := APt.restrict hF.le a₀
  have hip : p.left.appTop ≫ i₀.left.appTop = 𝟙 _ := by
    have h : (i₀ ≫ p).left.appTop = p.left.appTop ≫ i₀.left.appTop := by simp
    rw [← h, hi₀p]
    simp
  have hc₀ : APt.res i₀.op c = APt.faceExt hF aF := by
    refine MonoidHom.ext fun n => ?_
    have e₁ : i₀.left.appTop.hom (p.left.appTop.hom (a₁ n)) = a₁ n :=
      congrArg (fun k => k.hom (a₁ n)) hip
    change i₀.left.appTop.hom (p.left.appTop.hom (a₁ n) * Xt ^ w (Multiplicative.toAdd n)) = _
    rw [map_mul, map_pow, e₁, hX₀]
    by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ F
    · rw [(hw _).2 hn, pow_zero]
      refine Eq.trans (mul_one (a₁ n)) ?_
      rw [APt.faceExt_pos hF aF hn]
      rfl
    · have hne : w (Multiplicative.toAdd n) ≠ 0 := fun e => hn ((hw _).1 e)
      rw [zero_pow hne]
      refine Eq.trans (mul_zero (a₁ n)) ?_
      rw [APt.faceExt_neg hF aF hn]
      rfl
  -- the vertex: extend `a₀|F` to `M`
  let ξ : Multiplicative F.toAddSubmonoid →* Γ(Tk.left, ⊤)ˣ :=
    { toFun := fun f =>
        { val := aF f
          inv := aF (Multiplicative.ofAdd ⟨-((Multiplicative.toAdd f : F.toAddSubmonoid) : M),
            F.neg_mem (Multiplicative.toAdd f).2⟩)
          val_inv := ((map_mul aF _ _).symm.trans (congrArg aF (by
            apply Multiplicative.toAdd.injective
            exact Subtype.ext (add_neg_cancel _)))).trans (map_one aF)
          inv_val := ((map_mul aF _ _).symm.trans (congrArg aF (by
            apply Multiplicative.toAdd.injective
            exact Subtype.ext (neg_add_cancel _)))).trans (map_one aF) }
      map_one' := Units.ext (map_one aF)
      map_mul' := fun a b => Units.ext (map_mul aF a b) }
  obtain ⟨χ₀, hχ₀⟩ := exists_ext_units (units_div_of_field eK) F.toAddSubmonoid ξ
  let g₀ : APt (overO S) M (op Tk) := (Units.coeHom _).comp χ₀
  have hg₀ : APt.toMagnet F.toAddSubmonoid g₀ * 1 = aF := by
    refine MonoidHom.ext fun f => ?_
    change ((χ₀ (Multiplicative.ofAdd (((Multiplicative.toAdd f : F.toAddSubmonoid) : M))) : Γ(Tk.left, ⊤)ˣ) : Γ(Tk.left, ⊤)) * 1 = _
    rw [mul_one, hχ₀]
    rfl
  let y := φ.app (p ≫ s) c
  have hy₀ : i₀ ≫ y = sm aW g₀ (s ≫ u) ≫ j := by
    have e₁ : i₀ ≫ y = φ.app (i₀ ≫ p ≫ s) (APt.res i₀.op c) := (φ.naturality i₀ (p ≫ s) c).symm
    have e₂ : i₀ ≫ p ≫ s = s := by rw [← Category.assoc, hi₀p, Category.id_comp]
    rw [e₁, e₂, hc₀, hj]
    change (AttractorPt.ofFace hF φ).app s aF = _
    rw [← hg₀, (AttractorPt.ofFace hF φ).equivariant]
    congr 1
    have e₃ := (AttractorPt.ofFace hF φ).naturality s (𝟙 T) 1
    have hone : APt.res (𝒪 := overO S) (P := F.toAddSubmonoid) s.op 1 = 1 := by
      ext q
      simp
    rw [hone, Category.comp_id] at e₃
    refine e₃.trans ?_
    change s ≫ (AttractorPt.ofFace hF φ).toPoint = _
    rw [hu, Category.assoc]
  -- the generic point lies in `W`
  let pL : Spec (CommRingCat.of L) := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : y.left (η.left pL) ∈ Set.range j.left := by
    have hopen : IsOpen (y.left ⁻¹' Set.range j.left) :=
      (j.left.isOpenEmbedding.isOpen_range).preimage y.left.continuous
    have hsp : (η.left pL) ⤳ (i₀.left x) := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      have : (η.left pL : PrimeSpectrum (Polynomial K)).asIdeal = ⊥ := by
        change Ideal.comap fL.hom ⊥ = ⊥
        exact (RingHom.injective_iff_ker_eq_bot _).1 hfLinj
      change (η.left pL : PrimeSpectrum (Polynomial K)).asIdeal ≤ _
      rw [this]
      exact bot_le
    refine hsp.mem_open hopen ?_
    rw [Set.mem_preimage]
    have : y.left (i₀.left x) = (i₀ ≫ y).left x := by
      rw [Over.comp_left, Scheme.Hom.comp_apply]
    rw [this, hy₀, Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  -- undo the deformation
  let uτ : Γ(TL.left, ⊤)ˣ := Units.map (eL.symm : L →* Γ(TL.left, ⊤)) (Units.mk0 (eL τ) hτ0)
  have huτ : (uτ : Γ(TL.left, ⊤)) = τ := by
    change eL.symm (eL τ) = τ
    exact eL.symm_apply_apply τ
  let ξ' : Multiplicative N →* Γ(TL.left, ⊤)ˣ :=
    { toFun := fun n => uτ ^ w (Multiplicative.toAdd n)
      map_one' := by simp
      map_mul' := fun a b => by rw [toAdd_mul, map_add, pow_add] }
  obtain ⟨χu, hχu⟩ := exists_ext_units (units_div_of_field eL) N ξ'
  let χ' : APt (overO S) M (op TL) := (Units.coeHom _).comp χu
  let χi : APt (overO S) M (op TL) := (Units.coeHom _).comp χu⁻¹
  have hχi : χi * χ' = 1 := by
    refine MonoidHom.ext fun m => ?_
    change (((χu⁻¹) m : Γ(TL.left, ⊤)ˣ) : Γ(TL.left, ⊤)) * (χu m : Γ(TL.left, ⊤)ˣ) = 1
    rw [MonoidHom.inv_apply, Units.inv_mul]
  let q : TL ⟶ Tk := η ≫ p
  have hcL : APt.res η.op c = APt.toMagnet N χ' * APt.res q.op a₀ := by
    refine MonoidHom.ext fun n => ?_
    change η.left.appTop.hom (p.left.appTop.hom (a₀ n) * Xt ^ w (Multiplicative.toAdd n)) =
      ((χu (Multiplicative.ofAdd ((Multiplicative.toAdd n : N) : M)) : Γ(TL.left, ⊤)ˣ) : Γ(TL.left, ⊤)) *
        (η ≫ p).left.appTop.hom (a₀ n)
    rw [hχu, map_mul, map_pow]
    change _ * τ ^ _ = ((uτ ^ w (Multiplicative.toAdd n) : Γ(TL.left, ⊤)ˣ) : Γ(TL.left, ⊤)) * _
    rw [Units.val_pow_eq_pow_val, huτ, mul_comm, Over.comp_left, Scheme.Hom.comp_appTop]
    rfl
  let y' : TL ⟶ X := q ≫ φ.app s a₀
  have hy' : η ≫ y = sm aX χ' y' := by
    have e₁ : η ≫ y = φ.app (η ≫ p ≫ s) (APt.res η.op c) := (φ.naturality η (p ≫ s) c).symm
    rw [e₁, hcL]
    refine (φ.equivariant _ χ' _).trans ?_
    congr 1
    have e₂ := φ.naturality q s a₀
    rwa [Category.assoc] at e₂
  have hsub : Subsingleton (Spec (CommRingCat.of L)) := spec_field_subsingleton L
  have hrange : Set.range (sm aX χ' y').left ⊆ Set.range j.left := by
    rintro _ ⟨b, rfl⟩
    have : b = pL := hsub.elim _ _
    rw [this, ← hy', Over.comp_left, Scheme.Hom.comp_apply]
    exact hgen
  let v : TL ⟶ W := Over.homMk (IsOpenImmersion.lift j.left _ hrange) (by
    have e := Over.w j
    rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (sm aX χ' y'))
  have hv : v ≫ j = sm aX χ' y' := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hy'j : y' = sm aW χi v ≫ j := by
    rw [hj, hv]
    change y' = aX.smul χi (aX.smul χ' y')
    rw [← aX.mul_smul, hχi, aX.one_smul]
  have hq : q.left pL = x := by
    exact (spec_field_subsingleton K).elim _ _
  have : (φ.app s a₀).left x = y'.left pL := by
    change _ = (q ≫ φ.app s a₀).left pL
    rw [Over.comp_left, Scheme.Hom.comp_apply, hq]
  change (φ.app s a₀).left x ∈ _
  rw [this, hy'j, Over.comp_left, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

include hj hw in
/-- The value at any point. -/
theorem mem_range_app {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) {T' : Over S} (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) (x : T'.left) : (φ.app t a).left x ∈ Set.range j.left := by
  let κ := T'.left.residueField x
  let K : Type u := AlgebraicClosure κ
  let m : Spec (CommRingCat.of K) ⟶ T'.left :=
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ T'.left.fromSpecResidueField x
  let tk : Spec (CommRingCat.of K) ⟶ T.left := m ≫ t.left
  let m' : spO (T := T) tk ⟶ T' := Over.homMk m (by
    change m ≫ T'.hom = (m ≫ t.left) ≫ T.hom
    exact (congrArg (m ≫ ·) (Over.w t).symm).trans (Category.assoc _ _ _).symm)
  have hs : (Over.homMk tk rfl : spO (T := T) tk ⟶ T) = m' ≫ t := Over.OverMorphism.ext rfl
  have pt : Nonempty (Spec (CommRingCat.of K)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨z⟩ := pt
  have hz := mem_range_field j hj hF w hw φ u hu K tk (APt.res m'.op a) z
  rw [hs, φ.naturality, ] at hz
  have e : (yoneda.obj X).map m'.op (φ.app t a) = m' ≫ φ.app t a := rfl
  rw [e, Over.comp_left, Scheme.Hom.comp_apply] at hz
  have hm : m'.left z = x := by
    change T'.left.fromSpecResidueField x _ = x
    exact Scheme.fromSpecResidueField_apply x _
  rwa [hm] at hz

include hj hw in
/-- **The reduction to `W`**: a point of `X^N` with vertex in `W` is a point of `W^N`. -/
theorem exists_att_of_vertex {T : Over S} (φ : AttractorPt aX N T) (u : T ⟶ W)
    (hu : (AttractorPt.ofFace hF φ).toPoint = u ≫ j) :
    ∃ ψ : AttractorPt aW N T, AttractorPt.push (eqHom j hj) ψ = φ := by
  have hr : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')),
      Set.range (φ.app t a).left ⊆ Set.range j.left := by
    rintro T' t a _ ⟨x, rfl⟩
    exact mem_range_app j hj hF w hw φ u hu t a x
  let lf : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')), T' ⟶ W := fun t a =>
    Over.homMk (IsOpenImmersion.lift j.left _ (hr t a)) (by
      have e := Over.w j
      rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w (φ.app t a))
  have hlf : ∀ {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')), lf t a ≫ j = φ.app t a :=
    fun t a => Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hcancel : ∀ {T' : Over S} {a b : T' ⟶ W}, a ≫ j = b ≫ j → a = b := by
    intro T' a b h
    refine Over.OverMorphism.ext ((cancel_mono j.left).1 ?_)
    exact congrArg (fun k => k.left) h
  refine ⟨{ app := fun t a => lf t a
            naturality := fun s t a => hcancel ?_
            equivariant := fun t h a => hcancel ?_ }, ?_⟩
  · refine (hlf _ _).trans ?_
    refine (φ.naturality s t a).trans ?_
    change s ≫ φ.app t a = (s ≫ lf t a) ≫ j
    rw [Category.assoc, hlf]
  · refine (hlf _ _).trans ?_
    refine (φ.equivariant t h a).trans ?_
    rw [← hlf t a]
    exact (hj h (lf t a)).symm
  · refine AttractorPt.ext ?_
    funext T' t a
    exact hlf t a

end Vertex

end AlgMag.Sec12Printed
