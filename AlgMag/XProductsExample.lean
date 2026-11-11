/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsRep

/-!
# X-products of attractors: Example 4.4

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, Example 4.4.

`M = Z = ℤ`, `𝒩 = {εℕ}`, `ε = ±1`. The scheme `𝔸(𝒩)` is the projective line glued from its two charts
`Spec ℤ[u]` and `Spec ℤ[u⁻¹]`, with the action `t • u = t u` (`ex_coord_smul`). We work on the category of
all schemes (schemes over `S = Spec ℤ`), and `X = 𝔸(𝒩)` with its action.

## Main results

* `AlgMag.XP.exFam`, `AlgMag.XP.exAct`: the data of Example 4.4.
* `AlgMag.XP.exOrbit`, `AlgMag.XP.exConst`: the `G_m`-equivariant maps `z ↦ az` (`a` a unit) and the two
  constant maps `0`, `∞` of Example 4.4, as points of `X^𝒩`.
* `AlgMag.XP.ex44_injective`: these points are pairwise distinct, over nonempty `T`.
* `AlgMag.XP.ex44_not_iInf`: **Example 4.4**: the formula `X^𝒩 = X^{⋂ N}` of Proposition 4.3 does not
  extend to the non-affine case. The orbit map `z ↦ z` is a point of `X^𝒩(Spec ℤ)` which does not come from
  `X^{⋂ N}(Spec ℤ) = X^0(Spec ℤ)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

set_option linter.unusedSectionVars false

namespace AlgMag.XP

open GB

noncomputable section

section General

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A) [Nonempty A]
variable {C : Type*} [Category.{v} C] (τ : C ⥤ Scheme.{u})

/-- `X = 𝔸(𝒩)` as a presheaf on `C`. -/
abbrev selfX : Cᵒᵖ ⥤ Type u := τ.op ⋙ yoneda.obj 𝓝.AN

/-- The action of `D(M)` on `X = 𝔸(𝒩)`, on `C`. -/
def selfAct : AAction (τO τ) M (selfX 𝓝 τ) where
  smul {U} k y := 𝓝.smulN (W := τ.obj (unop U)) k y
  one_smul {U} x := 𝓝.actAN.one_smul (U := op (τ.obj (unop U))) x
  mul_smul {U} g h x := 𝓝.actAN.mul_smul (U := op (τ.obj (unop U))) g h x
  map_smul {U V} f h x := 𝓝.comp_smulN (τ.map f.unop) h x

variable {τ}

lemma smulN_comm {W : Scheme.{u}} (k k₀ : APt Scheme.Γ M (op W)) (y : W ⟶ 𝓝.AN) :
    𝓝.smulN k (𝓝.smulN k₀ y) = 𝓝.smulN k₀ (𝓝.smulN k y) := by
  have h1 := 𝓝.actAN.mul_smul (U := op W) k k₀ y
  have h2 := 𝓝.actAN.mul_smul (U := op W) k₀ k y
  rw [mul_comm k k₀] at h1
  exact h1.symm.trans h2

/-- The equivariant map `y ↦ k₀ • y`, for `k₀ ∈ D(M)(T)`: for `M = ℤ` and `k₀(n) = aⁿ` this is `z ↦ az`. -/
def orbitPt {T : C} (k₀ : APt (τO τ) M (op T)) : XNPt 𝓝 τ (selfAct 𝓝 τ) T where
  app {T'} t y := 𝓝.smulN (W := τ.obj T') (APt.res (𝒪 := τO τ) t.op k₀) y
  naturality {T' T''} s t y := by
    have e := 𝓝.comp_smulN (τ.map s) (APt.res (𝒪 := τO τ) t.op k₀) y
    have e' : APt.res (𝒪 := τO τ) (s ≫ t).op k₀ =
        APt.res (𝒪 := τO τ) s.op (APt.res (𝒪 := τO τ) t.op k₀) := by
      rw [op_comp, APt.res_comp]
    exact (congrArg (fun q => 𝓝.smulN (W := τ.obj T'') q (τ.map s ≫ y)) e').trans e.symm
  equivariant {T'} t k y :=
    smulN_comm 𝓝 (W := τ.obj T') (APt.res (𝒪 := τO τ) t.op k₀) k y

lemma toPoint_orbitPt {T : C} (k₀ : APt (τO τ) M (op T)) :
    (orbitPt 𝓝 k₀).toPoint = 𝓝.smulN (W := τ.obj T) k₀ (unitPt 𝓝 τ T) := by
  change 𝓝.smulN (W := τ.obj T) (APt.res (𝒪 := τO τ) (𝟙 T).op k₀) (unitPt 𝓝 τ T) = _
  rw [show APt.res (𝒪 := τO τ) (𝟙 T).op k₀ = k₀ from APt.res_id k₀]

/-- `k₀ • 1` determines the restriction of `k₀` to `Z`. -/
lemma pts_orbit_unit {T : C} (k₀ : APt (τO τ) M (op T)) :
    𝓝.smulN (W := τ.obj T) k₀ (unitPt 𝓝 τ T) =
      (ptsT τ 𝓝.Z.toAddSubmonoid T).symm (APt.toMagnet _ k₀) ≫ 𝓝.ιD := by
  rw [unitPt, 𝓝.smulN_comp_ιD]
  congr 1
  apply (ptsT τ _ T).injective
  have h := ptsT_smulA (τ := τ) (P := 𝓝.Z.toAddSubmonoid) k₀
    ((ptsT τ 𝓝.Z.toAddSubmonoid T).symm 1)
  refine h.trans ?_
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, mul_one]

end General

/-- The generators `±1`. -/
def exE : Bool → ℤ
  | true => 1
  | false => -1

/-- The family `𝒩 = {εℕ}` of Example 4.4, with `M = Z = ℤ`. -/
def exFam : MagnetFamily ℤ Bool where
  N b := AddSubmonoid.multiples (exE b)
  Z := ⊤
  fg b := ⟨{exE b}, by simp [AddSubmonoid.multiples_eq_closure]⟩
  gp b := by
    rw [eq_top_iff]
    intro z _
    have h1 : exE b ∈ AddSubgroup.closure ((AddSubmonoid.multiples (exE b) : AddSubmonoid ℤ) : Set ℤ) :=
      AddSubgroup.subset_closure (AddSubmonoid.mem_multiples _)
    have hb : exE b * exE b = 1 := by cases b <;> rfl
    have : z = (z * exE b) • exE b := by
      rw [smul_eq_mul, mul_assoc, hb, mul_one]
    rw [this]
    exact AddSubgroup.zsmul_mem _ h1 _

lemma mem_exN {b : Bool} {n : ℤ} : n ∈ exFam.N b ↔ ∃ k : ℕ, n = k * exE b := by
  change n ∈ AddSubmonoid.multiples (exE b) ↔ _
  rw [AddSubmonoid.mem_multiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

/-- `X = 𝔸(𝒩)` with its action, on all schemes. -/
abbrev exAct : AAction (τO (𝟭 Scheme.{0})) ℤ (selfX exFam (𝟭 Scheme.{0})) := selfAct exFam (𝟭 Scheme.{0})

section Coordinates

variable {T T' : Scheme.{0}}

/-- The element `u` or `u⁻¹` of the monoid `N_ε`. -/
def exGen (b : Bool) : Multiplicative (exFam.N b) :=
  Multiplicative.ofAdd ⟨exE b, AddSubmonoid.mem_multiples _⟩

/-- The coordinate of a point of the chart `𝔸(N_ε)`. -/
def exCoord {b : Bool} (a : T ⟶ AZ (exFam.N b)) : Scheme.Γ.obj (op T) :=
  pts (exFam.N b) T a (exGen b)

/-- **Example 4.4**: the action is `t • u = t u`, and `t • u⁻¹ = t⁻¹ u⁻¹` on the other chart. -/
theorem ex_coord_smul {b : Bool} (k : APt Scheme.Γ ℤ (op T)) (a : T ⟶ AZ (exFam.N b)) :
    exCoord (smulA k a) = k (Multiplicative.ofAdd (exE b)) * exCoord a := by
  unfold exCoord
  rw [pts_smulA]
  rfl

open Classical in
/-- The point `0` of the chart: the monoid map `n ↦ 0^n`. -/
def exZeroHom (b : Bool) (T : Scheme.{0}) : APt Scheme.Γ (exFam.N b) (op T) where
  toFun n := if Multiplicative.toAdd n = 0 then 1 else 0
  map_one' := if_pos rfl
  map_mul' m n := by
    have hsplit : ∀ x y : exFam.N b, x + y = 0 → x = 0 ∧ y = 0 := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      obtain ⟨i, rfl⟩ := mem_exN.mp hx
      obtain ⟨j, rfl⟩ := mem_exN.mp hy
      have h' : (i : ℤ) * exE b + (j : ℤ) * exE b = 0 := congrArg Subtype.val h
      have hne : exE b ≠ 0 := by cases b <;> decide
      have hij : ((i : ℤ) + j) = 0 := by
        have : ((i : ℤ) + j) * exE b = 0 := by rw [add_mul]; exact h'
        exact (mul_eq_zero.mp this).resolve_right hne
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst hi hj
      constructor <;> exact Subtype.ext (by simp)
    by_cases hm : Multiplicative.toAdd m = 0 <;> by_cases hn : Multiplicative.toAdd n = 0
    · have : Multiplicative.toAdd (m * n) = 0 := by rw [toAdd_mul, hm, hn, add_zero]
      rw [if_pos this, if_pos hm, if_pos hn, mul_one]
    · have : Multiplicative.toAdd (m * n) ≠ 0 := fun h => hn (hsplit _ _ h).2
      rw [if_neg this, if_pos hm, if_neg hn, mul_zero]
    · have : Multiplicative.toAdd (m * n) ≠ 0 := fun h => hm (hsplit _ _ h).1
      rw [if_neg this, if_neg hm, if_pos hn, zero_mul]
    · have : Multiplicative.toAdd (m * n) ≠ 0 := fun h => hm (hsplit _ _ h).1
      rw [if_neg this, if_neg hm, if_neg hn, zero_mul]

lemma exZeroHom_res {b : Bool} (g : T' ⟶ T) :
    APt.res g.op (exZeroHom b T) = exZeroHom b T' := by
  classical
  refine MonoidHom.ext fun n => ?_
  rw [APt.res_apply]
  change (Scheme.Γ.map g.op).hom (if Multiplicative.toAdd n = 0 then 1 else 0) =
    (if Multiplicative.toAdd n = 0 then 1 else 0)
  split_ifs
  · exact map_one _
  · exact map_zero _

lemma toMagnet_mul_exZero {b : Bool} (k : APt Scheme.Γ ℤ (op T)) :
    APt.toMagnet (exFam.N b) k * exZeroHom b T = exZeroHom b T := by
  classical
  refine MonoidHom.ext fun n => ?_
  rw [MonoidHom.mul_apply]
  change _ * (if Multiplicative.toAdd n = 0 then 1 else 0) =
    (if Multiplicative.toAdd n = 0 then 1 else 0)
  split_ifs with h
  · rw [mul_one]
    have hn : n = 1 := Multiplicative.toAdd.injective h
    rw [hn, map_one]
  · rw [mul_zero]

/-- The constant `0` (for `ε = +`) or `∞` (for `ε = -`) of `𝔸(𝒩)`. -/
def exPt (b : Bool) (T : Scheme.{0}) : T ⟶ exFam.AN := (pts (exFam.N b) T).symm (exZeroHom b T) ≫ exFam.ι b

lemma comp_exPt (b : Bool) (g : T' ⟶ T) : g ≫ exPt b T = exPt b T' := by
  rw [exPt, exPt, ← Category.assoc]
  congr 1
  apply (pts _ T').injective
  rw [pts_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, exZeroHom_res]

lemma smulN_exPt (b : Bool) (k : APt Scheme.Γ ℤ (op T)) : exFam.smulN k (exPt b T) = exPt b T := by
  rw [exPt, exFam.smulN_comp_ι]
  congr 1
  apply (pts _ T).injective
  rw [pts_smulA, Equiv.apply_symm_apply, toMagnet_mul_exZero]

end Coordinates

/-- The constant equivariant maps of Example 4.4: the constant `0` and the constant `∞`. -/
def exConst (b : Bool) (T : Scheme.{0}) : XNPt exFam (𝟭 Scheme.{0}) exAct T where
  app {T'} _ _ := exPt b T'
  naturality s t y := (comp_exPt b s).symm
  equivariant {T'} t k y := (smulN_exPt b (T := T') k).symm

/-- The character `n ↦ aⁿ` of a unit `a`. -/
def exChar {T : Scheme.{0}} (a : Γ(T, ⊤)ˣ) : APt (τO (𝟭 Scheme.{0})) ℤ (op T) where
  toFun n := ((a ^ (Multiplicative.toAdd n) : Γ(T, ⊤)ˣ) : Γ(T, ⊤))
  map_one' := by
    rw [toAdd_one, zpow_zero]
    rfl
  map_mul' m n := by
    rw [toAdd_mul, zpow_add, Units.val_mul]
    rfl

/-- The map `z ↦ az` of Example 4.4, for a unit `a`. -/
def exOrbit {T : Scheme.{0}} (a : Γ(T, ⊤)ˣ) : XNPt exFam (𝟭 Scheme.{0}) exAct T :=
  orbitPt exFam (exChar a)

/-- The point of `X^𝒩(T)` attached to a unit or to one of the constants `0`, `∞`. -/
def exPoint (T : Scheme.{0}) : Γ(T, ⊤)ˣ ⊕ Bool → XNPt exFam (𝟭 Scheme.{0}) exAct T
  | .inl a => exOrbit a
  | .inr b => exConst b T

lemma toPoint_exOrbit {T : Scheme.{0}} (a : Γ(T, ⊤)ˣ) :
    (exOrbit a).toPoint = (pts exFam.Z.toAddSubmonoid T).symm (APt.toMagnet _ (exChar a)) ≫ exFam.ιD :=
  (toPoint_orbitPt exFam _).trans (pts_orbit_unit exFam _)

instance : IsOpenImmersion exFam.ιD := by
  rw [← exFam.gpMap_ι true]
  infer_instance

instance : Mono exFam.ιD := inferInstance

lemma exZero_gen {T : Scheme.{0}} (b : Bool) : exZeroHom b T (exGen b) = 0 := by
  classical
  refine if_neg ?_
  intro h
  have := congrArg Subtype.val h
  revert this
  cases b <;> decide

/-- The element `ε` of `Z = ℤ`. -/
def exGenZ (b : Bool) : Multiplicative exFam.Z.toAddSubmonoid :=
  Multiplicative.ofAdd ⟨exE b, trivial⟩

lemma pts_gp {T : Scheme.{0}} {b : Bool} (u : T ⟶ exFam.D) :
    pts (exFam.N b) T (u ≫ exFam.gpMap b) (exGen b) = pts exFam.Z.toAddSubmonoid T u (exGenZ b) := by
  have h : pts (exFam.N b) T (u ≫ exFam.gpMap b) =
      APt.restrict (exFam.le b) (pts exFam.Z.toAddSubmonoid T u) := pts_map _ u
  rw [h]
  rfl

lemma not_isUnit_zero_of_nonempty {T : Scheme.{0}} [Nonempty T] :
    ¬ IsUnit (0 : Scheme.Γ.obj (op T)) := by
  have : Nontrivial (Scheme.Γ.obj (op T)) := by
    have : Nonempty ↑(⊤ : T.Opens) := ⟨⟨Classical.arbitrary T, trivial⟩⟩
    exact Scheme.component_nontrivial T ⊤
  exact not_isUnit_zero

/-- A point of `D(Z)` is not one of the constants `0`, `∞`, over a nonempty base. -/
lemma exPt_ne_of_gp {T : Scheme.{0}} [Nonempty T] (b : Bool) (u : T ⟶ exFam.D)
    (hu : IsUnit (pts exFam.Z.toAddSubmonoid T u (exGenZ b))) :
    exPt b T ≠ u ≫ exFam.ιD := by
  intro h
  rw [exPt, ← exFam.gpMap_ι b, ← Category.assoc] at h
  have e := (cancel_mono (exFam.ι b)).mp h
  have e2 := congrArg (fun a => pts (exFam.N b) T a (exGen b)) e
  simp only [Equiv.apply_symm_apply] at e2
  rw [exZero_gen, pts_gp] at e2
  rw [← e2] at hu
  exact not_isUnit_zero_of_nonempty hu

lemma exChar_gen {T : Scheme.{0}} (a : Γ(T, ⊤)ˣ) (b : Bool) :
    IsUnit (APt.toMagnet exFam.Z.toAddSubmonoid (exChar a) (exGenZ b)) :=
  Units.isUnit _

/-- **Example 4.4**: the points `z ↦ az` (`a` a unit) and the two constant maps `0`, `∞` of `X^𝒩(T)` are
pairwise distinct, for `T` nonempty. Their images in `X(T)` are already distinct. -/
theorem ex44_injective (T : Scheme.{0}) [Nonempty T] :
    Function.Injective fun x => (exPoint T x).toPoint := by
  rintro (a | b) (a' | b') h
  · have h' : (exOrbit a).toPoint = (exOrbit a').toPoint := h
    rw [toPoint_exOrbit, toPoint_exOrbit] at h'
    have e := (pts exFam.Z.toAddSubmonoid T).symm.injective ((cancel_mono exFam.ιD).mp h')
    have e2 := congrFun (congrArg DFunLike.coe e) (exGenZ true)
    congr 1
    refine Units.ext ?_
    have e3 : ((a ^ (1 : ℤ) : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) = ((a' ^ (1 : ℤ) : Γ(T, ⊤)ˣ) : Γ(T, ⊤)) := e2
    simpa using e3
  · have h' : (exOrbit a).toPoint = exPt b' T := h
    rw [toPoint_exOrbit] at h'
    refine (exPt_ne_of_gp b' _ ?_ h'.symm).elim
    have e : pts exFam.Z.toAddSubmonoid T ((pts exFam.Z.toAddSubmonoid T).symm
        (APt.toMagnet _ (exChar a))) = APt.toMagnet _ (exChar a) := Equiv.apply_symm_apply _ _
    rw [e]
    exact exChar_gen a b'
  · have h' : exPt b T = (exOrbit a').toPoint := h
    rw [toPoint_exOrbit] at h'
    refine (exPt_ne_of_gp b _ ?_ h').elim
    have e : pts exFam.Z.toAddSubmonoid T ((pts exFam.Z.toAddSubmonoid T).symm
        (APt.toMagnet _ (exChar a'))) = APt.toMagnet _ (exChar a') := Equiv.apply_symm_apply _ _
    rw [e]
    exact exChar_gen a' b
  · congr 1
    by_contra hne
    have h' : exPt b T = exPt b' T := h
    obtain ⟨u, hu, -⟩ := exFam.exists_factor_of_overlap hne _ _ h'
    have e2 := congrArg (fun a => pts (exFam.N b) T a (exGen b)) hu
    simp only [Equiv.apply_symm_apply] at e2
    rw [exZero_gen, pts_gp] at e2
    have hzero : pts exFam.Z.toAddSubmonoid T u (exGenZ b) = 0 := e2
    have hneg : exGenZ b * exGenZ (!b) = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      cases b <;> rfl
    have h1 := map_mul (pts exFam.Z.toAddSubmonoid T u) (exGenZ b) (exGenZ (!b))
    rw [hneg, map_one, hzero, zero_mul] at h1
    exact not_isUnit_zero_of_nonempty (T := T) (h1 ▸ isUnit_one)

/-- `⋂ N = 0` in Example 4.4: `X^{⋂ N} = X^0`. -/
theorem ex44_iInf : (⨅ b, exFam.N b) = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  have h1 := (AddSubmonoid.mem_iInf.mp hn) true
  have h2 := (AddSubmonoid.mem_iInf.mp hn) false
  obtain ⟨i, hi⟩ := mem_exN.mp h1
  obtain ⟨j, hj⟩ := mem_exN.mp h2
  have hi' : n = i := by simpa [exE] using hi
  have hj' : n = -j := by simpa [exE] using hj
  have : n = 0 := by omega
  exact this

/-- `Spec ℤ`. -/
abbrev specZ : Scheme.{0} := Spec (.of ℤ)

/-- **Example 4.4**: the formula `X^𝒩 = X^{⋂ N}` does not extend to the non-affine case. The orbit map
`z ↦ z` is a point of `X^𝒩(Spec ℤ)` whose image in `X(Spec ℤ)` is not the image of a point of
`X^{⋂ N}(Spec ℤ)`. -/
theorem ex44_not_iInf :
    ¬ ∃ χ : AttractorPt exAct (⨅ b, exFam.N b) specZ, χ.toPoint = (exOrbit 1).toPoint := by
  rintro ⟨χ, hχ⟩
  let k : APt (τO (𝟭 Scheme.{0})) ℤ (op specZ) := exChar (-1)
  have hk : APt.toMagnet (⨅ b, exFam.N b) k * 1 = 1 := by
    refine MonoidHom.ext fun n => ?_
    have hn : n = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have h4 : (⨅ b, exFam.N b) ≤ ⊥ := ex44_iInf.le
      exact AddSubmonoid.mem_bot.mp (h4 (Multiplicative.toAdd n).2)
    rw [hn]
    exact (map_one _).trans (map_one _).symm
  have heq := χ.equivariant (𝟙 _) k 1
  rw [hk] at heq
  have hfix : χ.toPoint = exFam.smulN (W := specZ) k χ.toPoint := heq
  rw [hχ, toPoint_exOrbit] at hfix
  rw [exFam.smulN_comp_ιD] at hfix
  have e := (cancel_mono exFam.ιD).mp hfix
  have e2 := congrArg (pts exFam.Z.toAddSubmonoid specZ) e
  rw [pts_smulA, Equiv.apply_symm_apply] at e2
  have e3 := congrFun (congrArg DFunLike.coe e2) (exGenZ true)
  have e4 : (1 : Scheme.Γ.obj (op specZ)) = -1 := by
    have l : APt.toMagnet exFam.Z.toAddSubmonoid (exChar (T := specZ) 1) (exGenZ true) = 1 := by
      change (((1 : Γ(specZ, ⊤)ˣ) ^ (1 : ℤ) : Γ(specZ, ⊤)ˣ) : Γ(specZ, ⊤)) = 1
      simp
    have r : APt.toMagnet exFam.Z.toAddSubmonoid k (exGenZ true) = -1 := by
      change (((-1 : Γ(specZ, ⊤)ˣ) ^ (1 : ℤ) : Γ(specZ, ⊤)ˣ) : Γ(specZ, ⊤)) = -1
      simp
    have e5 : APt.toMagnet exFam.Z.toAddSubmonoid (exChar (T := specZ) 1) (exGenZ true) =
        APt.toMagnet exFam.Z.toAddSubmonoid k (exGenZ true) *
          APt.toMagnet exFam.Z.toAddSubmonoid (exChar (T := specZ) 1) (exGenZ true) := e3
    rw [l, r, mul_one] at e5
    exact e5
  have e6 := congrArg (Scheme.ΓSpecIso (.of ℤ)).hom.hom e4
  let f := (Scheme.ΓSpecIso (.of ℤ)).hom.hom
  have e7 : (1 : ℤ) = -1 := (map_one f).symm.trans (e6.trans ((map_neg f 1).trans
    (congrArg (fun x : ℤ => -x) (map_one f))))
  exact absurd e7 (by decide)

end

end AlgMag.XP

#print axioms AlgMag.XP.ex_coord_smul
#print axioms AlgMag.XP.ex44_injective
#print axioms AlgMag.XP.ex44_not_iInf
