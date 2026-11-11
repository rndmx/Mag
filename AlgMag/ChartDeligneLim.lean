/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartDeligneCore

/-!
# Lemma 4.3 of the chart-lemma proof: the ideal `a` and the elements of `C`

For an equivariant system `x` on a complete pair `(C, m)`: the ideal `a` with `J·C/mⁿ = a·C/mⁿ`
(`idl_eq_map`), and, for `g ∈ a` of degree `δ`, `f` of degree `d`, an element `t` of degree
`d + Nδ` with `t = g^N f` modulo each `mⁿ` (`exists_LL`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain.DeligneInst

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)}
  {fU : yoneda.obj U₀ ⟶ X} {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {φ : yoneda.obj V ⟶ X} (C : Ctx actX actU fU φ)

/-- `homog_of_lift` for `Lift`. -/
theorem homog_lift {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (actW : AAction (fppfO B S hS) M (yoneda.obj W)) (y : X.obj (op W))
    (hy : EquivAlong actW actX (𝟙 W) y) (e : ℕ) {d δ : M} {f g t : _} (he : E₀ C f ≤ e)
    (hf : f ∈ homog actU d) (hg : g ∈ homog actW δ) (hgi : g ∈ C.idl y)
    (ht : Lift C y f (g ^ e) t) :
    g ^ e * t ∈ homog actW (d + (e + e) • δ) := by
  classical
  let pr := spToT W (ι1 W (M := M)) contains1
  let Wm := spObj W (ι1 W (M := M)) contains1
  have hWm : IsAffine ((SCH).obj Wm) := inferInstanceAs (IsAffine (Spec _))
  let P := sec pr
  let Q := sec (univMap actW)
  let χ : Multiplicative M →* Γ((SCH).obj Wm, ⊤) := univPt1 (U := W)
  have hact : X.map (univMap actW).op y = smX actX χ (X.map pr.op y) := by
    refine hy pr (univMap actW) χ ?_
    simp only [Category.comp_id]
    rfl
  have hχu : ∀ z : Multiplicative M, χ z * χ z⁻¹ = 1 := fun z => by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hQg : Q (g ^ e) = χ (Multiplicative.ofAdd (e • δ)) * P (g ^ e) := by
    have h1 : Q g = P g * χ (Multiplicative.ofAdd δ) :=
      appTop_smul_of_mem actW pr χ hg
    rw [map_pow, map_pow, h1, mul_pow, mul_comm]
    congr 1
    rw [← map_pow, ofAdd_nsmul]
  have l₁ : Lift C (X.map pr.op y) f (P (g ^ e)) (P t) := lift_map C pr ht
  have l₂ : Lift C (smX actX χ (X.map pr.op y)) f (Q (g ^ e)) (Q t) := by
    rw [← hact]
    exact lift_map C (univMap actW) ht
  have l₃ := lift_mul_left C (χ (Multiplicative.ofAdd (e • δ))⁻¹) l₂
  have hcancel : χ (Multiplicative.ofAdd (e • δ))⁻¹ * Q (g ^ e) = P (g ^ e) := by
    rw [hQg, ← mul_assoc, mul_comm (χ _⁻¹), hχu, one_mul]
  rw [hcancel] at l₃
  have hc : P (g ^ e) ∈ C.idl (X.map pr.op y) ^ E₀ C f := by
    rw [C.idl_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_le_pow_right he (Ideal.pow_mem_pow hgi e))
  have key := lift_smul C χ hf l₁ l₃ hc
  change coact actW _ = _
  apply (spSec_bijective W (ι1 W (M := M)) contains1).1
  rw [spSec_coact]
  have hr : spSec W (ι1 W (M := M)) contains1
      (AddMonoidAlgebra.single (d + (e + e) • δ) (g ^ e * t)) =
      P (g ^ e * t) * χ (Multiplicative.ofAdd (d + (e + e) • δ)) := by
    have hs := spToT_appTop W (ι1 W (M := M)) contains1 (g ^ e * t)
    have : (AddMonoidAlgebra.single (d + (e + e) • δ) (g ^ e * t) : R1 W M) =
        ι1 W (M := M) (g ^ e * t) * AddMonoidAlgebra.of (RT W) M
          (Multiplicative.ofAdd (d + (e + e) • δ)) := by
      simp [ι1, AddMonoidAlgebra.single_mul_single]
    rw [this, map_mul]
    exact congrArg₂ _ hs.symm rfl
  rw [hr]
  change Q (g ^ e * t) = _
  rw [map_mul, hQg, map_mul]
  have e₂ : Multiplicative.ofAdd (d + (e + e) • δ) =
      Multiplicative.ofAdd d * Multiplicative.ofAdd (e • δ) * Multiplicative.ofAdd (e • δ) := by
    rw [add_nsmul, ← ofAdd_add, ← ofAdd_add, add_assoc]
  rw [e₂, map_mul, map_mul]
  have hk : P (g ^ e) * Q t = χ (Multiplicative.ofAdd (e • δ)) *
      (P (g ^ e) * (χ (Multiplicative.ofAdd d) * P t)) := by
    have k2 := key
    rw [mul_sub, sub_eq_zero] at k2
    calc P (g ^ e) * Q t = χ (Multiplicative.ofAdd (e • δ)) *
          (P (g ^ e) * (χ (Multiplicative.ofAdd (e • δ))⁻¹ * Q t)) := by
            have := hχu (Multiplicative.ofAdd (e • δ))
            linear_combination (-(P (g ^ e) * Q t)) * this
      _ = _ := by rw [k2]
  linear_combination (χ (Multiplicative.ofAdd (e • δ))) * hk

/-- The cross relation on a point. -/
lemma lift_cross {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    {y : X.obj (op W)} {f r r' t t'} (h : Lift C y f r t) (h' : Lift C y f r' t') {c}
    (hc : c ∈ C.idl y ^ E₀ C f) : c * (r' * t - r * t') = 0 := by
  have h₁ := lift_mul_left C r' h
  have h₂ := lift_mul_left C r h'
  rw [mul_comm r' r] at h₁
  exact lift_unique C h₁ h₂ hc

section System

variable [DecidableEq M] {T : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T))

/-- The closed `V(I)` of `T`. -/
noncomputable abbrev Vc (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) : BigFppfOver B S hS :=
  Chart.immObj T (Chart.closedι ((BigFppfOver.toScheme B S hS).obj T) I)

/-- Its inclusion. -/
noncomputable abbrev ιc (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) : Vc T I ⟶ T :=
  Chart.immι T (Chart.closedι ((BigFppfOver.toScheme B S hS).obj T) I)

lemma baseMap_coeff {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    (p : AddMonoidAlgebra R M) (d : M) : (baseMap g p).coeff d = g (p.coeff d) := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Finsupp.add_apply, hx, hy, map_add]
  | single e b =>
    rw [baseMap_single, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp

lemma coeff_mem_map {R : Type u} [CommRing R] (I : Ideal R) {y : AddMonoidAlgebra R M}
    (hy : y ∈ I.map (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R M)) (d : M) :
    y.coeff d ∈ I := by
  have hle : I.map (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R M) ≤
      RingHom.ker (baseMap (M' := M) (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change baseMap (Ideal.Quotient.mk I) (AddMonoidAlgebra.single (0 : M) r) = 0
    rw [baseMap_single, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    simp
  have h0 : baseMap (M' := M) (Ideal.Quotient.mk I) y = 0 := hle hy
  have := baseMap_coeff (Ideal.Quotient.mk I) y d
  rw [h0] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using this.symm)

/-- `Γ(W)[M] = Γ(gm W)`, for the evaluation at the universal point. -/
lemma spSec_baseMap {W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] {R : Type u}
    [CommRing R] (ρ : R →+* Γ((SCH).obj W, ⊤)) (p : AddMonoidAlgebra R M) :
    spSec W (ι1 W (M := M)) contains1 (baseMap ρ p) =
      evalAt ((sec (gmπ (M := M) W)).comp ρ) (univPt1 (U := W)) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | single e b =>
    rw [baseMap_single, evalAt_single]
    have : (AddMonoidAlgebra.single e (ρ b) : R1 W M) =
        ι1 W (M := M) (ρ b) * AddMonoidAlgebra.of (RT W) M (Multiplicative.ofAdd e) := by
      simp [ι1, AddMonoidAlgebra.single_mul_single]
    rw [this, map_mul]
    exact congrArg₂ _ (spToT_appTop W (ι1 W (M := M)) contains1 (ρ b)).symm rfl

/-- Equivariant `y` on a stable closed `V(J)`: `idl y` pulled back to `T` is closed under components. -/
theorem comap_idl_coeff {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (y : X.obj (op (Vc T J)))
    (hy : ∀ t' : gmObj (M := M) (Vc T J) ⟶ Vc T J,
      t' ≫ ιc T J = smulAt actT (univPt1 (U := Vc T J)) (gmπ (M := M) (Vc T J) ≫ ιc T J) →
      X.map t'.op y = smX actX (univPt1 (U := Vc T J)) (X.map (gmπ (M := M) (Vc T J)).op y))
    {c : Γ((SCH).obj T, ⊤)} (hc : (sec (ιc T J)) c ∈ C.idl y) (d : M) :
    (sec (ιc T J)) ((coact actT c).coeff d) ∈ C.idl y := by
  classical
  let W := Vc T J
  let t : gmObj (M := M) W ⟶ W := gmπ (M := M) W
  let h : Multiplicative M →* Γ((SCH).obj (gmObj (M := M) W), ⊤) := univPt1 (U := W)
  obtain ⟨t', ht'⟩ := exists_factor_closed (smulAt actT h (t ≫ ιc T J)) J (fun z hz =>
    appTop_smul_eq_zero actT (t ≫ ιc T J) h J hJ (fun z hz => by
      have hz0 : (sec (ιc T J)) z = 0 := closedι_appTop_of_mem J hz
      change (sec (t ≫ ιc T J)) z = 0
      rw [sec_comp, hz0, map_zero]) hz)
  have hact := hy t' ht'
  have e : (C.idl y).map (sec t') = (C.idl y).map (sec t) := by
    rw [← C.idl_map, hact]
    exact (C.idl_smul h _).trans (C.idl_map t y)
  have h1 : (sec t') ((sec (ιc T J)) c) ∈ (C.idl y).map (sec t) := by
    rw [← e]; exact Ideal.mem_map_of_mem _ hc
  rw [← sec_comp, ht', appTop_smul] at h1
  let σ := spSec W (ι1 W (M := M)) contains1
  have hb := spSec_bijective W (ι1 W (M := M)) contains1
  let y' : R1 W M := baseMap (sec (ιc T J)) (coact actT c)
  have hy' : σ y' = evalAt ((SCH).map (t ≫ ιc T J)).appTop.hom h (coact actT c) := by
    refine (spSec_baseMap (sec (ιc T J)) (coact actT c)).trans ?_
    congr 1
  have hmap : (C.idl y).map (sec t) = ((C.idl y).map (ι1 W (M := M))).map σ := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun b => (spToT_appTop W (ι1 W (M := M)) contains1 b)
  rw [← hy', hmap] at h1
  have h2 : y' ∈ (C.idl y).map (ι1 W (M := M)) := by
    have := Ideal.comap_map_of_bijective _ hb (I := (C.idl y).map (ι1 W (M := M)))
    rw [← this]
    exact h1
  have h3 := coeff_mem_map (C.idl y) h2 d
  rwa [baseMap_coeff] at h3

section IdealA

variable {m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} {actT}
  (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
  (x : ∀ n, X.obj (op (Vc T (m ^ n)))) (hx : IsEquivSystem actT actX m x)

include hP in
lemma pow_coeff (n : ℕ) (c) (hc : c ∈ m ^ n) (d : M) : (coact actT c).coeff d ∈ m ^ n := by
  letI := gradedRingOfAction actT
  exact coeff_mem_of_isHomogeneous actT (ChartGraded.pow_homogeneous hP.hom n) hc d

/-- `A n`, the preimage in `C` of `J·C/mⁿ`. -/
noncomputable def An (n : ℕ) : Ideal Γ((SCH).obj T, ⊤) :=
  (C.idl (x n)).comap (sec (ιc T (m ^ n)))

omit [AddMonoid.FG M] in
lemma ιc_surj (I : Ideal Γ((SCH).obj T, ⊤)) : Function.Surjective (sec (ιc T I)) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine (Chart.closedι ((SCH).obj T) I)).2

omit [AddMonoid.FG M] in
lemma ιc_ker (I : Ideal Γ((SCH).obj T, ⊤)) (c) : (sec (ιc T I)) c = 0 ↔ c ∈ I :=
  ⟨fun h => Chart.closedι_appTop_eq_zero _ c h, fun h => closedι_appTop_of_mem _ h⟩

lemma An_ge (n : ℕ) : m ^ n ≤ An C x n := fun c hc => by
  have : (sec (ιc T (m ^ n))) c = 0 := (ιc_ker _ c).2 hc
  rw [An, Ideal.mem_comap, this]
  exact zero_mem _

include hP hx in
lemma An_hom (n : ℕ) : letI := gradedRingOfAction actT; (An C x n).IsHomogeneous (homog actT) := by
  letI := gradedRingOfAction actT
  intro d c hc
  rw [decompose_eq_coeff, An, Ideal.mem_comap]
  exact comap_idl_coeff C actT (pow_coeff hP n) (x n)
    (fun t' ht' => hx.equiv n _ t' _ ht') hc d

lemma ring_succ {C₀ D₁ D₀ : Type*} [CommRing C₀] [CommRing D₁] [CommRing D₀] (π₁ : C₀ →+* D₁)
    (e : D₁ →+* D₀) (π₀ : C₀ →+* D₀) (hπ : ∀ c, π₀ c = e (π₁ c)) (hs : Function.Surjective π₁)
    (I₁ : Ideal D₁) (I₀ : Ideal D₀) (hid : I₀ = I₁.map e) (mp : Ideal C₀)
    (hk : ∀ c, π₀ c = 0 ↔ c ∈ mp) (hs₀ : Function.Surjective π₀) :
    I₁.comap π₁ ⊔ mp = I₀.comap π₀ := by
  subst hid
  have hes : Function.Surjective e := fun w => by
    obtain ⟨c, rfl⟩ := hs₀ w
    exact ⟨_, (hπ c).symm⟩
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro c hc
    rw [Ideal.mem_comap, hπ]
    exact Ideal.mem_map_of_mem _ hc
  · intro c hc
    rw [Ideal.mem_comap, (hk c).2 hc]
    exact zero_mem _
  · intro c hc
    rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective _ hes] at hc
    obtain ⟨w, hw, hwe⟩ := hc
    obtain ⟨c', rfl⟩ := hs w
    refine Submodule.mem_sup.2 ⟨c', hw, c - c', ?_, by ring⟩
    rw [← hk, map_sub, hπ c', hwe, sub_self]

include hx in
set_option maxHeartbeats 1000000 in
lemma An_succ (n : ℕ) : An C x (n + 1) ⊔ m ^ n = An C x n := by
  obtain ⟨e, he⟩ := exists_factor_closed (ιc T (m ^ n)) (m ^ (n + 1)) (fun c hc =>
    closedι_appTop_of_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) hc))
  have hxe : X.map e.op (x (n + 1)) = x n := hx.compat n (n + 1) e he
  have hπ : ∀ c, (sec (ιc T (m ^ n))) c = (sec e) ((sec (ιc T (m ^ (n + 1)))) c) := fun c => by
    rw [← sec_comp]; exact congrArg (fun k => (sec k) c) he.symm
  have hid : C.idl (x n) = (C.idl (x (n + 1))).map (sec e) := by
    rw [← C.idl_map, hxe]
  exact ring_succ _ _ _ hπ (ιc_surj _) _ _ hid _ (fun c => ιc_ker _ c) (ιc_surj _)

include hP hx in
set_option maxHeartbeats 2000000 in
/-- **§4, setup**: the ideal `a` with `J·C/mⁿ = a·C/mⁿ`. -/
theorem exists_ideal : ∃ (a : Ideal Γ((SCH).obj T, ⊤)) (gens : Set Γ((SCH).obj T, ⊤)),
    a = Ideal.span gens ∧ (∀ g ∈ gens, ∃ d, g ∈ homog actT d) ∧
    (∀ k, ∀ y ∈ a ^ k, ∀ d, (coact actT y).coeff d ∈ a ^ k) ∧
    ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))) := by
  classical
  letI := gradedRingOfAction actT
  have hsup := ChartGraded.limIdeal_sup hP (An C x) (An_ge C x) (An_hom C hP x hx) (An_succ C x hx)
  refine ⟨ChartGraded.limIdeal (homog actT) (An C x), _, rfl, fun g hg => hg.1, fun k y hy d => ?_,
    fun n => ?_⟩
  · have hk := ChartGraded.limIdeal_pow_homogeneous (𝒞 := homog actT) (An C x) k
    exact coeff_mem_of_isHomogeneous actT hk hy d
  · have h1 : (An C x n).map (sec (ιc T (m ^ n))) = C.idl (x n) :=
      Ideal.map_comap_of_surjective _ (ιc_surj _) _
    rw [← h1, ← hsup n, Ideal.map_sup]
    have h2 : (m ^ n).map (sec (ιc T (m ^ n))) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      exact fun c hc => (ιc_ker _ c).2 hc
    rw [h2, sup_bot_eq]

end IdealA

section Elements

variable {m : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} {actT}
  (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
  (x : ∀ n, X.obj (op (Vc T (m ^ n)))) (hx : IsEquivSystem actT actX m x)
  (a : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (hax : ∀ n, C.idl (x n) = a.map (sec (ιc T (m ^ n))))

/-- `t = r f` modulo each `mⁿ`. -/
def LL (f : Γ((SCH).obj U₀, ⊤)) (r t : Γ((SCH).obj T, ⊤)) : Prop :=
  ∀ n, Lift C (x n) f ((sec (ιc T (m ^ n))) r) ((sec (ιc T (m ^ n))) t)

variable {x} in
set_option maxHeartbeats 1000000 in
lemma LL.mul_left {f r t} (c) (h : LL C x f r t) : LL C x f (c * r) (c * t) := fun n => by
  rw [map_mul, map_mul]
  exact lift_mul_left C _ (h n)

variable {x} in
set_option maxHeartbeats 1000000 in
lemma LL.add {f f' r r' t t'} (h : LL C x f r t) (h' : LL C x f' r' t') :
    LL C x (f + f') (r * r') (t * r' + r * t') := fun n => by
  have := lift_add' C (h n) (h' n)
  simpa only [map_mul, map_add] using this

variable {x} in
set_option maxHeartbeats 1000000 in
lemma LL.mul {f f' r r' t t'} (h : LL C x f r t) (h' : LL C x f' r' t') :
    LL C x (f * f') (r * r') (t * t') := fun n => by
  rw [map_mul, map_mul]
  exact lift_mul C (h n) (h' n)

include hP in
/-- `∩ mⁿ = 0`. -/
lemma sep_of (z : Γ((SCH).obj T, ⊤)) (hz : ∀ n, (sec (ιc T (m ^ n))) z = 0) : z = 0 := by
  letI := gradedRingOfAction actT
  have h := Chart.iInf_pow_eq_bot (homog actT) m hP.hom hP.sep
  have : z ∈ ⨅ n : ℕ, m ^ n := Ideal.mem_iInf.2 fun n => (ιc_ker _ z).1 (hz n)
  rw [h] at this
  exact this

variable {x a} in
include hP hax in
set_option maxHeartbeats 2000000 in
/-- Uniqueness in `C`. -/
lemma LL.unique {f r t t'} (h : LL C x f r t) (h' : LL C x f r t') {c} (hc : c ∈ a ^ E₀ C f) :
    c * (t - t') = 0 := by
  refine sep_of hP _ fun n => ?_
  rw [map_mul, map_sub]
  refine lift_unique C (h n) (h' n) ?_
  have e : ∀ k, C.idl (x n) ^ k = (a ^ k).map (sec (ιc T (m ^ n))) := fun k => by
    rw [hax, Ideal.map_pow]
  rw [e]
  exact Ideal.mem_map_of_mem _ hc

variable {x a} in
include hP hax in
/-- **The cross relation in `C`.** -/
lemma LL.cross {f r r' t t'} (h : LL C x f r t) (h' : LL C x f r' t') {c} (hc : c ∈ a ^ E₀ C f) :
    c * (r' * t - r * t') = 0 := by
  have h₁ := h.mul_left C r'
  have h₂ := h'.mul_left C r
  rw [mul_comm r' r] at h₁
  exact LL.unique C hP hax h₁ h₂ hc

variable {x a} in
include hP hx hax in
set_option maxHeartbeats 16000000 in
/-- **Lemma 4.3, the element of `C`.** -/
theorem exists_LL_homog {d δ : M} {f g} (hf : f ∈ homog actU d) (hg : g ∈ homog actT δ) (hga : g ∈ a) :
    ∃ t ∈ homog actT (d + (expo C f + expo C f) • δ), LL C x f (g ^ (expo C f + expo C f)) t := by
  classical
  letI := gradedRingOfAction actT
  set e := expo C f with he
  have hJ := fun n => pow_coeff (m := m) (actT := actT) hP n
  have hge : E₀ C f ≤ e := Nat.le_add_left _ _
  have hgi : ∀ n, (sec (ιc T (m ^ n))) g ∈ C.idl (x n) := fun n => by
    rw [hax]; exact Ideal.mem_map_of_mem _ hga
  have hgp : ∀ n, (sec (ιc T (m ^ n))) g ^ e ∈ C.idl (x n) ^ e := fun n =>
    Ideal.pow_mem_pow (hgi n) _
  choose t' ht' using fun n => lift_exists C (x n) f (hgp n)
  have hgh : ∀ n, (sec (ιc T (m ^ n))) g ∈ homog (closedAct actT (hJ n)) δ := fun n => by
    have heq : IsEquivariant (closedAct actT (hJ n)) actT (yoneda.map (ιc T (m ^ n))) :=
      fun {_} h t => closedAct_spec actT (hJ n) h t
    exact map_mem_homog _ _ heq hg
  have hcl : ∀ n, EquivAlong (closedAct actT (hJ n)) actX (𝟙 _) (x n) := fun n => by
    intro W s s' h hs
    refine hx.equiv n s s' h ?_
    rw [Category.comp_id] at hs
    rw [hs]
    exact closedAct_spec actT (hJ n) h s
  have hw : ∀ n, ∃ c ∈ homog actT (d + (e + e) • δ), (sec (ιc T (m ^ n))) c =
      (sec (ιc T (m ^ n))) g ^ e * t' n := fun n =>
    exists_homog_lift actT (hJ n)
      (homog_lift C (closedAct actT (hJ n)) (x n) (hcl n) e hge hf (hgh n) (hgi n) (ht' n))
  choose c hc hcπ using hw
  have hq : ∀ n, ∃ q : Vc T (m ^ n) ⟶ Vc T (m ^ (n + 1)), q ≫ ιc T _ = ιc T _ := fun n =>
    exists_factor_closed (ιc T (m ^ n)) (m ^ (n + 1)) (fun z hz => closedι_appTop_of_mem _
      (Ideal.pow_le_pow_right (Nat.le_succ n) hz))
  choose q hq using hq
  have hmap : ∀ n z, (sec (q n)) ((sec (ιc T (m ^ (n + 1)))) z) = (sec (ιc T (m ^ n))) z :=
    fun n z => by rw [← sec_comp]; exact congrArg (fun k => (sec k) z) (hq n)
  have hdiff : ∀ n, c (n + 1) - c n ∈ m ^ n := fun n => by
    refine (ιc_ker _ _).1 ?_
    have l := lift_map C (q n) (ht' (n + 1))
    rw [hx.compat n (n + 1) (q n) (hq n), map_pow, hmap] at l
    have u := lift_unique C l (ht' n) (Ideal.pow_le_pow_right hge (hgp n))
    have e1 := congrArg (sec (q n)) (hcπ (n + 1))
    rw [hmap, map_mul, map_pow, hmap] at e1
    rw [map_sub, e1, hcπ]
    linear_combination u

  obtain ⟨z, hz, hzn⟩ := hP.exists_lim _ c hc hdiff
  refine ⟨z, hz, fun n => ?_⟩
  have h2 : (sec (ιc T (m ^ n))) z = (sec (ιc T (m ^ n))) g ^ e * t' n := by
    have := (ιc_ker _ _).2 (hzn n)
    rw [map_sub, sub_eq_zero, hcπ] at this
    exact this
  rw [h2, pow_add, map_mul, map_pow]
  exact lift_mul_left C _ (ht' n)

variable {x a} in
include hP hx hax in
/-- For any `f`. -/
theorem exists_LL {g} {δ : M} (hg : g ∈ homog actT δ) (hga : g ∈ a) (f) :
    ∃ (N : ℕ) (t : _), LL C x f (g ^ N) t := by
  classical
  letI := gradedRingOfAction actU
  induction f using DirectSum.Decomposition.inductionOn (homog actU) with
  | zero =>
    refine ⟨0, 0, fun n => ?_⟩
    simp only [pow_zero, map_one, map_zero]
    exact lift_one_of C (x n) 0 0 (fun W c y₀ _ => by simp) 0 (by simp)
  | homogeneous f =>
    obtain ⟨t, -, ht⟩ := exists_LL_homog C hP hx hax f.2 hg hga
    exact ⟨_, t, ht⟩
  | add f f' hf hf' =>
    obtain ⟨N, t, ht⟩ := hf
    obtain ⟨N', t', ht'⟩ := hf'
    refine ⟨N + N', t * g ^ N' + g ^ N * t', ?_⟩
    rw [pow_add]
    exact ht.add C ht'

end Elements

end System

end AlgMag.ChartMain.DeligneInst
