/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveInduct

/-!
# Lemma 4.3 of the chart-lemma proof: Deligne's formula on graded rings

`AlgMag.ChartDeligne.DeligneCalc` records what Deligne's formula gives on points `y : W → X`:
`Lift y f r t` reads "`t` is the value at `r` of the pullback along `y` of an extension
`ψ : J^N → O_X` of `f`".
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Lemma 4.3, the formula on points.** Here `U₀` is the affine open stratum with inclusion `u`. -/
structure DeligneCalc (actX : AAction (fppfO B S hS) M X) {U₀ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] (actU : AAction (fppfO B S hS) M (yoneda.obj U₀)) (u : X.obj (op U₀)) where
  /-- `J·Γ(W)`. -/
  ideal : ∀ {W : BigFppfOver B S hS}, X.obj (op W) → Ideal Γ((SCH).obj W, ⊤)
  /-- `t = y^*ψ_f (r)`. -/
  Lift : ∀ {W : BigFppfOver B S hS}, X.obj (op W) → Γ((SCH).obj U₀, ⊤) →
    Γ((SCH).obj W, ⊤) → Γ((SCH).obj W, ⊤) → Prop
  /-- the pole order of `f` -/
  exp : Γ((SCH).obj U₀, ⊤) → ℕ
  ideal_map : ∀ {W W' : BigFppfOver B S hS} (q : W' ⟶ W) (y : X.obj (op W)),
    ideal (X.map q.op y) = (ideal y).map ((SCH).map q).appTop.hom
  ideal_smul : ∀ {W : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj W, ⊤))
    (y : X.obj (op W)), ideal (actX.smul (F := X) (U := op W) h y) = ideal y
  lift_map : ∀ {W W' : BigFppfOver B S hS} (q : W' ⟶ W) {y : X.obj (op W)} {f r t},
    Lift y f r t → Lift (X.map q.op y) f (((SCH).map q).appTop.hom r) (((SCH).map q).appTop.hom t)
  lift_exists : ∀ {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] (y : X.obj (op W)) (f r),
    r ∈ ideal y ^ exp f → ∃ t, Lift y f r t
  lift_unique : ∀ {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] {y : X.obj (op W)} {f r t t'},
    Lift y f r t → Lift y f r t' → ∀ c ∈ ideal y ^ exp f, c * (t - t') = 0
  lift_mul_left : ∀ {W : BigFppfOver B S hS} {y : X.obj (op W)} {f r t} (c : Γ((SCH).obj W, ⊤)),
    Lift y f r t → Lift y f (c * r) (c * t)
  lift_smul : ∀ {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)] {y : X.obj (op W)} {d f r t t'}
    (h : Multiplicative M →* Γ((SCH).obj W, ⊤)), f ∈ homog actU d → Lift y f r t →
    Lift (actX.smul (F := X) (U := op W) h y) f r t' →
    ∀ c ∈ ideal y ^ exp f, c * (t' - h (Multiplicative.ofAdd d) * t) = 0

section Point

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)} {u : X.obj (op U₀)}
  (K : DeligneCalc actX actU u)

/-- **Lemma 4.3, homogeneity.** On an affine `W` with action and an equivariant point `y`, the lift of
`g^e` for `g` of degree `δ` gives after multiplying by `g^e` an element of degree `d + 2eδ`. -/
theorem homog_of_lift {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)]
    (actW : AAction (fppfO B S hS) M (yoneda.obj W)) (y : X.obj (op W))
    (hy : EquivAlong actW actX (𝟙 W) y) {d δ : M} {f g t : _}
    (hf : f ∈ homog actU d) (hg : g ∈ homog actW δ) (hgi : g ∈ K.ideal y)
    (ht : K.Lift y f (g ^ K.exp f) t) :
    g ^ K.exp f * t ∈ homog actW (d + (K.exp f + K.exp f) • δ) := by
  classical
  set e := K.exp f with he
  let pr := spToT W (ι1 W (M := M)) contains1
  let Wm := spObj W (ι1 W (M := M)) contains1
  have hWm : IsAffine ((SCH).obj Wm) := inferInstanceAs (IsAffine (Spec _))
  let P := ((SCH).map pr).appTop.hom
  let Q := ((SCH).map (univMap actW)).appTop.hom
  let χ : Multiplicative M →* Γ((SCH).obj Wm, ⊤) := univPt1 (U := W)
  have hact : X.map (univMap actW).op y = actX.smul (F := X) (U := op Wm) χ (X.map pr.op y) := by
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
  have l₁ : K.Lift (X.map pr.op y) f (P (g ^ e)) (P t) := K.lift_map pr ht
  have l₂ : K.Lift (actX.smul (F := X) (U := op Wm) χ (X.map pr.op y)) f
      (Q (g ^ e)) (Q t) := by
    rw [← hact]
    exact K.lift_map (univMap actW) ht
  have l₃ := K.lift_mul_left (χ (Multiplicative.ofAdd (e • δ))⁻¹) l₂
  have hcancel : χ (Multiplicative.ofAdd (e • δ))⁻¹ * Q (g ^ e) = P (g ^ e) := by
    rw [hQg, ← mul_assoc, mul_comm (χ _⁻¹), hχu, one_mul]
  rw [hcancel] at l₃
  have hc : P (g ^ e) ∈ K.ideal (X.map pr.op y) ^ K.exp f := by
    rw [K.ideal_map, ← Ideal.map_pow, ← he]
    exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hgi e)
  have key := K.lift_smul χ hf l₁ l₃ _ hc
  -- `key : P(g^e) * (χ(-eδ) Q t - χ(d) P t) = 0`
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

/-- `lift_unique` as an equality. -/
theorem DeligneCalc.mul_eq_of_lift {W : BigFppfOver B S hS} [IsAffine ((SCH).obj W)]
    {y : X.obj (op W)} {f r t t' c} (h : K.Lift y f r t) (h' : K.Lift y f r t')
    (hc : c ∈ K.ideal y ^ K.exp f) : c * t = c * t' := by
  have := K.lift_unique h h' c hc
  rwa [mul_sub, sub_eq_zero] at this

/-- One step of the tower: `c` restricting to `g^e t` at `W` restricts to `g^e t'` at `W'`. -/
theorem DeligneCalc.lift_step {T W W' : BigFppfOver B S hS} [IsAffine ((SCH).obj W')]
    (q : W' ⟶ W) (i : W ⟶ T) (i' : W' ⟶ T) (hq : q ≫ i = i') {y : X.obj (op W)}
    {y' : X.obj (op W')} (hy : X.map q.op y = y') {f t t'} {g c : Γ((SCH).obj T, ⊤)}
    (h : K.Lift y f (((SCH).map i).appTop.hom g ^ K.exp f) t)
    (h' : K.Lift y' f (((SCH).map i').appTop.hom g ^ K.exp f) t')
    (hg : ((SCH).map i').appTop.hom g ^ K.exp f ∈ K.ideal y' ^ K.exp f)
    (hc : ((SCH).map i).appTop.hom c = ((SCH).map i).appTop.hom g ^ K.exp f * t) :
    ((SCH).map i').appTop.hom c = ((SCH).map i').appTop.hom g ^ K.exp f * t' := by
  subst hq hy
  have hQ : ∀ z, ((SCH).map (q ≫ i)).appTop.hom z =
      ((SCH).map q).appTop.hom (((SCH).map i).appTop.hom z) := fun z => by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have l := K.lift_map q h
  rw [map_pow, ← hQ] at l
  rw [hQ c, hc, map_mul, map_pow, ← hQ]
  exact K.mul_eq_of_lift l h' hg

end Point

section Limit

variable [DecidableEq M] {T : BigFppfOver B S hS} [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (actT : AAction (fppfO B S hS) M (yoneda.obj T))

/-- The component of degree `d` is the coefficient of the coaction. -/
lemma decompose_eq_coeff (a : Γ((SCH).obj T, ⊤)) (d : M) :
    letI := gradedRingOfAction actT
    (DirectSum.decompose (homog actT) a d : Γ((SCH).obj T, ⊤)) = (coact actT a).coeff d := by
  classical
  letI := gradedRingOfAction actT
  have hmem : ∀ e, (coact actT a).coeff e ∈ homog actT e := fun e => coact_coeff actT a e
  have hsum : a = ∑ e ∈ (coact actT a).coeff.support, (coact actT a).coeff e := by
    conv_lhs => rw [← sum_coact actT a]
    rfl
  conv_lhs => rw [hsum]
  rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  have hc : ∀ e, ((DirectSum.decompose (homog actT) ((coact actT a).coeff e)) d :
      Γ((SCH).obj T, ⊤)) = if e = d then (coact actT a).coeff e else 0 := by
    intro e
    split_ifs with h
    · subst h; exact DirectSum.decompose_of_mem_same _ (hmem e)
    · exact DirectSum.decompose_of_mem_ne _ (hmem e) h
  simp only [hc, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact (not_not.1 h).symm

/-- A homogeneous ideal is closed under coefficients of the coaction. -/
lemma coeff_mem_of_isHomogeneous {J : Ideal Γ((SCH).obj T, ⊤)}
    (hJ : letI := gradedRingOfAction actT; J.IsHomogeneous (homog actT))
    {x : Γ((SCH).obj T, ⊤)} (hx : x ∈ J) (d : M) : (coact actT x).coeff d ∈ J := by
  letI := gradedRingOfAction actT
  rw [← decompose_eq_coeff]
  exact hJ d hx

/-- The closed `V(J)`, with the equivariant inclusion: a homogeneous lift of a homogeneous element. -/
lemma exists_homog_lift {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    {D : M} {w : Γ((SCH).obj (Chart.immObj T (Chart.closedι ((SCH).obj T) J)), ⊤)}
    (hw : w ∈ homog (closedAct actT hJ) D) :
    ∃ c ∈ homog actT D, ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom c = w := by
  classical
  letI := gradedRingOfAction actT
  letI := gradedRingOfAction (closedAct actT hJ)
  have heq : IsEquivariant (closedAct actT hJ) actT
      (yoneda.map (Chart.immι T (Chart.closedι ((SCH).obj T) J))) :=
    fun {_} h t => closedAct_spec actT hJ h t
  let ρ := ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom
  have hsurj : Function.Surjective ρ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (Chart.closedι ((SCH).obj T) J)).2
  obtain ⟨c, hc⟩ := hsurj w
  refine ⟨_, SetLike.coe_mem (DirectSum.decompose (homog actT) c D), ?_⟩
  rw [← decompose_map (homog actT) (homog (closedAct actT hJ)) ρ
    (fun d a ha => map_mem_homog _ _ heq ha), hc, DirectSum.decompose_of_mem_same _ hw]

variable {actX : AAction (fppfO B S hS) M X} {U₀ : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  {actU : AAction (fppfO B S hS) M (yoneda.obj U₀)} {u : X.obj (op U₀)}
  (K : DeligneCalc actX actU u)

/-- `homog_of_lift` on a stable closed `V(J)`. -/
theorem closed_homog {J : Ideal Γ((SCH).obj T, ⊤)} (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (y : X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) J))))
    (hy : EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) J)) y)
    {d δ : M} {f : Γ((SCH).obj U₀, ⊤)} {g : Γ((SCH).obj T, ⊤)} {t}
    (hf : f ∈ homog actU d) (hg : g ∈ homog actT δ)
    (hgi : ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom g ∈ K.ideal y)
    (ht : K.Lift y f (((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom g ^ K.exp f) t) :
    ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) J))).appTop.hom g ^ K.exp f * t ∈
      homog (closedAct actT hJ) (d + (K.exp f + K.exp f) • δ) := by
  have heq : IsEquivariant (closedAct actT hJ) actT
      (yoneda.map (Chart.immι T (Chart.closedι ((SCH).obj T) J))) :=
    fun {_} h t => closedAct_spec actT hJ h t
  refine homog_of_lift K (closedAct actT hJ) y ?_ hf (map_mem_homog _ _ heq hg) hgi ht
  intro W s s' h hs
  refine hy s s' h ?_
  rw [Category.comp_id] at hs
  rw [hs]
  exact closedAct_spec actT hJ h s

/-- The limit along an abstract tower `Wₙ → T` with kernels `mⁿ`. -/
theorem exists_limit_tower {m : Ideal Γ((SCH).obj T, ⊤)}
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
    (W : ℕ → BigFppfOver B S hS) [∀ n, IsAffine ((SCH).obj (W n))] (i : ∀ n, W n ⟶ T)
    (q : ∀ n, W n ⟶ W (n + 1)) (hq : ∀ n, q n ≫ i (n + 1) = i n)
    (y : ∀ n, X.obj (op (W n))) (hy : ∀ n, X.map (q n).op (y (n + 1)) = y n)
    (hker : ∀ n c, ((SCH).map (i n)).appTop.hom c = 0 ↔ c ∈ m ^ n)
    {D : M} {f : Γ((SCH).obj U₀, ⊤)} {g : Γ((SCH).obj T, ⊤)}
    (hgp : ∀ n, ((SCH).map (i n)).appTop.hom g ^ K.exp f ∈ K.ideal (y n) ^ K.exp f)
    (hw : ∀ n t', K.Lift (y n) f (((SCH).map (i n)).appTop.hom g ^ K.exp f) t' →
      ∃ c ∈ homog actT D, ((SCH).map (i n)).appTop.hom c =
        ((SCH).map (i n)).appTop.hom g ^ K.exp f * t') :
    ∃ t ∈ homog actT D, ∀ n t', K.Lift (y n) f (((SCH).map (i n)).appTop.hom g ^ K.exp f) t' →
      ((SCH).map (i n)).appTop.hom t = ((SCH).map (i n)).appTop.hom g ^ K.exp f * t' := by
  classical
  letI := gradedRingOfAction actT
  choose t' ht' using fun n => K.lift_exists (y n) f _ (hgp n)
  choose c hc hcπ using fun n => hw n _ (ht' n)
  have hstep : ∀ n, ((SCH).map (i n)).appTop.hom (c (n + 1)) =
      ((SCH).map (i n)).appTop.hom g ^ K.exp f * t' n := fun n =>
    K.lift_step (q n) (i (n + 1)) (i n) (hq n) (hy n) (ht' (n + 1)) (ht' n) (hgp n) (hcπ (n + 1))
  obtain ⟨z, hz, hzn⟩ := hP.exists_lim D c hc (fun n => (hker n _).1 (by
    rw [map_sub, hstep, hcπ, sub_self]))
  refine ⟨z, hz, fun n s hs => ?_⟩
  have h2 := (hker n _).2 (hzn n)
  rw [map_sub, sub_eq_zero, hcπ] at h2
  exact h2.trans (K.mul_eq_of_lift hs (ht' n) (hgp n)).symm

set_option maxHeartbeats 2000000 in
/-- **Lemma 4.3, the element of `C`.** For a compatible equivariant system on a complete pair with
`J·C/mⁿ = a·C/mⁿ`, `f` of degree `d` and `g ∈ a` of degree `δ`, there is `t ∈ C` of degree
`d + 2eδ`, `e` the pole order of `f`, which modulo each `mⁿ` is `g^e` times the formula at `g^e`. -/
theorem exists_limit_lift {m : Ideal Γ((SCH).obj T, ⊤)}
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (hx : IsEquivSystem actT actX m x) (a : Ideal Γ((SCH).obj T, ⊤))
    (hax : ∀ n, K.ideal (x n) = a.map ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))).appTop.hom)
    {d δ : M} {f : Γ((SCH).obj U₀, ⊤)} {g : Γ((SCH).obj T, ⊤)} (hf : f ∈ homog actU d)
    (hg : g ∈ homog actT δ) (hga : g ∈ a) :
    ∃ t ∈ homog actT (d + (K.exp f + K.exp f) • δ), ∀ n t',
      K.Lift (x n) f (((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))).appTop.hom g ^ K.exp f) t' →
      ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))).appTop.hom t =
        ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))).appTop.hom g ^ K.exp f * t' := by
  classical
  have hJ : ∀ n, ∀ x ∈ m ^ n, ∀ d, (coact actT x).coeff d ∈ m ^ n := fun n x hx d => by
    letI := gradedRingOfAction actT
    exact coeff_mem_of_isHomogeneous actT (ChartGraded.pow_homogeneous hP.hom n) hx d
  have hgi : ∀ n, ((SCH).map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))).appTop.hom g ∈
      K.ideal (x n) := fun n => by
    rw [hax]; exact Ideal.mem_map_of_mem _ hga
  have hq : ∀ n, ∃ q : Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)) ⟶
      Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ (n + 1))),
      q ≫ Chart.immι T _ = Chart.immι T _ := fun n =>
    exists_factor_closed (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n)))
      (m ^ (n + 1)) (fun c hc => closedι_appTop_of_mem (m ^ n)
        (Ideal.pow_le_pow_right (Nat.le_succ n) hc))
  choose q hq using hq
  refine exists_limit_tower actT K hP (fun n => Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))
    (fun n => Chart.immι T _) q hq x (fun n => hx.compat n (n + 1) (q n) (hq n))
    (fun n c => ⟨fun h => Chart.closedι_appTop_eq_zero _ c h,
      fun h => closedι_appTop_of_mem _ h⟩)
    (fun n => Ideal.pow_mem_pow (hgi n) _) fun n t' ht' =>
    exists_homog_lift actT (hJ n) (closed_homog actT K (hJ n) (x n) (hx.equiv n) hf hg (hgi n) ht')

end Limit

end AlgMag.ChartMain
