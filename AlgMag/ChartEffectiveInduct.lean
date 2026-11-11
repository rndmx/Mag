/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartEffectiveBridge

/-!
# Lemma 4.4 of the chart-lemma proof

* `AlgMag.ChartMain.Effective`: the conclusion of Theorem 4.1 for `X`, the statement of the
  noetherian induction.
* `AlgMag.ChartMain.lemma44`: by induction, the maps `T^(k) → Z^(k) → X`, equivariant along `V(J)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A compatible equivariant system `φₙ : Spec C/mⁿ → X` (Theorem 4.1). -/
structure IsEquivSystem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    (actX : AAction (fppfO B S hS) M X) (m : Ideal Γ((SCH).obj T, ⊤))
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))))) : Prop where
  compat : ∀ (n k : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)) ⟶
      Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ k))),
      e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (x k) = x n
  equiv : ∀ n, EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))) (x n)

/-- **Theorem 4.1, existence, for `X`.** -/
def Effective {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (actX : AAction (fppfO B S hS) M X) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (m : Ideal Γ((SCH).obj T, ⊤)),
    (letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m) →
    ∀ x, IsEquivSystem actT actX m x →
    ∃ φ : X.obj (op T),
      (∀ n, X.map (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ n))).op φ = x n) ∧
      ∀ {W : BigFppfOver B S hS} (t : W ⟶ T) (h : Multiplicative M →* Γ((SCH).obj W, ⊤)),
        X.map (smulAt actT h t).op φ = actX.smul (F := X) (U := op W) h (X.map t.op φ)

variable {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
  [hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

set_option maxHeartbeats 4000000 in
/-- Any two truncations of a system agree on a common source. -/
lemma IsEquivSystem.agree {actT : AAction (fppfO B S hS) M (yoneda.obj T)}
    {actX : AAction (fppfO B S hS) M X} {m : Ideal Γ((SCH).obj T, ⊤)}
    {x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))))}
    (hx : IsEquivSystem actT actX m x) {W : BigFppfOver B S hS} {n k : ℕ}
    (a : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))
    (b : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ k)))
    (hab : a ≫ Chart.immι T _ = b ≫ Chart.immι T _) : X.map a.op (x n) = X.map b.op (x k) := by
  have hto : ∀ r, n + k ≥ r → ∃ e : Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ r)) ⟶
      Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ (n + k))),
      e ≫ Chart.immι T _ = Chart.immι T _ := fun r hr =>
    exists_factor_closed (Chart.immι T (Chart.closedι ((SCH).obj T) (m ^ r))) (m ^ (n + k))
      fun c hc => closedι_appTop_of_mem (m ^ r) (Ideal.pow_le_pow_right hr hc)
  obtain ⟨e₁, he₁⟩ := hto n (Nat.le_add_right n k)
  obtain ⟨e₂, he₂⟩ := hto k (Nat.le_add_left k n)
  have := mono_immι (T := T) (m ^ (n + k))
  have e : a ≫ e₁ = b ≫ e₂ := (cancel_mono (Chart.immι T _)).1 (by
    rw [Category.assoc, Category.assoc, he₁, he₂, hab])
  rw [← hx.compat n _ e₁ he₁, ← hx.compat k _ e₂ he₂, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]

set_option maxHeartbeats 4000000 in
/-- Lemma 4.4, for an abstract stable closed `ιE : E → T`. -/
theorem lemma44_aux {E : BigFppfOver B S hS} [hEa : IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    (actX : AAction (fppfO B S hS) M X) (actZ : AAction (fppfO B S hS) M Z) (i : Z ⟶ X)
    (hi : IsEquivariant actZ actX i) (hmono : ∀ U, Function.Injective (i.app U))
    (hZ : Effective actZ) (ιE : E ⟶ T) [Mono ιE]
    (actE : AAction (fppfO B S hS) M (yoneda.obj E))
    (hE : ∀ {W : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (t : W ⟶ E),
      smulAt actE h t ≫ ιE = smulAt actT h (t ≫ ιE))
    {m : Ideal Γ((SCH).obj T, ⊤)} (mE : Ideal Γ((SCH).obj E, ⊤))
    (hmE : ∀ n, mE ^ n = (m ^ n).map ((SCH).map ιE).appTop.hom)
    (hPE : letI := gradedRingOfAction actE; ChartGraded.IsCompletePair (homog actE) mE)
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (hx : IsEquivSystem actT actX m x)
    (hfac : ∀ (n : ℕ) (W : BigFppfOver B S hS) (g₁ : W ⟶ E)
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
      g₁ ≫ ιE = g₂ ≫ Chart.immι T _ → ∃ z : Z.obj (op W), i.app _ z = X.map g₂.op (x n)) :
    ∃ χ : X.obj (op E), EquivAlong actT actX ιE χ ∧
      ∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ E)
        (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
        g₁ ≫ ιE = g₂ ≫ Chart.immι T _ → X.map g₁.op χ = X.map g₂.op (x n) := by
  have hkill : ∀ n, ∀ c ∈ m ^ n, ((SCH).map (Chart.immι E (Chart.closedι ((SCH).obj E) (mE ^ n)) ≫ ιE)).appTop.hom c = 0 :=
    fun n c hc => by
      rw [Functor.map_comp]
      exact appTop_comp_eq_zero (Chart.closedι ((SCH).obj E) (mE ^ n)) ((SCH).map ιE) c
        (closedι_appTop_of_mem _ (by rw [hmE]; exact Ideal.mem_map_of_mem _ hc))
  choose s hs using fun n => exists_factor_closed _ (m ^ n) (hkill n)
  choose z hz using fun n => hfac n _ _ (s n) (hs n).symm
  have hsys : IsEquivSystem actE actZ mE z := by
    refine ⟨fun n k e he => hmono _ ?_, fun n W t t' h ht => hmono _ ?_⟩
    · rw [NatTrans.naturality_apply, hz, hz, ← Functor.map_comp_apply, ← op_comp]
      refine hx.agree _ _ ?_
      rw [Category.assoc, hs, hs, ← Category.assoc, he]
    · have h₁ : (t' ≫ s n) ≫ Chart.immι T _ = smulAt actT h ((t ≫ s n) ≫ Chart.immι T _) := by
        rw [Category.assoc, hs, ← Category.assoc, ht, hE, Category.assoc, Category.assoc, hs]
      have h₂ := hx.equiv n (t ≫ s n) (t' ≫ s n) h h₁
      rw [NatTrans.naturality_apply, hz]
      have h₃ := hi (T := op W) h (Z.map t.op (z n))
      refine Eq.trans ?_ h₃.symm
      rw [NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp]
      exact h₂
  obtain ⟨ψ, hψ, hψe⟩ := hZ E actE mE hPE z hsys
  refine ⟨i.app _ ψ, fun W t t' h ht => ?_, fun n W g₁ g₂ hg => ?_⟩
  · have e : t' = smulAt actE h t := (cancel_mono ιE).1 (by rw [ht, hE])
    subst e
    have h₁ := hψe t h
    rw [← NatTrans.naturality_apply, h₁]
    have h₃ := hi (T := op W) h (Z.map t.op ψ)
    rw [h₃, NatTrans.naturality_apply]
  · have h0 := kill_scheme ((SCH).map g₁) ((SCH).map ιE) ((SCH).map g₂)
      (Chart.closedι ((SCH).obj T) (m ^ n))
      (((SCH).map_comp g₂ _).symm.trans ((congrArg (fun z => (SCH).map z) hg.symm).trans
        ((SCH).map_comp g₁ ιE))) (m ^ n) (fun c hc => closedι_appTop_of_mem _ hc)
    obtain ⟨c, hc⟩ := exists_factor_closed g₁ (mE ^ n) (fun y hy => by
      rw [hmE] at hy
      exact h0 y hy)
    have e : X.map g₁.op (i.app _ ψ) = X.map (c ≫ s n).op (x n) := by
      rw [← hc, op_comp, Functor.map_comp_apply, ← NatTrans.naturality_apply, hψ n, hz,
        op_comp, Functor.map_comp_apply]
    refine e.trans (hx.agree _ _ ?_)
    rw [Category.assoc, hs, ← Category.assoc, hc, hg]

/-- **Lemma 4.4.** Let `i : Z → X` be an equivariant monomorphism with `Z` effective (the induction
hypothesis), `J` a stable ideal of `C` and `x` a system on `C/mⁿ` whose truncations to `V(J) ∩ V(mⁿ)`
factor through `Z`. Then there is `χ ∈ X(V(J))`, equivariant, restricting to `x`. -/
theorem lemma44 (actT : AAction (fppfO B S hS) M (yoneda.obj T))
    (actX : AAction (fppfO B S hS) M X) (actZ : AAction (fppfO B S hS) M Z) (i : Z ⟶ X)
    (hi : IsEquivariant actZ actX i) (hmono : ∀ U, Function.Injective (i.app U))
    (hZ : Effective actZ) {J m : Ideal Γ((SCH).obj T, ⊤)}
    (hJ : ∀ x ∈ J, ∀ d, (coact actT x).coeff d ∈ J)
    (hP : letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m)
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (hx : IsEquivSystem actT actX m x)
    (hfac : ∀ (n : ℕ) (W : BigFppfOver B S hS)
      (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J))
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
      g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → ∃ z : Z.obj (op W), i.app _ z = X.map g₂.op (x n)) :
    ∃ χ : X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) J))),
      EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) J)) χ ∧
      ∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄
        (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) J))
        (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
        g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → X.map g₁.op χ = X.map g₂.op (x n) := by
  have := mono_immι (T := T) J
  exact lemma44_aux actT actX actZ i hi hmono hZ _ (closedAct actT hJ)
    (fun h t => closedAct_spec actT hJ h t) _ (fun n => (Ideal.map_pow _ m n).symm)
    (isCompletePair_closedAct actT hJ hP) x hx hfac

end AlgMag.ChartMain

#print axioms AlgMag.ChartMain.lemma44
