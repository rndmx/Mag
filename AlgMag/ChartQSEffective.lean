/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSEquivUnique
import AlgMag.ChartEffectiveFinal

/-!
# Theorem 4.1, existence: the inductive step and the noetherian induction, any algebraic space

`ChartMain.effective_of_stratum`, `ChartMain.effective_of_noetherian` without separatedness: the
compatibility `hχc` is `thm41_unique_equivariant`, since all `χ k` are equivariant.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

universe u

namespace AlgMag.ChartQS

open ChartMain

set_option linter.unusedSectionVars false

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] [DecidableEq M]

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Lemma 4.3 with the setup of §4**, the form for `X` not separated: as `ChartMain.OpenStratumMap`, with
the maps `χ k` on the closed strata equivariant. They are, in the induction (Lemma 4.4); without
equivariance the compatibility on `V` has no reason to hold, as the equalizer of `τ` and `θ` is only
open and the equivariant uniqueness is what controls it. -/
def OpenStratumMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {actX : AAction (fppfO B S hS) M X}
    (tow : ClosedTower actX) : Prop :=
  ∀ (T : BigFppfOver B S hS) [IsAffine ((SCH).obj T)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (m : Ideal Γ((SCH).obj T, ⊤)),
    (letI := gradedRingOfAction actT; ChartGraded.IsCompletePair (homog actT) m) →
    ∀ x, IsEquivSystem actT actX m x →
    ∃ (a : Ideal Γ((SCH).obj T, ⊤)) (gens : Set Γ((SCH).obj T, ⊤)),
      a = Ideal.span gens ∧ (∀ g ∈ gens, ∃ d, g ∈ homog actT d) ∧
      (∀ k, ∀ y ∈ a ^ k, ∀ d, (coact actT y).coeff d ∈ a ^ k) ∧
      (∀ (k n : ℕ) (W : BigFppfOver B S hS)
        (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
        (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
        g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ →
        ∃ z : (tow.Z k).obj (op W), (tow.i k).app _ z = X.map g₂.op (x n)) ∧
      ∃ (UT : BigFppfOver B S hS) (j : UT ⟶ T) (τ : X.obj (op UT)),
        IsOpenImmersion ((SCH).map j) ∧
        (∀ y : (SCH).obj T, y ∈ Set.range ((SCH).map j) ↔ ∃ g ∈ a, y ∈ ((SCH).obj T).basicOpen g) ∧
        EquivAlong actT actX j τ ∧
        (∀ (n : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UT)
          (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
          g₁ ≫ j = g₂ ≫ Chart.immι T _ → X.map g₁.op τ = X.map g₂.op (x n)) ∧
        ∀ (Y : BigFppfOver B S hS) [IsAffine ((SCH).obj Y)] [IsNoetherianRing Γ((SCH).obj Y, ⊤)]
          (p : Y ⟶ T), Flat ((SCH).map p) →
          (∀ (k : ℕ) (r : Γ((SCH).obj Y, ⊤)), ∃ c : Γ((SCH).obj T, ⊤),
            r - ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom) →
          (∀ (k : ℕ) (c : Γ((SCH).obj T, ⊤)),
            ((SCH).map p).appTop.hom c ∈ (a ^ k).map ((SCH).map p).appTop.hom → c ∈ a ^ k) →
          IsAdicComplete (a.map ((SCH).map p).appTop.hom) Γ((SCH).obj Y, ⊤) →
          ∀ (χ : ∀ k, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))))),
          (∀ k, EquivAlong actT actX (Chart.immι T (Chart.closedι ((SCH).obj T) (a ^ k))) (χ k)) →
          (∀ (k n : ℕ) ⦃W : BigFppfOver B S hS⦄
            (g₁ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k)))
            (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n))),
            g₁ ≫ Chart.immι T _ = g₂ ≫ Chart.immι T _ → X.map g₁.op (χ k) = X.map g₂.op (x n)) →
          ∀ θ : X.obj (op Y),
          (∀ (k : ℕ) (W : BigFppfOver B S hS) (i : W ⟶ Y)
            (s : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
            s ≫ Chart.immι T _ = i ≫ p → X.map i.op θ = X.map s.op (χ k)) →
          ∀ ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ UT) (g₂ : W ⟶ Y), g₁ ≫ j = g₂ ≫ p →
            X.map g₁.op τ = X.map g₂.op θ

set_option maxHeartbeats 4000000 in
/-- `hχc`, on an abstract stable closed `ιE : E → T`: an equivariant point pulled back from `E'` and an
equivariant point of `E`, both restricting to the system `x`, agree. -/
lemma chi_compat_aux {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T E E' : BigFppfOver B S hS}
    [IsAffine ((SCH).obj T)] [IsAffine ((SCH).obj E)]
    (actT : AAction (fppfO B S hS) M (yoneda.obj T)) (actX : AAction (fppfO B S hS) M X)
    (hX : IsAlgebraicSpace B S hS X)
    (ιE : E ⟶ T) (actE : AAction (fppfO B S hS) M (yoneda.obj E))
    (hE : ∀ {W : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj W, ⊤)) (s : W ⟶ E),
      smulAt actE h s ≫ ιE = smulAt actT h (s ≫ ιE))
    {m : Ideal Γ((SCH).obj T, ⊤)} (mE : Ideal Γ((SCH).obj E, ⊤))
    (hmE : ∀ n, mE ^ n = (m ^ n).map ((SCH).map ιE).appTop.hom)
    (hPE : letI := gradedRingOfAction actE; ChartGraded.IsCompletePair (homog actE) mE)
    (x : ∀ n, X.obj (op (Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ n)))))
    (ψ : X.obj (op E)) (hψe : EquivAlong actT actX ιE ψ)
    (hψ : ∀ (r : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ E)
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ r))),
      g₁ ≫ ιE = g₂ ≫ Chart.immι T _ → X.map g₁.op ψ = X.map g₂.op (x r))
    (χ' : X.obj (op E')) (ι' : E' ⟶ T) (e : E ⟶ E') (he : e ≫ ι' = ιE)
    (hχe : EquivAlong actT actX ι' χ')
    (hχ' : ∀ (r : ℕ) ⦃W : BigFppfOver B S hS⦄ (g₁ : W ⟶ E')
      (g₂ : W ⟶ Chart.immObj T (Chart.closedι ((SCH).obj T) (m ^ r))),
      g₁ ≫ ι' = g₂ ≫ Chart.immι T _ → X.map g₁.op χ' = X.map g₂.op (x r)) :
    X.map e.op χ' = ψ := by
  refine thm41_unique_equivariant actE actX hX mE hPE _ _
    (fun {W} t h => ?_) (fun {W} t h => hψe t (smulAt actE h t) h (hE h t)) fun r => ?_
  · rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    refine hχe (t ≫ e) (smulAt actE h t ≫ e) h ?_
    rw [Category.assoc, he, Category.assoc, he]
    exact hE h t
  · have hkill : ∀ c ∈ m ^ r, ((SCH).map (Chart.immι E (Chart.closedι ((SCH).obj E) (mE ^ r)) ≫ ιE)).appTop.hom c = 0 :=
      fun c hc => by
        rw [Functor.map_comp]
        exact appTop_comp_eq_zero (Chart.closedι ((SCH).obj E) (mE ^ r)) ((SCH).map ιE) c
          (closedι_appTop_of_mem _ (by rw [hmE]; exact Ideal.mem_map_of_mem _ hc))
    obtain ⟨s, hs⟩ := exists_factor_closed _ (m ^ r) hkill
    have h1 := hψ r _ s hs.symm
    have h2 := hχ' r (Chart.immι E (Chart.closedι ((SCH).obj E) (mE ^ r)) ≫ e) s (by
      rw [Category.assoc, he, hs])
    rw [← Functor.map_comp_apply, ← op_comp]
    exact h2.trans h1.symm

set_option maxHeartbeats 4000000 in
/-- **Theorem 4.1, existence: the inductive step**, `X` any algebraic space. -/
theorem effective_of_stratum {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {actX : AAction (fppfO B S hS) M X} (hX : IsAlgebraicSpace B S hS X)
    (hB : NoetherianAlgebraization X)
    (tow : ClosedTower actX) (hL : OpenStratumMap tow) (hZ : ∀ k, Effective (tow.actZ k)) :
    Effective actX := by
  intro T _ actT m hP x hx
  obtain ⟨a, gens, hgens, hhom, hI, hfac, UT, j, τ, hj, hjr, hτ, hτx, hθ⟩ := hL T actT m hP x hx
  letI := gradedRingOfAction actT
  haveI : IsNoetherianRing Γ((SCH).obj T, ⊤) := hP.noeth
  choose χ hχ hχx using fun k => lemma44 actT actX (tow.actZ k) (tow.i k) (tow.equiv k)
    (tow.mono k) (hZ k) (hI k) hP x hx (hfac k)
  have hχc : ∀ (n k : ℕ) (e : Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ n)) ⟶
      Chart.immObj T (Chart.closedι ((SCH).obj T) (a ^ k))),
      e ≫ Chart.immι T _ = Chart.immι T _ → X.map e.op (χ k) = χ n := by
    intro n k e he
    exact chi_compat_aux actT actX hX _ (closedAct actT (hI n))
      (fun {W} h s => closedAct_spec actT (hI n) h s) _ (fun r => (Ideal.map_pow _ m r).symm)
      (isCompletePair_closedAct actT (hI n) hP) x (χ n) (hχ n) (hχx n) (χ k) _ e he (hχ k) (hχx k)
  have hsu := compl_hsurj T a
  have hin := compl_hinj T a
  exact thm41_exists_of_strata actT actX hX hB a gens hgens hhom hI j (complMap T a) hj hjr
    (compl_flat T a)
    (fun y hy => compl_hcov T a y fun g hg hyg => hy ((hjr y).2 ⟨g, hg, hyg⟩))
    hsu hin τ hτ χ hχ hχc
    (fun θ hθk _ g₁ g₂ hg => hθ _ _ (compl_flat T a) hsu hin inferInstance χ hχ
      (fun k n _ g₁ g₂ h => hχx k n g₁ g₂ h) θ hθk g₁ g₂ hg)
    m x hτx (fun n k _ g₁ g₂ h => hχx k n g₁ g₂ h)

/-- `ChartMain.StrataOver` with `OpenStratumMap` of this file. -/
def StrataOver {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act₀ : AAction (fppfO B S hS) M X₀} (C : ClosedStable act₀) : Prop :=
  ∀ (U : BigFppfOver B S hS) (actU : AAction (fppfO B S hS) M (yoneda.obj U))
    (f : yoneda.obj U ⟶ C.Z), IsAffine ((SCH).obj U) → Nonempty ((SCH).obj U) →
    IsEquivariant actU C.actZ f →
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) f →
    ∃ tow : ClosedTower C.actZ,
      (∀ k, Space.IsClosedImmersion B S hS (tow.i k)) ∧
      (∀ k, IsAlgebraicSpace B S hS (tow.Z k)) ∧
      (∀ k, Disjoint (Set.range (pointsMap B S hS _ (tow.i k)))
        (Set.range (pointsMap B S hS _ f))) ∧
      OpenStratumMap tow

section Induction

attribute [local instance] Space.pointTopology

variable {X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Theorem 4.1, existence: the noetherian induction**, any algebraic space. -/
theorem effective_of_noetherian {act₀ : AAction (fppfO B S hS) M X₀}
    (hX₀ : IsAlgebraicSpace B S hS X₀)
    [TopologicalSpace.NoetherianSpace (points B S hS X₀)]
    (hC : ∀ C : ClosedStable act₀, NoetherianAlgebraization C.Z)
    (h42 : ∀ C : ClosedStable act₀, AffineStratum C.Z C.actZ)
    (h43 : ∀ C : ClosedStable act₀, StrataOver C)
    (C : ClosedStable act₀) : Effective C.actZ := by
  suffices h : ∀ (K : TopologicalSpace.Closeds (points B S hS X₀)) (C : ClosedStable act₀),
      C.pts hX₀ = K → Effective C.actZ from h _ C rfl
  intro K
  induction K using WellFoundedLT.induction with
  | ind K IH =>
    intro C hCK
    by_cases hne : ∃ W : BigFppfOver B S hS, Nonempty ((SCH).obj W) ∧ Nonempty (C.Z.obj (op W))
    · obtain ⟨U, actU, f, hUa, hUn, hfe, hfo⟩ := h42 C hne
      obtain ⟨tow, hcl, halg, hdis, hL⟩ := h43 C U actU f hUa hUn hfe hfo
      refine effective_of_stratum C.alg (hC C) tow hL fun k => ?_
      let C' : ClosedStable act₀ :=
        { Z := tow.Z k
          actZ := tow.actZ k
          i := tow.i k ≫ C.i
          equiv := fun h x => (C.equiv h _).symm ▸ congrArg (C.i.app _) (tow.equiv k h x)
          mono := fun V => (C.mono V).comp (tow.mono k V)
          closed := MorphismProperty.comp_mem _ _ _ (hcl k) C.closed
          alg := halg k }
      refine IH (C'.pts hX₀) ?_ C' rfl
      have hle : C'.pts hX₀ ≤ K := by
        rw [← hCK]
        rintro _ ⟨q, rfl⟩
        refine ⟨pointsMap B S hS _ (tow.i k) q, ?_⟩
        change _ = pointsMap B S hS _ (tow.i k ≫ C.i) q
        rw [pointsMap_comp]
        rfl
      refine lt_of_le_of_ne hle fun heq => ?_
      obtain ⟨u⟩ := hUn
      obtain ⟨p, -⟩ := (pointsEquivScheme B S hS U).surjective u
      have hmemK : pointsMap B S hS _ C.i (pointsMap B S hS _ f p) ∈ (K : Set _) := by
        rw [← hCK]
        exact ⟨_, rfl⟩
      rw [← heq] at hmemK
      obtain ⟨q, hq⟩ := hmemK
      haveI : Mono C.i := (NatTrans.mono_iff_mono_app _).2 fun V =>
        (mono_iff_injective _).2 (C.mono V)
      have hq' : pointsMap B S hS _ (tow.i k ≫ C.i) q = _ := hq
      rw [pointsMap_comp] at hq'
      have hinj := pointsMap_injective_of_mono B S hS C.i hq'
      exact Set.disjoint_left.1 (hdis k) ⟨q, hinj⟩ ⟨p, rfl⟩
    · exact effective_of_isEmpty C.actZ hne

end Induction

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.effective_of_stratum
#print axioms AlgMag.ChartQS.effective_of_noetherian
