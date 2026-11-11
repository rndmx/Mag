/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSChart

/-!
# Equalizer killing, for any algebraic space

Generalizes `Chart.eq_of_agree_basicOpen_of_agree_thickening`, which assumes `X` separated.
Step 1 of the chart-lemma proof without separatedness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A map landing in `D(r)` factors through it. -/
lemma exists_factor_basicOpen {W Z : BigFppfOver B S hS} (r : Γ((SCH).obj W, ⊤)) (t : Z ⟶ W)
    (ht : ∀ z, (SCH).map t z ∈ ((SCH).obj W).basicOpen r) :
    ∃ l : Z ⟶ Chart.immObj W ((SCH).obj W |>.basicOpen r).ι, l ≫ Chart.immι W _ = t := by
  haveI : IsOpenImmersion ((SCH).map (Chart.immι W ((SCH).obj W |>.basicOpen r).ι)) :=
    inferInstanceAs (IsOpenImmersion (((SCH).obj W).basicOpen r).ι)
  exact exists_factor_open _ t (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨_, ht z⟩, rfl⟩)

set_option maxHeartbeats 1000000 in
/-- **Equalizer killing, principal ideal, any algebraic space.** `W` affine, `Γ(W)` flat over a
noetherian `C`, `g ∈ C`. Two points of `X` over `W` agreeing on `D(g)` and on all `V(g^k)` are equal. -/
theorem eq_of_agree_principal (hX : IsAlgebraicSpace B S hS X) (W : BigFppfOver B S hS)
    [IsAffine ((SCH).obj W)] {C : Type*} [CommRing C] [IsNoetherianRing C]
    [Algebra C Γ((SCH).obj W, ⊤)] [Module.Flat C Γ((SCH).obj W, ⊤)] (g : C) (p q : X.obj (op W))
    (hD : X.map (Chart.immι W (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op p =
      X.map (Chart.immι W (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op q)
    (hV : ∀ k : ℕ, X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        (((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        (((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op q) : p = q := by
  let γ := algebraMap C Γ((SCH).obj W, ⊤) g
  let J : Ideal Γ((SCH).obj W, ⊤) := (Ideal.span {g}).map (algebraMap C _)
  let p' : yoneda.obj W ⟶ X := yonedaEquiv.symm p
  let q' : yoneda.obj W ⟶ X := yonedaEquiv.symm q
  have hmap : ∀ {Z : BigFppfOver B S hS} (i : Z ⟶ W), X.map i.op p = X.map i.op q →
      yoneda.map i ≫ p' = yoneda.map i ≫ q' := by
    intro Z i h
    apply yonedaEquiv.injective
    simpa [p', q', yonedaEquiv_apply] using h
  have hunmap : ∀ {Z : BigFppfOver B S hS} (i : Z ⟶ W), yoneda.map i ≫ p' = yoneda.map i ≫ q' →
      X.map i.op p = X.map i.op q := by
    intro Z i h
    have := congrArg yonedaEquiv h
    simpa [p', q', yonedaEquiv_apply] using this
  have hJ : ∀ k, (J ^ k) = ((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj W, ⊤)) := fun k => by
    rw [Ideal.map_pow]
  have hVk : ∀ k : ℕ, yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (J ^ k))) ≫ p' =
      yoneda.map (Chart.immι W (Chart.closedι ((SCH).obj W) (J ^ k))) ≫ q' := by
    intro k
    rw [hJ]
    exact hmap _ (hV k)
  have hch : ∀ y : (SCH).obj W, y ∉ ((SCH).obj W).basicOpen γ →
      ∃ (P : BigFppfOver B S hS) (e : P ⟶ W), Etale ((SCH).map e) ∧ y ∈ Set.range ((SCH).map e) ∧
        X.map e.op p = X.map e.op q := by
    intro y hy
    have hyJ : ∀ r ∈ J, y ∉ ((SCH).obj W).basicOpen r := by
      intro r hr hb
      have hle : J ≤ (((SCH).obj W).isoSpec.hom y).asIdeal := by
        refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
        rintro _ rfl
        by_contra hc
        exact hy ((mem_basicOpen_iff y γ).2 hc)
      exact (mem_basicOpen_iff y r).1 hb (hle hr)
    obtain ⟨P, V, hPa, e, v, hv, s, t, hVa, heE, hyr, hs, ht, hst⟩ :=
      exists_chart_agree hX J p' q' hVk y hyJ
    refine ⟨P, e, heE, hyr, ?_⟩
    letI algP : Algebra C Γ((SCH).obj P, ⊤) :=
      (((SCH).map e).appTop.hom.comp (algebraMap C Γ((SCH).obj W, ⊤))).toAlgebra
    have halg : ∀ c, algebraMap C Γ((SCH).obj P, ⊤) c =
        ((SCH).map e).appTop.hom (algebraMap C Γ((SCH).obj W, ⊤) c) := fun _ => rfl
    have heF : ((SCH).map e).appTop.hom.Flat :=
      (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
    letI algWP : Algebra Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := ((SCH).map e).appTop.hom.toAlgebra
    haveI : Module.Flat Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := heF
    haveI : IsScalarTower C Γ((SCH).obj W, ⊤) Γ((SCH).obj P, ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI hflat : Module.Flat C Γ((SCH).obj P, ⊤) := Module.Flat.trans C Γ((SCH).obj W, ⊤) _
    have hsE : v.app (op P) s = X.map e.op p := by
      have := congrArg (fun φ => φ.app (op P) (𝟙 P)) hs
      simpa [p', yonedaEquiv_symm_app_apply] using this
    have htE : v.app (op P) t = X.map e.op q := by
      have := congrArg (fun φ => φ.app (op P) (𝟙 P)) ht
      simpa [q', yonedaEquiv_symm_app_apply] using this
    rw [← hsE, ← htE]
    refine eq_of_lift_etale hX v hv s t g ?_ ?_
    · rw [hsE, htE, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
      obtain ⟨l, hl⟩ := exists_factor_basicOpen γ
        (Chart.immι P (((SCH).obj P).basicOpen (algebraMap C Γ((SCH).obj P, ⊤) g)).ι ≫ e) (by
          intro z
          have hz := ((((SCH).obj P).basicOpen (((SCH).map e).appTop.hom γ)).ι z)
          have hm : ((SCH).map (Chart.immι P (((SCH).obj P).basicOpen (algebraMap C Γ((SCH).obj P, ⊤) g)).ι) z :
              (SCH).obj P) ∈ ((SCH).map e) ⁻¹ᵁ ((SCH).obj W).basicOpen γ := by
            rw [Scheme.preimage_basicOpen]
            exact z.2
          rw [Functor.map_comp, Scheme.Hom.comp_apply]
          exact hm)
      rw [← hl, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hD]
    · intro k
      have h := hst k
      have : ((J ^ k).map ((SCH).map e).appTop.hom) =
          ((Ideal.span {g}) ^ k).map (algebraMap C Γ((SCH).obj P, ⊤)) := by
        rw [hJ, Ideal.map_map]
        rfl
      rw [this] at h
      exact h
  let Y₀ : Type u := {y : (SCH).obj W // y ∉ ((SCH).obj W).basicOpen γ}
  have hch' : ∀ y : Y₀, ∃ (P : BigFppfOver B S hS) (e : P ⟶ W), Etale ((SCH).map e) ∧
      y.1 ∈ Set.range ((SCH).map e) ∧ X.map e.op p = X.map e.op q := fun y => hch y.1 y.2
  choose Pf ef hEt hrg heq using hch'
  let Z : Option Y₀ → BigFppfOver B S hS := fun i => match i with
    | none => Chart.immObj W (((SCH).obj W).basicOpen γ).ι
    | some y => Pf y
  let e : ∀ i, Z i ⟶ W := fun i => match i with
    | none => Chart.immι W (((SCH).obj W).basicOpen γ).ι
    | some y => ef y
  refine eq_of_family hX Z e ?_ ?_ ?_ p q ?_
  · rintro (_ | y)
    · exact inferInstanceAs (Flat (((SCH).obj W).basicOpen γ).ι)
    · have := hEt y
      exact inferInstanceAs (Flat ((SCH).map (ef y)))
  · rintro (_ | y)
    · exact (((SCH).obj W).basicOpen γ).ι.isOpenEmbedding.isOpenMap
    · have := hEt y
      exact ((SCH).map (ef y)).isOpenMap
  · intro y
    by_cases hy : y ∈ ((SCH).obj W).basicOpen γ
    · exact ⟨none, ⟨⟨y, hy⟩, rfl⟩⟩
    · exact ⟨some ⟨y, hy⟩, hrg ⟨y, hy⟩⟩
  · rintro (_ | y)
    · exact hD
    · exact heq y

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.eq_of_agree_principal
