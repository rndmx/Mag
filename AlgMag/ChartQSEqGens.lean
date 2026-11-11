/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSEq
import AlgMag.ChartQSFlatQuot

/-!
# Equalizer killing for several generators, any algebraic space

`AlgMag.ChartQS.eq_of_agree_basicOpen_of_agree_thickening`: same statement as
`AlgMag.Chart.eq_of_agree_basicOpen_of_agree_thickening`, with `X` any algebraic space. Induction on the
number of generators, by passing to `C/(g^k)`. This replaces the iterated completion of
Step 2 of the chart-lemma proof without separatedness, for uniqueness.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace AlgMag.ChartQS

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

lemma eq_of_closed_bot (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)]
    (I : Ideal Γ((SCH).obj W, ⊤)) (hI : I = ⊥) (p q : X.obj (op W))
    (h : X.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W) I)).op q) : p = q := by
  let i := Chart.immι W (Chart.closedι ((SCH).obj W) I)
  have hinj : ∀ r, ((SCH).map i).appTop r = 0 → r = 0 := fun r hr => by
    have := Chart.closedι_appTop_eq_zero I r hr
    rw [hI] at this
    simpa using this
  haveI hcl : IsClosedImmersion ((SCH).map i) :=
    inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj W) I))
  haveI hE : IsAffine ((SCH).obj (Chart.immObj W (Chart.closedι ((SCH).obj W) I))) := by
    change IsAffine (Spec _)
    infer_instance
  haveI hiso : IsIso ((SCH).map i) := by
    apply IsClosedImmersion.isIso_of_injective_of_isAffine
    exact (injective_iff_map_eq_zero _).mpr hinj
  let u : W ⟶ Chart.immObj W (Chart.closedι ((SCH).obj W) I) := siteHom (inv ((SCH).map i)) (by
    rw [IsIso.inv_comp_eq]
    exact (site_w i).symm)
  have hu : u ≫ i = 𝟙 W := site_hom_ext (by
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact IsIso.inv_hom_id _)
  have := congrArg (X.map u.op) h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hu] at this
  simpa using this

lemma ring_kill {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E] [Algebra C R]
    (π : R →+* A) (ρ : A →+* E) (g : C) (b : Ideal C) (k m : ℕ)
    (h1 : ∀ u ∈ (Ideal.span {g}) ^ k, π (algebraMap C R u) = 0)
    (h2 : ∀ w ∈ b ^ m, ρ (π (algebraMap C R w)) = 0) :
    ∀ x ∈ (Ideal.span {g} ⊔ b) ^ (k + m), (ρ.comp π) (algebraMap C R x) = 0 := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (Ideal.sup_pow_add_le_pow_sup_pow hx)
  simp only [RingHom.comp_apply, map_add, h1 u hu, map_zero, h2 w hw, add_zero]

set_option maxHeartbeats 4000000 in
/-- Generators in a list. -/
theorem eq_of_agree_list (hX : IsAlgebraicSpace B S hS X) (n : ℕ) :
    ∀ {C : Type v} [CommRing C] [IsNoetherianRing C] (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)]
    [Algebra C Γ((SCH).obj W, ⊤)] [Module.Flat C Γ((SCH).obj W, ⊤)] (l : List C), l.length = n →
    ∀ (p q : X.obj (op W)),
    (∀ g ∈ l, X.map (Chart.immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op p =
      X.map (Chart.immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op q) →
    (∀ k : ℕ, X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        (((Ideal.span {x | x ∈ l}) ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        (((Ideal.span {x | x ∈ l}) ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op q) → p = q := by
  induction n with
  | zero =>
    intro C _ _ W _ _ _ l hl p q _ hV
    obtain rfl := List.length_eq_zero_iff.1 hl
    refine eq_of_closed_bot W _ ?_ p q (hV 1)
    simp
  | succ n ih =>
    intro C _ _ W _ _ _ l hl p q hD hV
    obtain ⟨g, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    have hl' : l'.length = n := by simpa using hl
    refine eq_of_agree_principal hX W g p q (hD g (by simp)) fun k => ?_
    let b : Ideal C := Ideal.span {x | x ∈ l'}
    have hab : Ideal.span {x | x ∈ g :: l'} = Ideal.span {g} ⊔ b := by
      rw [← Ideal.span_union]
      congr 1
      ext x
      simp
    let Ik : Ideal C := (Ideal.span {g}) ^ k
    let I' := Ik.map (algebraMap C Γ((SCH).obj W, ⊤))
    let ik := Chart.immι W (Chart.closedι ((SCH).obj W) I')
    let Wk := Chart.immObj W (Chart.closedι ((SCH).obj W) I')
    haveI hWk : IsAffine ((SCH).obj Wk) := by
      change IsAffine (Spec _)
      infer_instance
    let π : Γ((SCH).obj W, ⊤) →+* Γ((SCH).obj Wk, ⊤) := ((SCH).map ik).appTop.hom
    haveI hcl : IsClosedImmersion ((SCH).map ik) :=
      inferInstanceAs (IsClosedImmersion (Chart.closedι ((SCH).obj W) I'))
    have hs : Function.Surjective π :=
      (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map ik)).2
    have hker : RingHom.ker π = Ik.map (algebraMap C Γ((SCH).obj W, ⊤)) := by
      ext r
      exact ⟨fun h => Chart.closedι_appTop_eq_zero I' r h,
        fun h => ChartMain.closedι_appTop_of_mem I' h⟩
    letI algk : Algebra (C ⧸ Ik) Γ((SCH).obj Wk, ⊤) := (quotHom Ik π hker).toAlgebra
    haveI hfk : Module.Flat (C ⧸ Ik) Γ((SCH).obj Wk, ⊤) := flat_quot Ik π hs hker
    have halg : ∀ c : C, algebraMap (C ⧸ Ik) Γ((SCH).obj Wk, ⊤) (Ideal.Quotient.mk Ik c) =
        π (algebraMap C _ c) := fun _ => rfl
    refine ih (C := C ⧸ Ik) Wk (l'.map (Ideal.Quotient.mk Ik)) (by simpa using hl') _ _ ?_ ?_
    · intro h hh
      obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.1 hh
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
      obtain ⟨c, hc⟩ := exists_factor_basicOpen (algebraMap C Γ((SCH).obj W, ⊤) h₀)
        (Chart.immι Wk (((SCH).obj Wk).basicOpen (algebraMap (C ⧸ Ik) Γ((SCH).obj Wk, ⊤)
          (Ideal.Quotient.mk Ik h₀))).ι ≫ ik) (by
          intro z
          have hm : ((SCH).map (Chart.immι Wk (((SCH).obj Wk).basicOpen (algebraMap (C ⧸ Ik) Γ((SCH).obj Wk, ⊤)
              (Ideal.Quotient.mk Ik h₀))).ι) z : (SCH).obj Wk) ∈
              ((SCH).map ik) ⁻¹ᵁ ((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) h₀) := by
            rw [Scheme.preimage_basicOpen]
            exact z.2
          rw [Functor.map_comp, Scheme.Hom.comp_apply]
          exact hm)
      rw [← hc, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hD h₀ (List.mem_cons_of_mem _ hh₀)]
    · intro m
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
      let bb : Ideal (C ⧸ Ik) := Ideal.span {x | x ∈ l'.map (Ideal.Quotient.mk Ik)}
      have hbb : bb = b.map (Ideal.Quotient.mk Ik) := by
        simp only [bb, b, Ideal.map_span]
        congr 1
        ext x
        simp
      let jm := Chart.immι Wk (Chart.closedι ((SCH).obj Wk)
        ((bb ^ m).map (algebraMap (C ⧸ Ik) Γ((SCH).obj Wk, ⊤))))
      have hkill : ∀ x ∈ ((Ideal.span {x | x ∈ g :: l'}) ^ (k + m)).map (algebraMap C Γ((SCH).obj W, ⊤)),
          ((SCH).map (jm ≫ ik)).appTop.hom x = 0 := by
        let ρ : Γ((SCH).obj Wk, ⊤) →+* _ := ((SCH).map jm).appTop.hom
        have h1 : ∀ u ∈ Ik, π (algebraMap C Γ((SCH).obj W, ⊤) u) = 0 := fun u hu => by
          have : algebraMap C Γ((SCH).obj W, ⊤) u ∈ RingHom.ker π :=
            hker ▸ Ideal.mem_map_of_mem _ hu
          exact this
        have h2 : ∀ w ∈ b ^ m, ρ (π (algebraMap C Γ((SCH).obj W, ⊤) w)) = 0 := fun w hw => by
          refine ChartMain.closedι_appTop_of_mem _ ?_
          rw [← halg]
          refine Ideal.mem_map_of_mem _ ?_
          rw [hbb, ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ hw
        have h3 := ring_kill π ρ g b k m h1 h2
        rw [hab]
        have h4 := kill_of_map (algebraMap C Γ((SCH).obj W, ⊤)) (ρ.comp π) _ h3
        intro x hx
        have h5 := h4 x hx
        rw [Functor.map_comp, Scheme.Hom.comp_appTop]
        exact h5
      obtain ⟨c, hc⟩ := ChartMain.exists_factor_closed (jm ≫ ik) _ hkill
      rw [← hc, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hV (k + m)]

/-- **Equalizer killing (§4, after Lemma 4.5), for any algebraic space.** Same statement as
`Chart.eq_of_agree_basicOpen_of_agree_thickening`, without separatedness. -/
theorem eq_of_agree_basicOpen_of_agree_thickening (hX : IsAlgebraicSpace B S hS X)
    (W : BigFppfOver B S hS) [IsAffine ((SCH).obj W)]
    {C : Type v} [CommRing C] [IsNoetherianRing C] [Algebra C Γ((SCH).obj W, ⊤)]
    [Module.Flat C Γ((SCH).obj W, ⊤)] (a : Ideal C) (gens : Set C) (hgens : a = Ideal.span gens)
    (p q : X.obj (op W))
    (hD : ∀ g ∈ gens, X.map (Chart.immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op p =
      X.map (Chart.immι W
        (((SCH).obj W).basicOpen (algebraMap C Γ((SCH).obj W, ⊤) g)).ι).op q)
    (hV : ∀ k : ℕ, X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        ((a ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op p =
      X.map (Chart.immι W (Chart.closedι ((SCH).obj W)
        ((a ^ k).map (algebraMap C Γ((SCH).obj W, ⊤))))).op q) : p = q := by
  have hfg : (Ideal.span gens).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := Submodule.fg_span_iff_fg_span_finset_subset gens |>.1 hfg
  refine eq_of_agree_list hX _ W t.toList rfl p q (fun g hg => hD g (ht (by simpa using hg))) fun k => ?_
  have e : Ideal.span {x | x ∈ t.toList} = a := by
    rw [hgens]
    change _ = Submodule.span C gens
    rw [hspan]
    change Submodule.span C _ = _
    congr 1
    ext x
    simp
  rw [e]
  exact hV k

end AlgMag.ChartQS

#print axioms AlgMag.ChartQS.eq_of_agree_basicOpen_of_agree_thickening
