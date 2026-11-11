/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDTorus
import AlgMag.SDLocSFactor

/-!
# Lemma D, Step 1: an invariant point is constant on the closed orbit

For Props. 3.31 (ii), 3.32 (ii) of `Algebraic Magnetism`, Step 1. A point
`c₁ : P → 𝒪(V)` of `𝔸(P)`, supported in degrees of a subgroup `L` of `Γ`, spreads to the orbit point
`c₀(p) = c₁(p) [δ p]` over `𝔸(L)_V`. For an invariant `x` on `𝔸(P)_T`, the pullback of `x` along `c₀` is the constant
one: pull back along the fppf cover `D(Γ)_V → D(L)_V`, where `c₀` is `g ∘ δ * c₁`. The group algebra of `L` appears as
`PUnit ×_{Γ/L} Γ`, for which `AlgMag.SDTorus.ext_Pt` is the separatedness along the cover.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

section Orbit

variable {Γ : Type u} [AddCommGroup Γ] (L : AddSubgroup Γ)

/-- The map `PUnit → Γ/L`. -/
abbrev SDR3Orbit_δL : PUnit.{u + 1} →+ Γ ⧸ L := 0

/-- The monoid of `L`, as `PUnit ×_{Γ/L} Γ`. -/
abbrev SDR3Orbit_OM : AddSubmonoid (PUnit.{u + 1} × Γ) := Pt (SDR3Orbit_δL L) (QuotientAddGroup.mk' L)

/-- An element of `L` in `SDR3Orbit_OM`. -/
def SDR3Orbit_om {d : Γ} (hd : d ∈ L) : SDR3Orbit_OM L :=
  ⟨(PUnit.unit, d), mem_Pt.2 ((QuotientAddGroup.eq_zero_iff d).2 hd).symm⟩

variable [Countable Γ] [AddGroup.FG Γ]

variable {P : Type u} [AddCommMonoid P] [Countable P] (δ : P →+ Γ)
  {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (c₁ : APt (fppfO B S hS) P (op V))

/-- The orbit point `c₀(p) = c₁(p) [δ p]`, over `𝔸(L)_V`, for `c₁` supported in the degrees of `L`. -/
noncomputable def SDR3Orbit_c₀ (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c₁ p = 0) :
    APt (fppfO B S hS) P (op (specObj (SDR3Orbit_OM L) V)) := by
  classical
  let res₁ := APt.res (specPr (SDR3Orbit_OM L) V).op c₁
  let pt := specPt (SDR3Orbit_OM L) V
  have hres : ∀ p : Multiplicative P, δ p.toAdd ∉ L → res₁ p = 0 := fun p hp => by
    simp only [res₁, APt.res_apply, hL p hp, map_zero]
  exact
    { toFun := fun p => if h : δ p.toAdd ∈ L then res₁ p * pt (Multiplicative.ofAdd (SDR3Orbit_om L h)) else 0
      map_one' := by
        have h0 : δ (1 : Multiplicative P).toAdd ∈ L := by
          change δ 0 ∈ L
          rw [map_zero]
          exact L.zero_mem
        rw [dif_pos h0, map_one, one_mul]
        have : Multiplicative.ofAdd (SDR3Orbit_om L h0) = 1 := by
          apply Multiplicative.toAdd.injective
          apply Subtype.ext
          refine Prod.ext rfl ?_
          change δ 0 = 0
          rw [map_zero]
        rw [this, map_one]
      map_mul' := fun p p' => by
        by_cases h : δ p.toAdd ∈ L
        · by_cases h' : δ p'.toAdd ∈ L
          · have hpp : δ (p * p').toAdd ∈ L := by
              change δ (p.toAdd + p'.toAdd) ∈ L
              rw [map_add]
              exact L.add_mem h h'
            rw [dif_pos hpp, dif_pos h, dif_pos h', map_mul]
            have : Multiplicative.ofAdd (SDR3Orbit_om L hpp) =
                Multiplicative.ofAdd (SDR3Orbit_om L h) * Multiplicative.ofAdd (SDR3Orbit_om L h') := by
              apply Multiplicative.toAdd.injective
              apply Subtype.ext
              refine Prod.ext rfl ?_
              change δ (p.toAdd + p'.toAdd) = _
              rw [map_add]
              rfl
            rw [this, map_mul]
            ring
          · rw [dif_neg h', mul_zero]
            split_ifs with hpp
            · rw [map_mul, hres p' h', mul_zero, zero_mul]
            · rfl
        · rw [dif_neg h, zero_mul]
          split_ifs with hpp
          · rw [map_mul, hres p h, zero_mul, zero_mul]
          · rfl }

lemma SDR3Orbit_c₀_pos (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c₁ p = 0) (p : Multiplicative P)
    (h : δ p.toAdd ∈ L) : SDR3Orbit_c₀ L δ c₁ hL p =
      APt.res (specPr (SDR3Orbit_OM L) V).op c₁ p * specPt (SDR3Orbit_OM L) V (Multiplicative.ofAdd (SDR3Orbit_om L h)) := by
  classical
  exact dif_pos h

lemma SDR3Orbit_c₀_neg (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c₁ p = 0) (p : Multiplicative P)
    (h : δ p.toAdd ∉ L) : SDR3Orbit_c₀ L δ c₁ hL p = 0 := by
  classical
  exact dif_neg h

/-- The composite of a classifying morphism with a morphism of the base. -/
lemma SDR3Orbit_comp_specLift {P' : Type u} [AddCommMonoid P'] [Countable P'] {V' T' T'' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (a : T'' ⟶ T') (t : T' ⟶ V')
    (c : APt (fppfO B S hS) P' (op T')) :
    a ≫ specLift t c = specLift (a ≫ t) (APt.res a.op c) := by
  refine specLift_uniq _ _ _ (by rw [Category.assoc, specLift_pr]) ?_
  rw [op_comp, APt.res_comp, res_specLift]

/-- **Step 1, constancy.** For `x` invariant on `𝔸(P)_T`, the pullback of `x` along the orbit point `c₀` over `𝔸(L)_V` is
the pullback of `c₁^* x` from `V`. -/
theorem SDR3Orbit_const {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (x : X.obj (op (specObj P T)))
    (hx : IsInvPt X δ x) (t : V ⟶ T) (hL : ∀ p : Multiplicative P, δ p.toAdd ∉ L → c₁ p = 0) :
    X.map (specLift (specPr (SDR3Orbit_OM L) V ≫ t) (SDR3Orbit_c₀ L δ c₁ hL)).op x =
      X.map (specPr (SDR3Orbit_OM L) V).op (X.map (specLift t c₁).op x) := by
  have hq : Function.Surjective (QuotientAddGroup.mk' L) := QuotientAddGroup.mk'_surjective L
  let a := specAlong V (SDR3Orbit_OM L).subtype
  let prW := specPr (PUnit.{u + 1} × Γ) V
  have ha : a ≫ specPr (SDR3Orbit_OM L) V = prW := specAlong_pr V _
  refine ext_Pt (SDR3Orbit_δL L) V hF hq ?_
  let g : APt (fppfO B S hS) Γ (op (specObj (PUnit.{u + 1} × Γ) V)) :=
    APt.along (AddMonoidHom.inr PUnit.{u + 1} Γ) (specPt (PUnit.{u + 1} × Γ) V)
  let c₁W := APt.res prW.op c₁
  have hres : APt.res a.op (SDR3Orbit_c₀ L δ c₁ hL) = g.comp (AddMonoidHom.toMultiplicative δ) * c₁W := by
    refine MonoidHom.ext fun p => ?_
    by_cases h : δ p.toAdd ∈ L
    · rw [APt.res_apply, SDR3Orbit_c₀_pos L δ c₁ hL p h, map_mul]
      have e1 : (((fppfO B S hS).map a.op).hom) (APt.res (specPr (SDR3Orbit_OM L) V).op c₁ p) = c₁W p := by
        change _ = APt.res prW.op c₁ p
        rw [← ha, op_comp, APt.res_comp]
        rfl
      have e2 := congrArg (fun k => k (Multiplicative.ofAdd (SDR3Orbit_om L h))) (res_specAlong V (SDR3Orbit_OM L).subtype)
      rw [e1]
      have e3 : ((fppfO B S hS).map a.op).hom (specPt (SDR3Orbit_OM L) V (Multiplicative.ofAdd (SDR3Orbit_om L h))) =
          g (Multiplicative.ofAdd (δ p.toAdd)) := e2
      rw [e3, mul_comm]
      rfl
    · have h0 : c₁W p = 0 := by
        simp only [c₁W, APt.res_apply, hL p h, map_zero]
      rw [APt.res_apply, SDR3Orbit_c₀_neg L δ c₁ hL p h, map_zero, MonoidHom.mul_apply, h0, mul_zero]
  have h1 : a ≫ specLift (specPr (SDR3Orbit_OM L) V ≫ t) (SDR3Orbit_c₀ L δ c₁ hL) =
      specLift (prW ≫ t) (g.comp (AddMonoidHom.toMultiplicative δ) * c₁W) := by
    rw [SDR3Orbit_comp_specLift, hres, ← Category.assoc, ha]
  have h2 : prW ≫ specLift t c₁ = specLift (prW ≫ t) c₁W := SDR3Orbit_comp_specLift _ _ _
  have hinv := hx (prW ≫ t) g c₁W
  have hl : ∀ {Y Y' Y'' : BigFppfOver B S hS} (m : Y ⟶ Y') (n : Y' ⟶ Y'') (z : X.obj (op Y'')),
      X.map m.op (X.map n.op z) = X.map (m ≫ n).op z := fun m n z => by
    rw [op_comp, Functor.map_comp_apply]
  rw [hl, hl, hl, h1, hinv]
  change _ = X.map ((a ≫ specPr (SDR3Orbit_OM L) V) ≫ specLift t c₁).op x
  rw [ha, h2]

end Orbit

section Lift

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- `SDLocS_chart` for a surjective chart: `W' → V` is étale and surjective. -/
theorem SDR3Orbit_chart {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    (hsu : (MorphismProperty.presheaf (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) (SCH))) f)
    {V : BigFppfOver B S hS} (y : X.obj (op V)) :
    ∃ (W' : BigFppfOver B S hS) (p : W' ⟶ V) (s : W' ⟶ U), Etale ((SCH).map p) ∧ Surjective ((SCH).map p) ∧
      f.app (op W') s = X.map p.op y := by
  let g : yoneda.obj V ⟶ X := yonedaEquiv.symm y
  have hgapp : ∀ {T : BigFppfOver B S hS} (a : T ⟶ V), g.app (op T) a = X.map a.op y := fun a => by
    simp [g, yonedaEquiv_symm_app_apply]
  have hrep := hf.1
  have hw := hrep.isPullback' g
  refine ⟨hrep.pullback g, hrep.snd g, hrep.fst' g, hf.2 g _ _ (hrep.isPullback g), hsu.2 g _ _ (hrep.isPullback g), ?_⟩
  have h := congrArg (fun φ : yoneda.obj (hrep.pullback g) ⟶ X => φ.app (op (hrep.pullback g)) (𝟙 _)) hw.w
  change f.app (op (hrep.pullback g)) (𝟙 (hrep.pullback g) ≫ hrep.fst' g) =
    g.app (op (hrep.pullback g)) (𝟙 (hrep.pullback g) ≫ hrep.snd g) at h
  rw [Category.id_comp, Category.id_comp] at h
  rw [h, hgapp]

/-- An étale scheme over a field, nonempty, has a point in a finite separable extension. -/
theorem SDR3Orbit_residue {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) [Etale f] (y : Y) :
    ∃ (κ : Type u) (_ : Field κ) (_ : Algebra K κ) (_ : Module.Finite K κ) (_ : Algebra.IsSeparable K κ)
      (e : Spec (.of κ) ⟶ Y), e ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K κ)) := by
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  let m := hW.fromSpec ≫ f
  haveI : Etale m := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective m
  have hφe : φ.hom.Etale := by
    have : Etale (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 this
  letI : Algebra K Γ(Y, W) := φ.hom.toAlgebra
  have : Algebra.Etale K Γ(Y, W) := RingHom.etale_algebraMap.1 hφe
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := Algebra.Etale.iff_exists_algEquiv_prod K Γ(Y, W) |>.1 this
  have hne : Nontrivial Γ(Y, W) := by
    have hmem : ∃ z : Spec Γ(Y, W), True := by
      have : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hy
      obtain ⟨z, -⟩ := this
      exact ⟨z, trivial⟩
    obtain ⟨z, -⟩ := hmem
    exact (PrimeSpectrum.nonempty_iff_nontrivial).1 ⟨z⟩
  have hI : Nonempty I := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have : Subsingleton (Π i, Ai i) := inferInstance
    have h2 : Subsingleton Γ(Y, W) := e.toEquiv.subsingleton
    exact not_subsingleton _ h2
  obtain ⟨i⟩ := hI
  obtain ⟨h1, h2⟩ := hAi i
  let ψ : Γ(Y, W) →ₐ[K] Ai i := (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  refine ⟨Ai i, inferInstance, inferInstance, h1, h2, Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec, ?_⟩
  rw [Category.assoc]
  change _ ≫ m = _
  rw [← hφ, ← Spec.map_comp]
  congr 1
  ext k
  exact ψ.commutes k

end Lift

end AlgMag.SD

#print axioms AlgMag.SD.SDR3Orbit_const
#print axioms AlgMag.SD.SDR3Orbit_chart
#print axioms AlgMag.SD.SDR3Orbit_residue
