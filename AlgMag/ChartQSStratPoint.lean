/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartQSStab

/-!
# The stabilizer of a closed point, without separatedness

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


`exists_stabilizer_of_ideal` is the classification step of `ChartPoint.exists_stabilizer`, from any
ideal describing the stabilizer. With `exists_stab_ideal_closedPoint` it gives `H = D(M/Z₀)` and the
orbit map for a closed immersion `x : P → X`, `X` any presheaf with action.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.ChartQSStrat

open AlgMag.ChartPoint ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]

/-- The classification step of `exists_stabilizer`, from an ideal describing the stabilizer. -/
theorem exists_stabilizer_of_ideal (hK : IsField (RT P))
    (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X) (J : Ideal (R1 P M))
    (hJ : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ f ∈ J, evalAt ((SCH).map t).appTop.hom h f = 0) :
    ∃ Z₀ : AddSubgroup M, ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1 := by
  classical
  letI : Field (RT P) := hK.toField
  refine ⟨stabSubgroup J, ?_⟩
  have hone : ∀ f ∈ J, evalAt (algebraMap (RT P) (RT P)) (1 : Multiplicative M →* RT P) f = 0 := by
    intro f hf
    have := (hJ (𝟙 P) (1 : Multiplicative M →* _)).1 (by
      exact actX.one_smul (U := op P) _) f hf
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop] at this
    exact this
  have hmul : ∀ f ∈ J, evalAt (algebraMap (RT P) _) (diagPt J) f = 0 := by
    let Bq := R1 P M ⧸ J
    let R := Bq ⊗[RT P] Bq
    haveI : Algebra.FiniteType (RT P) (R1 P M) := AddMonoidAlgebra.finiteType_of_fg _ _
    haveI : Algebra.FiniteType (RT P) Bq :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ J) Ideal.Quotient.mk_surjective
    haveI : Algebra.FiniteType Bq R := inferInstance
    haveI : Algebra.FiniteType (RT P) R := Algebra.FiniteType.trans ‹_› ‹_›
    have hC : B.Contains (Spec (.of R)) := contains_ft (RT P) R (contains_RT P)
    let T := spObj P (algebraMap (RT P) R) hC
    let t : T ⟶ P := spToT P _ hC
    let sec : R →+* Γ((SCH).obj T, ⊤) := spSec P _ hC
    have ht : ((SCH).map t).appTop.hom = sec.comp (algebraMap (RT P) R) :=
      RingHom.ext fun b => spToT_appTop P _ hC b
    let i₁ : Bq →ₐ[RT P] R := Algebra.TensorProduct.includeLeft
    let i₂ : Bq →ₐ[RT P] R := Algebra.TensorProduct.includeRight
    have hi : ∀ i : Bq →ₐ[RT P] R, ∀ f ∈ J, evalAt ((SCH).map t).appTop.hom
        (sec.toMonoidHom.comp ((i : Bq →+* R).toMonoidHom.comp (bq J))) f = 0 := by
      intro i f hf
      have e : ∀ p : R1 P M, evalAt (algebraMap (RT P) R)
          ((i : Bq →+* R).toMonoidHom.comp (bq J)) p = i (Ideal.Quotient.mk J p) := by
        intro p
        induction p using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | single m c =>
          rw [evalAt_single, mk_single, map_smul, Algebra.smul_def]
          rfl
      rw [ht, eval_secPt, e, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero, map_zero]
    have h₁ := (hJ t _).2 (hi i₁)
    have h₂ := (hJ t _).2 (hi i₂)
    have hm := actX.mul_smul (U := op T) (sec.toMonoidHom.comp ((i₁ : Bq →+* R).toMonoidHom.comp (bq J)))
      (sec.toMonoidHom.comp ((i₂ : Bq →+* R).toMonoidHom.comp (bq J))) (x.app (op T) t)
    rw [h₂, h₁] at hm
    intro f hf
    have ed : (sec.toMonoidHom.comp ((i₁ : Bq →+* R).toMonoidHom.comp (bq J)) *
        sec.toMonoidHom.comp ((i₂ : Bq →+* R).toMonoidHom.comp (bq J)) :
          APt (fppfO B S hS) M (op T)) =
        sec.toMonoidHom.comp (diagPt J) := by
      ext m
      change sec _ * sec _ = sec _
      rw [← map_mul]
      congr 1
      change (bq J m ⊗ₜ[RT P] 1) * (1 ⊗ₜ[RT P] bq J m) = bq J m ⊗ₜ[RT P] bq J m
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hm' : actX.smul (U := op T) (sec.toMonoidHom.comp (diagPt J)) (x.app (op T) t) =
        x.app (op T) t := by
      rw [← ed]; exact hm
    have := (hJ t _).1 hm' f hf
    rw [ht, eval_secPt] at this
    exact (spSec_bijective P _ hC).1 (this.trans (map_zero _).symm)
  intro T t h
  rw [hJ t h]
  constructor
  · intro hk z hz
    have := hk _ hz
    rw [map_sub, evalAt_single, map_one, map_one, one_mul, sub_eq_zero] at this
    exact this
  · intro hz f hf
    exact eval_eq_zero_of_trivial_on hone hmul _ h (fun z hzJ => hz z hzJ) hf


/-- No separatedness: the stabilizer of a closed immersion `x : P → X`, `P` the spectrum of a
field, is `D(M/Z₀)`. -/
theorem exists_stabilizer_closedPoint (hK : IsField (RT P))
    (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X)
    (hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) x) :
    ∃ Z₀ : AddSubgroup M, ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1 := by
  obtain ⟨J, hJ⟩ := exists_stab_ideal_closedPoint actX x hx
  exact exists_stabilizer_of_ideal hK actX x J hJ

/-- Summary, no separatedness: `exists_orbit_mono` for a closed immersion `x`. -/
theorem exists_orbit_mono_closedPoint (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X)
    (hx : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) x)
    {Zp : BigFppfOver B S hS} (zS : X ⟶ yoneda.obj Zp)
    (hz : ∀ {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (y : X.obj (op T)),
      zS.app (op T) (actX.smul (U := op T) h y) = zS.app (op T) y)
    (ιz : P ⟶ Zp) [Mono ιz] (hxz : x ≫ zS = yoneda.map ιz) :
    ∃ (Z₀ : AddSubgroup M) (_ : AddMonoid.FG Z₀) (o : yoneda.obj (Ob P Z₀) ⟶ X),
      (∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
        actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
          ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1) ∧
      IsEquivariant (oAct Z₀) actX o ∧
      (∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P Z₀), o.app (op T) a = o.app (op T) b → a = b) := by
  obtain ⟨Z₀, hZ⟩ := exists_stabilizer_closedPoint hK actX x hx
  haveI hfg := fg_addSubgroup Z₀
  obtain ⟨o, ho⟩ := exists_orbit (N := Z₀) hK hX hZ
  exact ⟨Z₀, hfg, o, hZ, orbit_equivariant hK hX ho,
    fun a b hab => orbit_injective hK hX hZ ho zS hz ιz hxz a b hab⟩

end AlgMag.ChartQSStrat

#print axioms AlgMag.ChartQSStrat.exists_orbit_mono_closedPoint
