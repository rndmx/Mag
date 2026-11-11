/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartS5Chart
import AlgMag.ChartS5EB

/-!
# Equivariant Artin approximation, formal étaleness: `eA` on the site

Part of the proof of **Theorem 6.8 (ii)** (= Theorem A.2 (ii)) of Algebraic Magnetism (Mayeux,
Semigroup Forum 113 (2026)), through the specialization to `D(M)` of Alper–Hall–Rydh, Corollary 10.2.


`exists_eA`: for `Z → X` a closed immersion from an affine, and an étale chart `(V, v)` with a point
`P` over both, `Γ(V)/p^j ≃ Γ(Z)/𝔞^j` as soon as the ideal of `Z` in `V` lies in `p^j`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.ChartS5

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V Z P : BigFppfOver B S hS}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- **Formal étaleness.** -/
theorem exists_eA {e : yoneda.obj V ⟶ X} {o : yoneda.obj Z ⟶ X} (ho : ChartMain.ClosedP o) (he : EtP e)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)] [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    {k : Type u} [Field k] (iso : (BigFppfOver.toScheme B S hS).obj P ≅ Spec (.of k))
    (uz : P ⟶ Z) (v : P ⟶ V) (hw : yoneda.map uz ≫ o = yoneda.map v ≫ e)
    (huz : Function.Surjective ((BigFppfOver.toScheme B S hS).map uz).appTop.hom)
    (hv : Function.Surjective ((BigFppfOver.toScheme B S hS).map v).appTop.hom)
    [(RingHom.ker ((BigFppfOver.toScheme B S hS).map uz).appTop.hom).IsMaximal]
    (j : ℕ) (hker : (ChartMain.idealOf ho e).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom) ^ j) :
    Nonempty ((Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom) ^ j) ≃+*
      Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) ⧸
        (RingHom.ker ((BigFppfOver.toScheme B S hS).map uz).appTop.hom) ^ j) := by
  obtain ⟨hA, het, hsurj, hk, hc⟩ := etale_base_change_ideal ho he
  let τ := ho.rep.lift' uz v hw
  have hτ₁ : τ ≫ ho.rep.fst' e = uz := ho.rep.lift'_fst _ _ _
  have hτ₂ : τ ≫ ho.rep.snd e = v := ho.rep.lift'_snd _ _ _
  let r := ((BigFppfOver.toScheme B S hS).map (ho.rep.snd e)).appTop.hom
  let c₀ := ((BigFppfOver.toScheme B S hS).map (ho.rep.fst' e)).appTop.hom
  let κ := ((BigFppfOver.toScheme B S hS).map τ).appTop.hom
  have hκr : ∀ y, κ (r y) = ((BigFppfOver.toScheme B S hS).map v).appTop.hom y := fun y => by
    rw [← hτ₂, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have hκc : ∀ y, κ (c₀ y) = ((BigFppfOver.toScheme B S hS).map uz).appTop.hom y := fun y => by
    rw [← hτ₁, Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have hκs : Function.Surjective κ := fun y => by
    obtain ⟨a, rfl⟩ := hv y
    exact ⟨r a, hκr a⟩
  haveI hm𝔟 : (RingHom.ker κ).IsMaximal := by
    letI := (isField_of_iso iso).toField
    exact RingHom.ker_isMaximal_of_surjective _ hκs
  letI := c₀.toAlgebra
  haveI : Algebra.Etale Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) _ := het
  have hp : (RingHom.ker κ).comap r = RingHom.ker ((BigFppfOver.toScheme B S hS).map v).appTop.hom := by
    ext y; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hκr]
  have h𝔞 : (RingHom.ker κ).comap (algebraMap _ _) =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map uz).appTop.hom := by
    ext y; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    exact iff_of_eq (congrArg (· = 0) (hκc y))
  have hres : Function.Surjective ((Ideal.Quotient.mk (RingHom.ker κ)).comp (algebraMap _ _)) := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, hz⟩ := huz (κ y)
    refine ⟨z, Ideal.Quotient.eq.2 ?_⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (hκc z).trans hz
  exact ⟨eA_core r hsurj _ _ (RingHom.ker κ) hp h𝔞 hres j (hk.trans_le hker)⟩

end AlgMag.ChartS5

#print axioms AlgMag.ChartS5.exists_eA
