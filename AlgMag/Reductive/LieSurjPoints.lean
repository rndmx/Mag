/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SubgroupFullLie
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Cotangent
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.DominantPoints
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map

/-!
# Lie-surjective homomorphisms of smooth groups over `k̄` are surjective on points

(P2-tan of ParabolicGenRay.) No closed-image theorem: injectivity of the comorphism from the
conormal space, then Tau Ceti `mapDomain_surjective_of_injective` (faithful flatness).
-/

suppress_compilation

open TauCeti

namespace AlgMag.Reductive

universe u

variable {k : Type u} [Field k]

/-- **(P2-tan-b) Lie surjective ⇒ injective comorphism.** Route: `J := ker φ` is a Hopf ideal
(Tau Ceti `HopfIdeal.ker`, flat over a field); `H₂/J ↪ H₁` reduced, so `H₂/J` is smooth over
`k̄` (`smoothCommHopfAlgProperty_of_geometricallyReduced`); Lie surjectivity forces
`Lie V(J) = Lie G₂`, so equal cotangent dimensions, and `eq_of_le_of_finrank_cotangent_eq`
(SubgroupFullLie.lean, `G₂` smooth connected) gives `J = 0`. PROVED. -/
theorem injective_of_lie_surjective [IsAlgClosed k]
    {H₁ H₂ : Type u} [CommRing H₁] [HopfAlgebra k H₁] [CommRing H₂] [HopfAlgebra k H₂]
    [Algebra.FiniteType k H₁] [Algebra.Smooth k H₁] [Algebra.FiniteType k H₂]
    [Algebra.Smooth k H₂] [ConnectedSpace (PrimeSpectrum H₂)]
    (φ : H₂ →ₐc[k] H₁) (hφ : Function.Surjective (derivationCompLieHom (B := k) φ)) :
    Function.Injective φ := by
  classical
  let J : TauCeti.HopfIdeal k H₂ := TauCeti.HopfIdeal.ker φ
  have hJ : J.toIdeal = RingHom.ker (φ : H₂ →ₐ[k] H₁) := TauCeti.HopfIdeal.ker_toIdeal φ
  -- (3) every derivation of `H₂` kills `J`, so the conormal space vanishes
  have hcon : TauCeti.HopfIdeal.conormalSubspace J = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (TauCeti.HopfIdeal.mem_conormalSubspace_iff J x).1 hx
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun f => ?_
    obtain ⟨e, he⟩ := hφ (Derivation.cotangentLinearEquiv (R := k) (A := H₂) (B := k) f)
    rw [hJ, RingHom.mem_ker] at hy
    have h1 := TauCeti.algEquivSelf_derivationComp_apply (B := k) φ e y
    rw [hy, map_zero, map_zero, ← derivationCompLieHom_apply, he] at h1
    have h2 := Derivation.algEquivSelf_ofCotangentLinearMap_apply (R := k) (A := H₂)
      (B := k) f y
    exact h2.symm.trans h1
  -- (2) `H₂ ⧸ J` embeds in the reduced `H₁`, hence is smooth over `k̄`
  have hred : IsReduced (H₂ ⧸ J.toIdeal) := by
    have : IsReduced H₁ := TauCeti.isReduced_of_smooth k H₁
    let ι : H₂ ⧸ J.toIdeal →+* H₁ :=
      Ideal.Quotient.lift J.toIdeal (φ : H₂ →ₐ[k] H₁).toRingHom
        (fun a ha => by rw [hJ] at ha; exact ha)
    refine isReduced_of_injective ι ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hJ]
    exact ha
  have hft : Algebra.FiniteType k (H₂ ⧸ J.toIdeal) := inferInstance
  have hsm : Algebra.Smooth k (H₂ ⧸ J.toIdeal) :=
    (TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k
      (_root_.CommHopfAlgCat.of k (H₂ ⧸ J.toIdeal))).2 hred
  -- (4) equal cotangent dimensions, so `J = 0`
  have hdim := TauCeti.HopfIdeal.finrank_quotientCotangent_add_finrank_conormal J
  rw [hcon, finrank_bot, add_zero] at hdim
  have hbot := toIdeal_eq_bot_of_finrank_cotangent_eq k H₂ J hdim
  rw [hJ] at hbot
  exact (injective_iff_map_eq_zero _).2 fun a ha =>
    (RingHom.mem_ker (f := (φ : H₂ →ₐ[k] H₁))).2 ha |> (hbot ▸ ·) |> (Ideal.mem_bot.1 ·)

/-- **(P2-tan) Tangent surjection ⇒ points surjection**, from (P2-tan-b) and Tau Ceti
`mapDomain_surjective_of_injective` (injective Hopf comorphism ⇒ surjective on `k̄`-points,
via faithful flatness). -/
theorem points_surjective_of_lie_surjective [IsAlgClosed k]
    {H₁ H₂ : Type u} [CommRing H₁] [HopfAlgebra k H₁] [CommRing H₂] [HopfAlgebra k H₂]
    [Algebra.FiniteType k H₁] [Algebra.Smooth k H₁] [Algebra.FiniteType k H₂]
    [Algebra.Smooth k H₂] [ConnectedSpace (PrimeSpectrum H₂)]
    (φ : H₂ →ₐc[k] H₁) (hφ : Function.Surjective (derivationCompLieHom (B := k) φ))
    (y : H₂ →ₐ[k] k) : ∃ x : H₁ →ₐ[k] k, y = x.comp (φ : H₂ →ₐ[k] H₁) := by
  obtain ⟨q, hq⟩ := TauCeti.CommHopfAlgCat.mapDomain_surjective_of_injective
    (H := _root_.CommHopfAlgCat.of k H₂) (K := _root_.CommHopfAlgCat.of k H₁) k
    (_root_.CommHopfAlgCat.ofHom φ) (injective_of_lie_surjective φ hφ) (WithConv.toConv y)
  exact ⟨q.ofConv, (congrArg WithConv.ofConv hq).symm⟩

end AlgMag.Reductive
