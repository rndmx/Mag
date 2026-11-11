/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.ForwardAssembly
import AlgMag.Reductive.R1Geometry
import AlgMag.Reductive.ParabolicConnected

/-!
# Building `R1Geom` (plugging `R1Geometry` into `ForwardAssembly`)

`r1Geom_of_inputs` builds `R1Geom π α ψ hπ` for `Z = G^{ℤα}`, `B⁺ = P_Z(λ)`. It takes
`R1Geometry.r1Geom_fields` (applied with `k[Z] = ZAlg`, `k[B⁺] = BAlg`, `T_Z = TZ`), moves `g`
to `G(k)` along `zMk`, and descends `SQ` and `notC`.

Named inputs:
* `hLevi`: the Levi `Z_Z(λ)` is connected (so `B⁺` is connected, `connectedSpace_parabolic_of_levi`);
* `Bor`: `B⁺(k)` is solvable (instance argument);
* `hCB`: `C(k) ⊆ B⁺(k)`;
* `hinput : R1Geometry.OrbitInput fB TZ` (Stab(x₀)(k) ⊆ B⁺(k), and the second fixed point).
-/

set_option linter.style.haveILetI false

open Magnetism TauCeti TauCeti.HopfIdeal TauCeti.Cocharacter WithConv
open scoped TensorProduct

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [IsAlgClosed k]
variable (π : H →ₐc[k] MonoidAlgebra k X) (α : Additive X) (ψ : X →* Multiplicative ℤ)
variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

namespace R1Build

noncomputable local instance zDec' : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmooth' : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- `k[Z] ↠ k[B⁺]`. -/
noncomputable abbrev fB : ZAlg π α →ₐc[k] BAlg π α ψ :=
  Bialgebra.Quotient.mkBialgHom (parabolicDefiningHopfIdeal (zCochar π α ψ)).toIdeal

lemma fB_surjective : Function.Surjective (fB π α ψ) := Ideal.Quotient.mk_surjective

lemma zMk_surjective : Function.Surjective (zMk π α) := Ideal.Quotient.mk_surjective

lemma bMk_eq : bMk π α ψ = (fB π α ψ).comp (zMk π α) := rfl

/-- `T` as a Hopf ideal of `Z`. -/
noncomputable def TZ (hπ : Function.Surjective π) : HopfIdeal k (ZAlg π α) :=
  (TQ π α ψ hπ).comapOfSurjective (fB π α ψ) (fB_surjective π α ψ)

lemma TZ_comap (hπ : Function.Surjective π) :
    (TZ π α ψ hπ).comapOfSurjective (zMk π α) (zMk_surjective π α) =
      HopfIdeal.kerOfSurjective π hπ := by
  rw [TZ, HopfIdeal.comapOfSurjective_comapOfSurjective, ← TQ_comap π α ψ hπ]
  rfl

lemma TZ_isMaximalTorus (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k (ZAlg π α)) (TZ π α ψ hπ) :=
  isMaximalTorus_of_comapOfSurjective (zMk π α) (zMk_surjective π α) _
    (by rw [TZ_comap]; exact hT)

lemma zMk_mem_attractor (a : WithConv (ZAlg π α →ₐ[k] k)) :
    BialgHom.mapDomain (zMk π α) a ∈ attractorSubgroup π (lineMagnet α) k := by
  rw [mem_attractorSubgroup]
  intro x hx
  rw [← magnetHopfIdeal_toIdeal] at hx
  rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
  have : (zMk π α : H →ₐ[k] ZAlg π α) x = 0 := by
    change Ideal.Quotient.mk _ x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  rw [this, map_zero]

lemma mapDomain_bMk (b : WithConv (BAlg π α ψ →ₐ[k] k)) :
    BialgHom.mapDomain (bMk π α ψ) b =
      BialgHom.mapDomain (zMk π α) (BialgHom.mapDomain (fB π α ψ) b) := by
  apply WithConv.ofConv_injective
  ext x
  simp only [BialgHom.mapDomain_apply, ofConv_toConv]
  rfl

end R1Build

open R1Build in
/-- **`R1Geom` from the named geometric inputs.** -/
theorem r1Geom_of_inputs (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hLevi : ConnectedSpace (PrimeSpectrum
      (ZAlg π α ⧸ (leviDefiningHopfIdeal (zCochar π α ψ)).toIdeal)))
    [Group.IsSolvable (WithConv (BAlg π α ψ →ₐ[k] k))]
    (hCB : ∀ a : WithConv (ZAlg π α →ₐ[k] k),
      BialgHom.mapDomain (zMk π α) a ∈ attractorSubgroup π ⊥ k →
        a ∈ Set.range (BialgHom.mapDomain (fB π α ψ)))
    (hinput : R1Geometry.OrbitInput (fB π α ψ) (TZ π α ψ hπ)) :
    Nonempty (R1Geom π α ψ hπ) := by
  classical
  haveI : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _
  haveI : Algebra.Smooth k (BAlg π α ψ) := smooth_parQuot (zCochar π α ψ)
  haveI : IsReduced (BAlg π α ψ) := isReduced_of_smooth k _
  haveI : ConnectedSpace (PrimeSpectrum (BAlg π α ψ)) :=
    connectedSpace_parabolic_of_levi (zCochar π α ψ) hLevi
  obtain ⟨gZ, SQ, hSQ, hmax, hnot⟩ := R1Geometry.r1Geom_fields (fB π α ψ)
    (fB_surjective π α ψ) (TZ π α ψ hπ) (TZ_isMaximalTorus π α ψ hπ hT)
    {a | BialgHom.mapDomain (zMk π α) a ∈ attractorSubgroup π ⊥ k} hCB hinput
  refine ⟨{ g := BialgHom.mapDomain (zMk π α) gZ
            g_mem := zMk_mem_attractor π α gZ
            SQ := SQ
            hSQ := isMaximalTorus_of_comapOfSurjective (fB π α ψ) (fB_surjective π α ψ) SQ hmax
            hS := ?_
            notC := ?_ }⟩
  · have h1 : SQ.comapOfSurjective (bMk π α ψ) (bMk_surjective π α ψ) =
        (SQ.comapOfSurjective (fB π α ψ) (fB_surjective π α ψ)).comapOfSurjective (zMk π α)
          (zMk_surjective π α) := by
      rw [HopfIdeal.comapOfSurjective_comapOfSurjective]; rfl
    rw [h1, hSQ, ← HopfIdeal.conjugate_comapOfSurjective, TZ_comap]
    rfl
  · intro b hb
    apply hnot b
    show BialgHom.mapDomain (zMk π α) (BialgHom.mapDomain (fB π α ψ) b * gZ) ∈
      attractorSubgroup π ⊥ k
    rw [map_mul, ← mapDomain_bMk]
    exact hb

end AlgMag.Reductive
