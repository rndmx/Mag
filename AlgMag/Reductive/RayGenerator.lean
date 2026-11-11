/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.SmoothKrullDim
import AlgMag.Reductive.RayBootstrap
import AlgMag.Reductive.R1Discharge
import AlgMag.Reductive.TorusRigidity

/-!
# The ray generator `δ₀` and the bootstrap inputs (items 1, 2)

* `isOfFinOrder_of_isNormalizingWith`: the Weyl automorphism `σ` of a `k`-point normalizing `T`
  has finite order (`finite_weylImage`).
* `exists_line_generator`: for a root `α` there is `δ₀ ≠ 0` with `α ∈ ℤδ₀` and every root
  proportional to `δ₀` in `ℤδ₀` (`exists_ray_generator` applied to the roots on `ℚα`, both signs
  folded onto the ray of `α`). So `hRay` holds for `δ₀`.
* `r1Geom_at_generator`: `r1Geom_of_opposite''` at `δ₀` (with `hRay` discharged).
-/

open Magnetism TauCeti TauCeti.Comodule WithConv AlgMag.Weyl

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X)

/-- **Item 1**: Weyl automorphisms have finite order. -/
theorem isOfFinOrder_of_isNormalizingWith [Group.FG X] (hπ : Function.Surjective π)
    {n : WithConv (H →ₐ[k] k)} {σ : X ≃* X} (hn : IsNormalizingWith π k n σ) :
    IsOfFinOrder σ := by
  haveI : Finite (weylGroup π k) := (finite_weylImage π hπ k).to_subtype
  have h := isOfFinOrder_of_finite (⟨σ, ⟨n, hn⟩⟩ : weylGroup π k)
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, congrArg Subtype.val hpow⟩

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

open scoped Classical in
/-- **Item 2**: a generator `δ₀` of the roots on the line of `α`. -/
theorem exists_line_generator [Module.Free ℤ (Additive X)] [Module.IsTorsionFree ℤ (Additive X)]
    {α : Additive X} (hα : α ∈ roots π) :
    ∃ δ : Additive X, δ ≠ 0 ∧ α ∈ lineMagnet δ ∧
      ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ := by
  have hα0 := ne_zero_of_mem_roots hα
  haveI : IsAddTorsionFree (Additive X) := .of_isTorsionFree ℤ (Additive X)
  haveI : IsMulTorsionFree X :=
    ⟨fun n hn => IsAddTorsionFree.nsmul_right_injective (M := Additive X) hn⟩
  obtain ⟨ψ₀, hψ₀⟩ := exists_generic_cocharacter {α} (Set.finite_singleton α)
    (fun β hβ => by rw [Set.mem_singleton_iff.1 hβ]; exact hα0)
  have h0 := hψ₀ α rfl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X →* Multiplicative ℤ, 0 < pairingHom ψ α := by
    rcases lt_or_gt_of_ne h0 with h | h
    · exact ⟨ψ₀⁻¹, by rw [pairingHom_inv]; omega⟩
    · exact ⟨ψ₀, h⟩
  set R := (roots_finite π).toFinset
  set t := R.filter (fun β => SameRayRel β α) ∪
    (R.filter (fun β => SameRayRel (-β) α)).image Neg.neg
  have ht : ∀ β ∈ t, SameRayRel β α := by
    intro β hβ
    rcases Finset.mem_union.1 hβ with h | h
    · exact (Finset.mem_filter.1 h).2
    · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 h
      exact (Finset.mem_filter.1 hγ).2
  obtain ⟨δ, hδpos, ⟨c, hc, hαc⟩, hall⟩ := exists_ray_generator ψ α hψ t ht
  have hδ0 : δ ≠ 0 := by rintro rfl; simp at hδpos
  refine ⟨δ, hδ0, ⟨c, by beta_reduce; rw [hαc, natCast_zsmul]⟩, ?_⟩
  rintro β hβ ⟨m, n, hn, h⟩
  have hβ0 := ne_zero_of_mem_roots hβ
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    exact hβ0 ((smul_eq_zero_iff_right hn).mp h)
  have hβR : β ∈ R := (Set.Finite.mem_toFinset _).2 hβ
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  -- `(c n) β = m α`
  have h' : ((c : ℤ) * n) • β = m • α := by
    rw [mul_smul, h, hαc, ← natCast_zsmul, smul_comm]
  rcases lt_or_gt_of_ne (mul_ne_zero (mul_ne_zero hc'.ne' hn) hm) with hmn | hmn
  · have h'' : ((c : ℤ) * n) • (-β) = (-m) • α := by rw [smul_neg, h', neg_smul]
    have hr := sameRay_of_zsmul h'' (by nlinarith)
    have hmem : -β ∈ t := Finset.mem_union_right _
      (Finset.mem_image.2 ⟨β, Finset.mem_filter.2 ⟨hβR, hr⟩, rfl⟩)
    obtain ⟨j, -, hj⟩ := hall _ hmem
    exact ⟨-(j : ℤ), by beta_reduce; rw [neg_smul, natCast_zsmul, ← hj, neg_neg]⟩
  · have hr := sameRay_of_zsmul h' hmn
    have hmem : β ∈ t := Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hβR, hr⟩)
    obtain ⟨j, -, hj⟩ := hall _ hmem
    exact ⟨j, by beta_reduce; rw [natCast_zsmul, ← hj]⟩

open R1Opp R1Build in
/-- **R1 at the line generator `δ₀`** (`r1Geom_of_opposite''` with `hRay` from
`exists_line_generator`): there is `δ₀ ≠ 0` with `α ∈ ℤδ₀` such that, for every `ψ`, the
Borel-side inputs at `δ₀` give `R1Geom π δ₀ ψ hπ`. -/
theorem r1Geom_at_generator [IsAlgClosed k] [Algebra.FiniteType k H] [Algebra.Smooth k H]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    [Module.IsTorsionFree ℤ (Additive X)] (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    {α : Additive X} (hα : α ∈ roots π) :
    ∃ δ : Additive X, δ ≠ 0 ∧ α ∈ lineMagnet δ ∧ ∀ ψ : X →* Multiplicative ℤ,
      ∀ (_ : Group.IsSolvable (WithConv (BAlg π δ ψ →ₐ[k] k)))
        (_ : Group.IsSolvable (WithConv (BmAlg π δ ψ →ₐ[k] k))),
      ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k)) →
      (∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k (ZAlg π δ) M]
        [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k (ZAlg π δ)),
        IsClosed (Set.range (projectiveOrbitMap (H := ZAlg π δ) m hm)) →
        (∀ a : WithConv (ZAlg π δ →ₐ[k] k),
          a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
              (CommAlgCat.of k k) ↔
            projectiveOrbitMap (H := ZAlg π δ) m hm (AlgHom.kernelPoint a.ofConv) =
              projectiveOrbitMap (H := ZAlg π δ) m hm
                (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (ZAlg π δ)))) →
        (∀ b : WithConv (BAlg π δ ψ →ₐ[k] k), BialgHom.mapDomain (fB π δ ψ) b ∈
          CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
            (CommAlgCat.of k k)) →
        Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
          (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S (CommAlgCat.of k k)) →
        ∀ a : WithConv (ZAlg π δ →ₐ[k] k),
          a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π δ)) S
            (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain (fB π δ ψ))) →
      Nonempty (R1Geom π δ ψ hπ) := by
  obtain ⟨δ, hδ0, hαδ, hRay⟩ := exists_line_generator π hα
  exact ⟨δ, hδ0, hαδ, fun ψ _ _ hT2 hBorStab =>
    r1Geom_of_opposite'' π δ ψ hπ hT hδ0 hRay hT2 hBorStab⟩

end AlgMag.Reductive
