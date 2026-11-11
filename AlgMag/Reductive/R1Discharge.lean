/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.R1Opposite
import AlgMag.Reductive.LeviMagnet

/-!
# Discharging `hLevi` and `hCB` in `r1Geom_of_opposite`

* `hLevi_of_hZconn`: `Z = G^{ℤα}` connected ⇒ the Levi `Z_Z(λ)` connected
  (`connectedSpace_levi_of_openCell` + `isOpenEmbedding_openCell` on `Z`).
* `hCB_proof`: `C(k) = G^0(k) ⊆ P_Z(λ)(k) = B⁺(k)`, by `⊥ ≤ λ⁻¹(ℕ)` and the naturality of the
  dynamic parabolic along `zMk` (`conjugationAlgHom_natural`).
* `r1Geom_of_opposite'`: `R1Geom` from `hT`, `hZconn`, (Bor±), `hT2`, `hBorStab`.
-/

set_option linter.style.haveILetI false

open Magnetism TauCeti TauCeti.HopfIdeal TauCeti.Cocharacter TauCeti.Comodule WithConv

namespace AlgMag.Reductive

universe u

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [IsAlgClosed k]
variable (π : H →ₐc[k] MonoidAlgebra k X) (α : Additive X) (ψ : X →* Multiplicative ℤ)
variable [Algebra.FiniteType k H] [Algebra.Smooth k H]

namespace R1Dis

noncomputable local instance zDecD : DecidableEq (ZAlg π α) := Classical.decEq _
local instance zSmoothD : Algebra.Smooth k (ZAlg π α) := smooth_quotient_magnetHopfIdeal π _

/-- `Z` connected ⇒ `Z_Z(λ)` connected. -/
lemma hLevi_of_hZconn (hZconn : ConnectedSpace (PrimeSpectrum (ZAlg π α))) :
    ConnectedSpace (PrimeSpectrum
      (ZAlg π α ⧸ (leviDefiningHopfIdeal (zCochar π α ψ)).toIdeal)) := by
  haveI := hZconn
  haveI : IrreducibleSpace (PrimeSpectrum (ZAlg π α)) :=
    OpenCellNotes.irreducibleSpace_of_connectedSpace k
  exact connectedSpace_levi_of_openCell (zCochar π α ψ) (isOpenEmbedding_openCell _)

lemma zCochar_comp : (zCochar π α ψ).comp (zMk π α) = π.cocharacter ψ := by
  ext x n
  rw [BialgHom.comp_apply, zCochar_apply]

/-- A `Z`-point whose image in `G` lies in `P(λ)` lies in `P_Z(λ)`. -/
lemma mem_parabolic_zCochar (a : WithConv (ZAlg π α →ₐ[k] k))
    (ha : BialgHom.mapDomain (zMk π α) a ∈ parabolic k (π.cocharacter ψ)) :
    a ∈ parabolic k (zCochar π α ψ) := by
  classical
  rw [← negativeCoefficientIdeal_le_ker_iff] at ha ⊢
  rw [negativeCoefficientIdeal, Ideal.span_le]
  rintro _ ⟨y, n, hn, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have e := conjugationAlgHom_natural (π.cocharacter ψ) (zMk π α) (zCochar π α ψ)
    (zCochar_comp π α ψ) x
  have hx : (conjugationAlgHom (π.cocharacter ψ) x).coeff n ∈ negativeCoefficientIdeal
      (π.cocharacter ψ) := Ideal.subset_span ⟨x, n, hn, rfl⟩
  have h0 := ha hx
  rw [RingHom.mem_ker, BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply] at h0
  change a.ofConv ((conjugationAlgHom (zCochar π α ψ) (zMk π α x)).coeff n) = 0
  rw [e]
  simpa [AddMonoidAlgebra.mapAlgHom] using h0

/-- **`hCB`**: `C(k) ⊆ B⁺(k)`. -/
lemma hCB_proof (a : WithConv (ZAlg π α →ₐ[k] k))
    (ha : BialgHom.mapDomain (zMk π α) a ∈ attractorSubgroup π ⊥ k) :
    a ∈ Set.range (BialgHom.mapDomain (R1Build.fB π α ψ)) := by
  apply R1Opp.mem_range_of_mem_parabolic
  apply mem_parabolic_zCochar
  rw [← magnetIdeal_torusGrading_comap_nat_le_ker_iff]
  exact le_trans (magnetIdeal_anti_pure _ bot_le) ((mem_attractorSubgroup π).1 ha)

end R1Dis

open R1Opp R1Build R1Dis in
/-- **`R1Geom` from (Bor±), `hT2`, `hBorStab` and `hZconn`** (`hLevi`, `hCB` discharged). -/
theorem r1Geom_of_opposite' (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hZconn : ConnectedSpace (PrimeSpectrum (ZAlg π α)))
    [Group.IsSolvable (WithConv (BAlg π α ψ →ₐ[k] k))]
    [Group.IsSolvable (WithConv (BmAlg π α ψ →ₐ[k] k))]
    (hT2 : ¬ Group.IsSolvable (WithConv (ZAlg π α →ₐ[k] k)))
    (hBorStab : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k (ZAlg π α) M]
      [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k (ZAlg π α)),
      IsClosed (Set.range (projectiveOrbitMap (H := ZAlg π α) m hm)) →
      (∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := ZAlg π α) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := ZAlg π α) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (ZAlg π α)))) →
      (∀ b : WithConv (BAlg π α ψ →ₐ[k] k), BialgHom.mapDomain (fB π α ψ) b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (ZAlg π α)) S (CommAlgCat.of k k)) →
      ∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain (fB π α ψ))) :
    Nonempty (R1Geom π α ψ hπ) :=
  r1Geom_of_opposite π α ψ hπ hT (hLevi_of_hZconn π α ψ hZconn) hZconn (hCB_proof π α ψ) hT2
    hBorStab

open R1Opp R1Build R1Dis in
/-- **`R1Geom` with `hZconn` discharged** (`connectedSpace_lineAttractor`): from `hT`, `G`
connected, `X` free, `α ≠ 0`, `hRay` (roots in `ℚα` lie in `ℤα`), (Bor±), `hT2`, `hBorStab`. -/
theorem r1Geom_of_opposite'' [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [ConnectedSpace (PrimeSpectrum H)] [Module.Free ℤ (Additive X)]
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.kerOfSurjective π hπ))
    (hα0 : α ≠ 0)
    (hRay : ∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • α) → β ∈ lineMagnet α)
    [Group.IsSolvable (WithConv (BAlg π α ψ →ₐ[k] k))]
    [Group.IsSolvable (WithConv (BmAlg π α ψ →ₐ[k] k))]
    (hT2 : ¬ Group.IsSolvable (WithConv (ZAlg π α →ₐ[k] k)))
    (hBorStab : ∀ (M : Type u) [AddCommGroup M] [Module k M] [Comodule k (ZAlg π α) M]
      [Module.Finite k M] (m : M) (hm : Module.IsUnimodular k m) (S : HopfIdeal k (ZAlg π α)),
      IsClosed (Set.range (projectiveOrbitMap (H := ZAlg π α) m hm)) →
      (∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
            (CommAlgCat.of k k) ↔
          projectiveOrbitMap (H := ZAlg π α) m hm (AlgHom.kernelPoint a.ofConv) =
            projectiveOrbitMap (H := ZAlg π α) m hm
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k (ZAlg π α)))) →
      (∀ b : WithConv (BAlg π α ψ →ₐ[k] k), BialgHom.mapDomain (fB π α ψ) b ∈
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k)) →
      Group.IsSolvable (CommHopfAlgCat.quotientPointsSubgroup
        (_root_.CommHopfAlgCat.of k (ZAlg π α)) S (CommAlgCat.of k k)) →
      ∀ a : WithConv (ZAlg π α →ₐ[k] k),
        a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k (ZAlg π α)) S
          (CommAlgCat.of k k) → a ∈ Set.range (BialgHom.mapDomain (fB π α ψ))) :
    Nonempty (R1Geom π α ψ hπ) :=
  r1Geom_of_opposite' π α ψ hπ hT (connectedSpace_lineAttractor π hα0 hRay) hT2 hBorStab

end AlgMag.Reductive
