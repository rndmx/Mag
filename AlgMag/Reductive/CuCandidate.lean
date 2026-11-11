/-
`hcand` for `C_u = CuIdeal π` (pullback of `R_u(C)` along `H → H/C`, `C = G^0`):
`H/C_u ≅ (H/C)/R_u(C)` as Hopf algebras, and the candidate properties transfer along it.
-/
import AlgMag.Reductive.OpenCellGen

universe u

open CategoryTheory TauCeti

namespace AlgMag.Reductive

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable (π : H →ₐc[k] MonoidAlgebra k X) [Algebra.FiniteType k H]

/-- `H → H/C` as a bialgebra map. -/
noncomputable abbrev cMk : H →ₐc[k] (H ⧸ (magnetHopfIdeal π ⊥).toIdeal) :=
  Bialgebra.Quotient.mkBialgHom (R := k) (magnetHopfIdeal π ⊥).toIdeal

omit [Algebra.FiniteType k H] in
lemma cMk_surjective : Function.Surjective (cMk π) :=
  Ideal.Quotient.mk_surjective

/-- `CuIdeal` is the surjective inverse image of `R_u(C)`. -/
lemma CuIdeal_eq_comapOfSurjective :
    CuIdeal π = (RuC π).comapOfSurjective (cMk π) (cMk_surjective π) := by
  ext y
  rw [HopfIdeal.mem_comapOfSurjective, mem_CuIdeal]
  rfl

/-- `H ⧸ C_u ≅ (H ⧸ C) ⧸ R_u(C)` in `FiniteTypeCommHopfAlgCat`. -/
noncomputable def cuQuotientIso :
    FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        ((RuC π).comapOfSurjective (cMk π) (cMk_surjective π)) ≅
      FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) (RuC π) :=
  ObjectProperty.isoMk _
    (_root_.CommHopfAlgCat.Hom.quotientIsoOfSurjective
      (H := _root_.CommHopfAlgCat.of k H)
      (K := _root_.CommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
      (_root_.CommHopfAlgCat.ofHom (cMk π)) (cMk_surjective π) (RuC π))

lemma isCandidate_comapOfSurjective (hN : ((RuC π).comapOfSurjective (cMk π)
      (cMk_surjective π)).IsNormal) :
    HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H)
      ((RuC π).comapOfSurjective (cMk π) (cMk_surjective π)) := by
  obtain ⟨-, hgc, hsu⟩ :=
    FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
  refine ⟨hN, ?_, ?_⟩
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      ((ObjectProperty.ι _).mapIso (cuQuotientIso π)).symm hgc
  · exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso (cuQuotientIso π).symm hsu

/-- **`hcand` for `C_u`.** -/
theorem hcand_CuIdeal : (CuIdeal π).IsNormal →
    HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H) (CuIdeal π) := by
  rw [CuIdeal_eq_comapOfSurjective]
  exact isCandidate_comapOfSurjective π

/-- `H ⧸ C_u` is smooth (hence reduced). -/
theorem smooth_quotient_CuIdeal : Algebra.Smooth k (H ⧸ (CuIdeal π).toIdeal) := by
  rw [CuIdeal_eq_comapOfSurjective]
  obtain ⟨-, -, hsu⟩ :=
    FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
      (FiniteTypeCommHopfAlgCat.of k (H ⧸ (magnetHopfIdeal π ⊥).toIdeal))
  have h := (smoothUnipotentCommHopfAlgProperty k).prop_of_iso (cuQuotientIso π).symm hsu
  exact ((smoothUnipotentCommHopfAlgProperty_iff k _).1 h).1

instance isReduced_quotient_CuIdeal : IsReduced (H ⧸ (CuIdeal π).toIdeal) := by
  have := smooth_quotient_CuIdeal π
  exact TauCeti.isReduced_of_smooth k _

/-- `finrank_rootSpace_zero_le_of_reductive` with `Cu := CuIdeal π`: `hcand`, `hnormC` and the
reducedness instance discharged; remaining inputs `hcent`, `hCT`. -/
theorem finrank_rootSpace_zero_le_of_reductive_Cu [IsAlgClosed k]
    [Algebra.Smooth k H] [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [ConnectedSpace (PrimeSpectrum H)] (hπ : Function.Surjective π) (ψ : X →* Multiplicative ℤ)
    (hψ : ∀ α ∈ roots π, pairingHom ψ α ≠ 0)
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hcent : ∀ φ : X →* Multiplicative ℤ, (φ = ψ ∨ φ = ψ⁻¹) → ∀ α : PosRay φ,
      ∀ r ∈ rayPoints π φ α, ∀ c : WithConv (H →ₐ[k] k), (∀ y ∈ CuIdeal π, c.ofConv y = 0) →
        c * r = r * c)
    (hCT : CuIdeal π = HopfIdeal.augmentation k H →
      magnetHopfIdeal π ⊥ = HopfIdeal.kerOfSurjective π hπ) :
    Module.finrank k (rootSpace π 0) ≤
      Module.finrank k (Bialgebra.CotangentSpace k
        (H ⧸ (HopfIdeal.kerOfSurjective π hπ).toIdeal)) :=
  finrank_rootSpace_zero_le_of_reductive π hπ ψ hψ hred (CuIdeal π) hcent (hnormC_CuIdeal π)
    (hcand_CuIdeal π) hCT

end AlgMag.Reductive

