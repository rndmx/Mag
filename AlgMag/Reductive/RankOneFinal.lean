/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Reductive.EquivalenceFinal3
import AlgMag.Reductive.RankOneTrans

/-!
# (⇒) with inputs `hBruhat` and T2 only

`condI_condII_condIII_of_reductive_rankone` is `condI_condII_condIII_of_reductive_classical`
(T2Classical) without `hMaxOfT2`. Its inputs are:
* `hBruhat`: `BruhatRayCore` on root rays;
* `hT2`: `Z = G^{ℤδ}` has non-solvable `k`-points when `ℤδ` carries a root.

`hMaxOfT2` (T2 ⇒ `BorelZMax`) is now a theorem, `RankOneStructure.borelZMax_of_rayDim`, run on
the `rayDim ≤ 1` that `hBruhat` already produces. That proof is the density argument of
finish-plan §2 plus `T`-transitivity on `U_Z(λ^{∓1})(k) ∖ 1`, which comes from RayGa. `BorelZMax`
is only needed on lines `ℤδ` carrying a root. That is the only use made of it in
`condI_condII_condIII_of_reductive_final2` (`hR1at`), whose proof is reproduced below with
that one change.
-/

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Magnetism TauCeti TauCeti.Comodule WithConv AlgMag.Weyl
  TauCeti.Cocharacter

universe u

namespace AlgMag.Reductive

open R1Opp R1Build R1Dis Final2

variable {k : Type u} {H : Type u} {X : Type u}
variable [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H] [CommGroup X] [DecidableEq X]
variable [Algebra.FiniteType k H]

/-- **(⇒) assembled with inputs `hBruhat` and T2 only.** -/
theorem condI_condII_condIII_of_reductive_rankone [Module.IsTorsionFree ℤ (Additive X)]
    (π : H →ₐc[k] MonoidAlgebra k X)
    (hπ : Function.Surjective π)
    (hT : HopfIdeal.IsMaximalTorus k (CommHopfAlgCat.of k H) (HopfIdeal.kerOfSurjective π hπ))
    (hred : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H))
    (hBruhat : letI : Algebra.Smooth k H := hred.smooth
      haveI : IsMulTorsionFree X := ⟨fun n hn =>
        (IsAddTorsionFree.of_isTorsionFree ℤ (Additive X)).nsmul_right_injective hn⟩
      ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (hα : 0 < pairingHom ψ α),
        α ∈ roots π → BruhatRayCore π ψ α hα)
    (hT2 : letI : Algebra.Smooth k H := hred.smooth
      ∀ δ : Additive X, δ ≠ 0 →
        (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
        (∃ α ∈ roots π, α ∈ lineMagnet δ) →
        ¬ Group.IsSolvable (WithConv (ZAlg π δ →ₐ[k] k))) :
    CondI π ∧ CondII π ∧ CondIII π := by
  letI : Algebra.Smooth k H := hred.smooth
  haveI : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  haveI : Module.Finite k (Bialgebra.CotangentSpace k H) := inferInstance
  have : Algebra.FiniteType k (MonoidAlgebra k X) :=
    Algebra.FiniteType.of_surjective π.toAlgHom hπ
  haveI : Monoid.FG X := MonoidAlgebra.fg_of_finiteType (R := k)
  haveI : Group.FG X := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : Module.Finite ℤ (Additive X) :=
    Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2
      (Monoid.fg_iff_add_fg.1 inferInstance))
  haveI : Module.Free ℤ (Additive X) := Module.free_of_finite_type_torsion_free'
  haveI : IsAddTorsionFree (Additive X) := .of_isTorsionFree ℤ (Additive X)
  haveI : IsMulTorsionFree X :=
    ⟨fun n hn => IsAddTorsionFree.nsmul_right_injective (M := Additive X) hn⟩
  haveI : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_of_geometricallyConnected k H hred.geometricallyConnected
  haveI : IrreducibleSpace (PrimeSpectrum H) := OpenCellNotes.irreducibleSpace_of_connectedSpace k
  have hconnC : geometricallyConnectedCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥)).obj := by
    obtain ⟨ψc, hψc⟩ := exists_magnetIdeal_bot_eq_levi π
    rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace]
    have h0 := connectedSpace_levi_of_openCell (π.cocharacter ψc) (isOpenEmbedding_openCell _)
    have h' : ConnectedSpace (PrimeSpectrum (H ⧸ (magnetHopfIdeal π ⊥).toIdeal)) := by
      rw [magnetHopfIdeal_toIdeal, hψc, magnetIdeal_torusGrading_comap_bot]; exact h0
    exact h'
  haveI : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) (magnetHopfIdeal π ⊥))) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1 hconnC
  have hsolvC : geometricallySolvablePointsCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H)
        (magnetHopfIdeal π ⊥)).obj :=
    hsolvC_of_step2OverFpBar π hπ hT Step2BaseChange.step2OverFpBar
  -- T4 via the Bruhat core
  have hray : ∀ (ψ : X →* Multiplicative ℤ) (α : Additive X) (_ : 0 < pairingHom ψ α),
      rayDim π (pairingHom ψ) α ≤ 1 := by
    intro ψ α hα
    classical
    by_cases hne : ((posRoots π (pairingHom ψ)).filter (fun β => SameRayRel β α)).Nonempty
    · obtain ⟨β, hβ⟩ := hne
      obtain ⟨hβP, hβα⟩ := Finset.mem_filter.1 hβ
      obtain ⟨hβR, hβpos⟩ := Finset.mem_filter.1 hβP
      have heq : rayDim π (pairingHom ψ) α = rayDim π (pairingHom ψ) β := by
        unfold rayDim
        refine Finset.sum_congr (Finset.filter_congr fun γ _ => ?_) fun _ _ => rfl
        exact ⟨fun h => (sameRayRel_equivalence (X := X)).trans h
            ((sameRayRel_equivalence (X := X)).symm hβα),
          fun h => (sameRayRel_equivalence (X := X)).trans h hβα⟩
      rw [heq]
      letI : Algebra.Smooth k (ZAlg π (rayGen π ψ β hβpos).1) :=
        smooth_quotient_magnetHopfIdeal π _
      have hc := hBruhat ψ β hβpos ((finite_roots (π := π)).mem_toFinset.1 hβR)
      exact rayDim_le_one π (rayDimData_of_hAff π ψ β hβpos
        (hAff_of_bruhatCore _ hc.choose _ _ hc.choose_spec))
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      unfold rayDim
      rw [hne]
      simp
  let toψ : (Additive X →+ ℤ) → (X →* Multiplicative ℤ) := fun f =>
    { toFun := fun x => Multiplicative.ofAdd (f (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun a b => by simp [ofAdd_add] }
  have htoψ : ∀ f, pairingHom (toψ f) = f := fun f => by ext χ; rfl
  have hD : ∀ (f : Additive X →+ ℤ), ∀ α ∈ posRoots π f, Nonempty (RayDimData π f α) := by
    intro f α hα
    have hpos : 0 < pairingHom (toψ f) α := by
      rw [htoψ]; exact (Finset.mem_filter.1 hα).2
    letI : Algebra.Smooth k (ZAlg π (rayGen π (toψ f) α hpos).1) :=
      smooth_quotient_magnetHopfIdeal π _
    have hc := hBruhat (toψ f) α hpos
      ((finite_roots (π := π)).mem_toFinset.1 (Finset.mem_filter.1 hα).1)
    have := rayDimData_of_hAff π (toψ f) α hpos
      (hAff_of_bruhatCore _ hc.choose _ _ hc.choose_spec)
    rw [htoψ] at this
    exact ⟨this⟩
  have hT4 : ∀ (g : Additive X →+ ℤ), ∀ γ ∈ posRoots π g, rayDim π g γ ≤ 1 :=
    fun g γ hγ => rayDim_le_one π (hD g γ hγ).some
  -- hLie0
  obtain ⟨ψ₀, hψ₀⟩ := exists_generic_cocharacter (roots π) finite_roots
    (fun α hα => ne_zero_of_mem_roots hα)
  have hcent := hcent_CuIdeal_of_rayDim π (ψ := ψ₀)
    (fun φ _ α => hray φ α.1 α.2)
  have hCT' := HCTReal.hCT π hπ (CuIdeal π) (smooth_quotient_magnetHopfIdeal π ⊥) hconnC hsolvC
    (RuC_eq_augmentation π) hT (magnetHopfIdeal_bot_le_ker π hπ)
  have hLie0 := finrank_rootSpace_zero_le_of_reductive_Cu π hπ ψ₀ hψ₀ hred hcent hCT'
  -- (DC), (i), counts
  obtain ⟨ψ, hψ, hDC⟩ := dimCount_of_reductive'' π hπ hT hred hLie0 hD
  obtain ⟨h1, h2, h3⟩ := condI_and_counts_of_dimCount π hπ ψ hψ hDC
  -- (R1): `BorelZMax` at the generic `ψ₀`, from T2 and `rayDim ≤ 1` (density argument)
  have hR1at : ∀ δ : Additive X, δ ≠ 0 →
      (∀ β ∈ roots π, (∃ m n : ℤ, n ≠ 0 ∧ n • β = m • δ) → β ∈ lineMagnet δ) →
      (∃ α ∈ roots π, α ∈ lineMagnet δ) →
      ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X), IsNormalizingWith π k n σ ∧
        n ∈ attractorSubgroup π (lineMagnet δ) k ∧ σ ≠ 1 := by
    intro δ hδ hRay hroot
    obtain ⟨α, hα, hαδ⟩ := hroot
    have hφ : pairingHom ψ₀ δ ≠ 0 := by
      intro h0
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_lineMagnet.1 hαδ)
      apply hψ₀ _ hα
      rw [map_zsmul, h0, smul_zero]
    have hmax := RankOneStructure.borelZMax_of_rayDim π δ hδ hRay ψ₀ hφ
      (hT2 δ hδ hRay ⟨α, hα, hαδ⟩) (fun φ β hβ => hray φ β hβ)
    exact r1_of_borelZMax π hπ hT δ hδ hRay ψ₀ hφ hα hαδ (zzSolvable_of_hsolvC π hφ hsolvC) hmax
  have hR1 : ∀ α ∈ roots π, ∃ (n : WithConv (H →ₐ[k] k)) (σ : X ≃* X),
      IsNormalizingWith π k n σ ∧ n ∈ attractorSubgroup π (lineMagnet α) k ∧ σ ≠ 1 := by
    intro α hα
    obtain ⟨δ, hδ0, hαδ, hRayδ⟩ := exists_line_generator π hα
    obtain ⟨n, σ, hn, hmem, hσ⟩ := hR1at δ hδ0 hRayδ ⟨α, hα, hαδ⟩
    have hfin := isOfFinOrder_of_isNormalizingWith π hπ hn
    have hα0 := ne_zero_of_mem_roots hα
    obtain ⟨f, hf⟩ : ∃ f : Additive X →+ ℤ, 0 < f α := by
      rcases lt_or_gt_of_ne (hψ α hα) with h | h
      · exact ⟨-pairingHom ψ, by rw [AddMonoidHom.neg_apply]; omega⟩
      · exact ⟨pairingHom ψ, h⟩
    have hRayα := hRay_of_bootstrap π hπ hn hδ0 hmem hσ hfin hα hαδ f hf hT4
    exact hR1at α hα0 hRayα ⟨α, hα, mem_lineMagnet.2 (AddSubgroup.mem_zmultiples α)⟩
  -- (iii)
  let D := algClosedData π hπ h1
  have h3' : CondIII π := by
    intro α hα
    obtain ⟨n, σ, hn, hnα, hσ⟩ := hR1 α hα
    have hrefl := isReflectionOn_of_mem_lineAttractor D hα hn hnα hσ
    refine ⟨n, σ, hn, hnα, ?_⟩
    have := congrArg Additive.toMul hrefl.1
    simpa [actW] using this
  -- (ii′)
  have h2' : CondII π := by
    refine condII_of_counting π (pairingHom ψ) hψ h2 h3 ?_
    intro α hα
    obtain ⟨n, σ, hn, -, hσ⟩ := h3' α hα
    exact ⟨n, σ, hn, hσ⟩
  exact ⟨h1, h2', h3'⟩

end AlgMag.Reductive

#print axioms AlgMag.Reductive.condI_condII_condIII_of_reductive_rankone
