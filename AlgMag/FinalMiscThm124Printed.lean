/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscThm124Smooth
import AlgMag.Sec12PrintedSchemes

/-!
# Theorem 12.4 for `X` affine over `S`: the printed route

"By 11.2, `X^N → S` and `X^0 → S` are smooth, so by [32, Tag 067U] `X^0 → X^N` is a regular closed immersion. So by
[32, Tag 063M] the conormal sheaf `I/I²` is finite locally free hence projective."

`AlgMag.Sec12Printed.printed_affine` uses Cor 11.10 for the smoothness of `A₀ → B`. Here only Cor 11.2 is used
(`smooth_Zatt`, `smooth_Qalg`), then `printed_ring_smooth`.
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.Sec12Printed

open AlgMag.GB

attribute [local instance] gradedAlgebraOf


section Aug

variable {R A Z : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup Z] [DecidableEq Z]
  (𝒢 : Z → Submodule R A) [GradedAlgebra 𝒢] (Y : AddSubmonoid Z)
  {I₁ I₀ : Ideal A} (hI₁ : I₁ = magnetIdeal 𝒢 Y) (hI₀ : I₀ = magnetIdeal 𝒢 (⊥ : AddSubmonoid Z))
  (hsharp : ∀ y ∈ Y, ∀ y' ∈ Y, y + y' = 0 → y = 0)

/-- The data of `IsAug` for `A / J_Y`; the first part of the proof of `printed_graded`. -/
theorem printed_graded_aug (w : Z → ℕ)
    (hw : ∀ z, ∀ a ∈ 𝒢 z, Ideal.Quotient.mk I₁ a ≠ 0 → w z = 0 → z = 0)
    (hadd : ∀ u, ∀ a ∈ 𝒢 u, Ideal.Quotient.mk I₁ a ≠ 0 → ∀ v, ∀ b ∈ 𝒢 v,
      Ideal.Quotient.mk I₁ b ≠ 0 → w (u + v) = w u + w v) :
    letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
    letI := gradedB 𝒢 Y hI₁ hI₀ hsharp
    IsAug (gradB 𝒢 Y hI₁ hI₀ hsharp) (piB 𝒢 Y hI₁ hI₀ hsharp) w := by
  letI := (rho 𝒢 Y hI₁ hI₀ hsharp).toRingHom.toAlgebra
  letI := gradedB 𝒢 Y hI₁ hI₀ hsharp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro y _ ⟨a, ha, rfl⟩ hb e
    exact hw y a ha hb e
  · rintro u _ ⟨a, ha, rfl⟩ hb v _ ⟨d, hd, rfl⟩ hd'
    exact hadd u a ha hb v d hd hd'
  · rintro y hy _ ⟨a, ha, rfl⟩
    change Ideal.Quotient.mk I₀ a = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hI₀]
    exact mem_magnetIdeal_of_notMem (fun e => hy e) ha
  · rintro _ ⟨a, ha, rfl⟩
    change rho 𝒢 Y hI₁ hI₀ hsharp (Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I₁ a
    rw [rho_mk, pr0_of_mem 𝒢 ha, if_pos rfl]

end Aug

variable {S : Scheme.{u}} {M : Type u} [AddCommGroup M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M) {F : AddSubgroup M} (hF : IsFace F.toAddSubmonoid N)

/-- "By 11.2, `X^N → S` is smooth" (Cor 11.2 for `X → S`). -/
theorem smooth_Zatt [Smooth X.hom] : Smooth (Zatt act N).hom := by
  let g : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (Category.comp_id _)
  have : Smooth g.left := inferInstanceAs (Smooth X.hom)
  exact SmoothSchemes.smooth_repMap N (aY := SmoothSchemes.trivAction) g
    (fun _ _ => SmoothSchemes.term_ext _ _) (representsAttractor act N)
    (SmoothSchemes.repTerminal N) (Over.homMk (Zatt act N).hom (Category.comp_id _)) (fun T w => by
      refine AttractorPt.ext ?_
      funext T₁ t a
      exact SmoothSchemes.term_ext _ _)

/-- The chart of `X^N → S` over an affine open `U`: `A / J_N` is smooth over `Γ(S, U)`. -/
theorem smooth_Qalg [Smooth X.hom] (U : S.affineOpens) (N : AddSubmonoid M) :
    Algebra.Smooth Γ(S, U.1) (Qalg act N U.2) := by
  have := smooth_Zatt act N
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) (Qalg act N U.2))) ≫ U.2.fromSpec) := by
    have e := Over.w (iotaZ act N U)
    change (iotaZ act N U).left ≫ (Zatt act N).hom = _ at e
    change Smooth _
    rw [show (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) (Qalg act N U.2))) ≫ U.2.fromSpec) =
      (iotaZ act N U).left ≫ (Zatt act N).hom from e.symm]
    have := instOpenIotaZ act U N
    have h₁ : Smooth (iotaZ act N U).left := inferInstance
    exact MorphismProperty.comp_mem (@Smooth) _ _ h₁ ‹Smooth (Zatt act N).hom›
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf => by
      have : IsIso f := hf
      change Smooth f
      infer_instance
  have : MorphismProperty.HasOfPostcompProperty (@Smooth : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (@Smooth : MorphismProperty Scheme.{u})
      (fun f U hf => by
        have : Smooth f := hf
        infer_instance)
  have h₂ : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) (Qalg act N U.2)))) :=
    MorphismProperty.of_postcomp @Smooth (W' := @IsOpenImmersion) _ _ (show IsOpenImmersion U.2.fromSpec by unfold IsAffineOpen.fromSpec; infer_instance) h
  have h₃ := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 h₂
  exact (RingHom.smooth_algebraMap).1 h₃

variable {U : S.Opens} (hU : IsAffineOpen U)

/-- **Theorem 12.4** for `X` affine over `S`, printed route: Cor 11.2, then Tags 067U, 063M, 062Z.
`F` is a face subgroup of `N`. The statement is that of `printed_affine` without the finiteness. -/
theorem printed_affine_067U [Smooth X.hom] (h : N.FG ∨ AddGroup.FG M) :
    letI := (rho0 act N hF hU).toRingHom.toAlgebra
    Module.Projective (Qalg act F.toAddSubmonoid hU)
        (Conormal (piB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
          (sharp_Yq N hF))) ∧
      Nonempty (SymmetricAlgebra (Qalg act F.toAddSubmonoid hU)
        (Conormal (piB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
          (sharp_Yq N hF))) ≃ₐ[Qalg act F.toAddSubmonoid hU] Qalg act N hU) := by
  obtain ⟨Nc, hle, hFN, hfg, hsupp⟩ := exists_Nc act N hF hU h
  have hFc : IsFace F.toAddSubmonoid Nc :=
    ⟨hFN, fun {x y} hx hy e => hF.mem_of_add_mem (hle hx) (hle hy) e⟩
  obtain ⟨w, hw⟩ := exists_weight_of_isFace hFc hfg
  let f := QuotientAddGroup.mk' F
  -- `w` descends to `M/F`
  let wZ : M ⧸ F → ℕ := fun z =>
    if hz : ∃ n : Nc, f n = z then w hz.choose else 0
  have wZ_f : ∀ n : Nc, wZ (f n) = w n := by
    intro n
    have hz : ∃ n' : Nc, f n' = f n := ⟨n, rfl⟩
    have e : wZ (f n) = w hz.choose := dif_pos hz
    rw [e]
    obtain ⟨n', hn'⟩ : ∃ n' : Nc, n' = hz.choose := ⟨_, rfl⟩
    rw [← hn']
    have ef : f (n' : M) = f n := by rw [hn']; exact hz.choose_spec
    -- `n' = n + g` and `n = n' + g'` with `g, g' ∈ F`
    have hg₁ : -(n : M) + n' ∈ F := QuotientAddGroup.eq.1 ef.symm
    have hg₂ : -(n' : M) + n ∈ F := QuotientAddGroup.eq.1 ef
    let g₁ : Nc := ⟨_, hFN hg₁⟩
    let g₂ : Nc := ⟨_, hFN hg₂⟩
    have w₁ : w g₁ = 0 := (hw g₁).2 hg₁
    have w₂ : w g₂ = 0 := (hw g₂).2 hg₂
    have e₁ : n' = n + g₁ := Subtype.ext (by simp [g₁])
    rw [e₁, map_add, w₁, add_zero]
  have himg : ∀ z, ∀ a ∈ gZ act hU (F := F) z,
      Ideal.Quotient.mk (magnetIdeal (gradingOf hU act) N) a ≠ 0 → ∃ n : Nc, f n = z := by
    intro z a ha hne
    by_contra hz
    refine hne (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    refine pushGrading_induction (motive := fun a => a ∈ magnetIdeal (gradingOf hU act) N) ha
      (fun m hm b hb => hsupp m (fun hmc => hz ⟨⟨m, hmc⟩, hm⟩) b hb)
      (Ideal.zero_mem _) (fun a b h₁ h₂ => Ideal.add_mem _ h₁ h₂)
  letI := (rho0 act N hF hU).toRingHom.toAlgebra
  letI := gradedB (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU) (sharp_Yq N hF)
  have s₁ := smooth_Qalg act ⟨U, hU⟩ N
  have s₀ := smooth_Qalg act ⟨U, hU⟩ F.toAddSubmonoid
  have hIs := printed_graded_aug (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)
    (sharp_Yq N hF) wZ ?_ ?_
  · exact printed_ring_smooth (R := Γ(S, U))
      (piR (gZ act hU (F := F)) (Yq F N) (hI₁' act N hF hU) (hI₀' act hU)) (fun _ => rfl) hIs
  · intro z a ha hne hz0
    obtain ⟨n, rfl⟩ := himg z a ha hne
    rw [wZ_f] at hz0
    exact (QuotientAddGroup.eq_zero_iff _).2 ((hw n).1 hz0)
  · intro u a ha hne v b hb hne'
    obtain ⟨n, rfl⟩ := himg u a ha hne
    obtain ⟨n', rfl⟩ := himg v b hb hne'
    have : f (n : M) + f (n' : M) = f ((n + n' : Nc) : M) := by
      rw [AddSubmonoid.coe_add, map_add]
    rw [this, wZ_f, wZ_f, wZ_f, map_add]

#print axioms smooth_Qalg
#print axioms printed_affine_067U

end AlgMag.Sec12Printed
