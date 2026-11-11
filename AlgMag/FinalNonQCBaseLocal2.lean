/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalNonQCBaseLocal
import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae

/-!
# A property local at the target, tested on the affine opens of the base

Stacks 03M4 in the form needed: test objects are affine, so finitely many affine opens of the test object, each lying over an
affine open of `S`, suffice.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.Final

open AlgMag.ChartAssembly LimThm LimOrbit CategoryTheory.OverShriek

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- A Zariski local property `P` of a morphism of algebraic spaces holds when it holds after restriction to every
affine open of `S`. -/
theorem presheaf_of_openBase {P : MorphismProperty Scheme.{u}} (hP : IsZariskiLocalAtTarget P)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (h : ∀ O : S.affineOpens,
      (P.inverseImage (BigFppfOver.toScheme B (openBase (B := B) (hS := hS) O.1).left.1
        (openBase (B := B) (hS := hS) O.1).left.2)).presheaf
        ((relocalizeRestrict (openBase (B := B) (hS := hS) O.1).hom).map f)) :
    (P.inverseImage (SCH)).presheaf f := by
  refine Space.presheaf_of_affineBaseChange B S hS hP hF hG fun T hT g => ?_
  let I : Type u := { W : ((SCH).obj T).Opens // ∃ O : S.affineOpens, ∀ τ ∈ W, structMap T τ ∈ O.1 }
  have hC : ∀ i : I, B.Contains (i.1 : Scheme.{u}) := fun i =>
    Scheme.size_lt_of_isOpenImmersion i.1.ι T.left.property
  let V : I → BigFppfOver B S hS := fun i => siteObject B S hS (hC i) (i.1.ι ≫ T.hom.hom)
  let π : ∀ i, V i ⟶ T := fun i => siteHom i.1.ι rfl
  have hoi : ∀ i, IsOpenImmersion ((SCH).map (π i)) := fun i => inferInstanceAs (IsOpenImmersion i.1.ι)
  have hcov0 : ∀ τ : (SCH).obj T, ∃ i : I, τ ∈ (i.1 : Set _) := fun τ => by
    obtain ⟨_, ⟨O, hO, rfl⟩, hs, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (structMap T τ)) isOpen_univ
    let W : ((SCH).obj T).Opens :=
      ⟨structMap T ⁻¹' O, O.isOpen.preimage (Scheme.Hom.continuous _)⟩
    exact ⟨⟨W, ⟨O, hO⟩, fun _ h => h⟩, hs⟩
  have key : ∀ i, ∃ (W : BigFppfOver B S hS) (p : W ⟶ V i) (q : yoneda.obj W ⟶ pullback f g),
      IsPullback q (yoneda.map p) (pullback.snd f g) (yoneda.map (π i)) ∧ P ((SCH).map p) := by
    intro i
    obtain ⟨O, hO⟩ := i.2
    obtain ⟨l, -⟩ := exists_lift_openBase (O := O.1) (V i) (fun τ => hO _ (τ : i.1.toScheme).2)
    obtain ⟨W, p, q, hpb, hPp⟩ := exists_rep_over _ f (h O) l (yoneda.map (π i) ≫ g)
    exact ⟨W, p, _, IsPullback.of_right' hpb (IsPullback.of_hasPullback f g), hPp⟩
  choose W p q hpb hPp using key
  obtain ⟨σ, hσ⟩ := (isCompact_univ (X := (SCH).obj T)).elim_finite_subcover
    (fun i : I => (i.1 : Set ((SCH).obj T))) (fun i => i.1.isOpen)
    fun y _ => Set.mem_iUnion.2 (hcov0 y)
  have hσcov : ∀ y : (SCH).obj T, ∃ i : {i // i ∈ σ},
      y ∈ Set.range ((SCH).map (π i.1)) := by
    intro y
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (hσ (Set.mem_univ y))
    refine ⟨⟨i, hi⟩, ?_⟩
    have : Set.range ((SCH).map (π i)) = (i.1 : Set _) := Scheme.Opens.range_ι i.1
    rw [this]
    exact hy
  have hcontains : ∀ (Z' : Scheme.{u}) (k : ∀ i : {i // i ∈ σ}, (SCH).obj (W i.1) ⟶ Z'),
      (∀ i, IsOpenImmersion (k i)) → (∀ z : Z', ∃ i, z ∈ Set.range (k i)) → B.Contains Z' := by
    intro Z' k hk hkcov
    rcases isEmpty_or_nonempty {i // i ∈ σ} with hemp | hne
    · exact B.contains_of_isEmpty ⟨fun z => hemp.false (hkcov z).choose⟩
    · have := hk
      exact B.contains_of_openCover
        (lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) B.aleph0_lt_cutoff_cof.le)
        k hkcov fun i => (W i.1).left.property
  obtain ⟨Y₀, e, p₀, hp₀, hPp₀⟩ := Space.exists_representing_over_of_openCover B S hS hP
    (BigFppfOver.isSheaf_pullback_yoneda_obj f g hF.isSheaf hG.isSheaf) (pullback.snd f g)
    (V := fun i : {i // i ∈ σ} => V i.1) (W := fun i => W i.1)
    (u := fun i => π i.1) (p := fun i => p i.1) (q := fun i => q i.1)
    (fun i => hoi i.1) hσcov (fun i => hpb i.1) (fun i => hPp i.1) hcontains
  refine ⟨Y₀, p₀, e.inv ≫ pullback.fst f g, ?_, hPp₀⟩
  exact (IsPullback.of_hasPullback f g).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simpa using hp₀) (by simp) (by simp)

end AlgMag.Final
