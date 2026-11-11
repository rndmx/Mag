/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumRedAction
import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent

/-!
# The open subspace `X[1/N]` (affine stratum lemma, step 1)

`invSub X N` is the open subspace of the points of `X` on which the integer `N` is invertible.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- The base, as an object of the site. -/
abbrev baseObj (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : BigFppfOver B S hS :=
  Over.mk (𝟙 (B.obj hS))

/-- The open `S[1/N]`, as an object of the site. -/
noncomputable def baseInv (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (N : ℕ) :
    BigFppfOver B S hS :=
  Space.opensObject B S hS (baseObj B S hS)
    (show ((BigFppfOver.toScheme B S hS).obj (baseObj B S hS)).Opens from S.basicOpen (N : Γ(S, ⊤)))

noncomputable def baseInvι (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (N : ℕ) :
    baseInv B S hS N ⟶ baseObj B S hS := Space.opensObjectι B S hS _ _

/-- The structure map to the base. -/
noncomputable def toBaseObj (T : BigFppfOver B S hS) : T ⟶ baseObj B S hS :=
  Over.homMk T.hom (by simp)

lemma toBaseObj_uniq {T : BigFppfOver B S hS} (a : T ⟶ baseObj B S hS) : a = toBaseObj T := by
  ext1
  simpa [toBaseObj] using Over.w a

/-- `X → S` as a map of presheaves. -/
noncomputable def toBase (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : X ⟶ yoneda.obj (baseObj B S hS) where
  app T := ↾ fun _ => toBaseObj T.unop
  naturality T T' f := by
    ext1
    refine DFunLike.ext _ _ fun x => ?_
    exact (toBaseObj_uniq _).symm

lemma isOpenImmersion_baseInvι (N : ℕ) :
    AlgebraicGeometry.IsOpenImmersion ((SCH).map (baseInvι B S hS N)) := by
  change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := (SCH).obj (baseObj B S hS)) _)
  infer_instance

/-- `X[1/N]`. -/
noncomputable def invSub (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (N : ℕ) : Subfunctor X :=
  (Subfunctor.range (yoneda.map (baseInvι B S hS N))).preimage (toBase X)

/-- **Affine stratum lemma, step 1**: the sections of `X[1/N]` over `T` are the sections of `X`, if `N` is a
unit on `T`. -/
theorem mem_invSub_iff (N : ℕ) {T : BigFppfOver B S hS} (x : X.obj (op T)) :
    x ∈ (invSub X N).obj (op T) ↔ IsUnit (N : Γ((SCH).obj T, ⊤)) := by
  have hmem : x ∈ (invSub X N).obj (op T) ↔ ∃ t : T ⟶ baseInv B S hS N,
      t ≫ baseInvι B S hS N = toBaseObj T := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, ht⟩
  rw [hmem]
  constructor
  · rintro ⟨t, -⟩
    have h1 := isUnit_of_factor_basicOpen (V := S) (N : Γ(S, ⊤)) ((SCH).map t)
    rw [map_natCast] at h1
    exact h1
  · intro hu
    have hb : Set.range (structMap T) ⊆ Set.range (structMap (baseInv B S hS N)) := by
      rintro _ ⟨y, rfl⟩
      have h1 : y ∈ ((SCH).obj T).basicOpen (N : Γ((SCH).obj T, ⊤)) := by
        rw [Scheme.basicOpen_of_isUnit _ hu]; trivial
      have h2 := Scheme.preimage_basicOpen (structMap T) (N : Γ(S, ⊤))
      rw [map_natCast] at h2
      have h3 : y ∈ (structMap T) ⁻¹ᵁ S.basicOpen (N : Γ(S, ⊤)) := h2.symm ▸ h1
      exact ⟨⟨structMap T y, h3⟩, rfl⟩
    have hop : AlgebraicGeometry.IsOpenImmersion (structMap (baseInv B S hS N)) := by
      change AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι (X := S) (S.basicOpen (N : Γ(S, ⊤))) ≫ 𝟙 S)
      infer_instance
    obtain ⟨t⟩ := nonempty_hom_of_range hop hb
    exact ⟨t, toBaseObj_uniq _⟩

/-- `X[1/N]` is open. -/
theorem invSub_isOpen (hX : IsAlgebraicSpace B S hS X) (N : ℕ) :
    Space.IsOpenSubspace B S hS (invSub X N) := by
  have h1 : Space.IsOpenImmersion B S hS (yoneda.map (baseInvι B S hS N)) := by
    have := Space.inverseImage_isStableUnderBaseChange B S hS
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance
    exact MorphismProperty.relative_map (F := yoneda) (isOpenImmersion_baseInvι N)
  exact Space.isOpenSubspace_preimage B S hS (toBase X) _ (isAlgebraicSpace_yoneda B S hS _) hX
    (Space.isOpenSubspace_subfunctorRange B S hS (isAlgebraicSpace_yoneda B S hS _) h1)

end AlgMag.ChartStratum
