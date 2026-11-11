/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SDTorus
import AlgMag.SDExistMain
import AlgMag.SpacesDescentUnique

/-!
# Lemma D and Propositions 3.31 (ii), 3.32 (ii), 15.1 for algebraic spaces

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026).
The single remaining input is `SDLocS_LocalFactorAll X`, the local factorization of Part B, Steps 3-4.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgMag.SD

open AlgMag AlgMag.SQ AlgMag.SDTorus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

instance SDLocS_uniqueSums_lat (r : ℕ) : UniqueSums (Lat.{u} r) :=
  UniqueSums.of_injective_addHom (AddEquiv.ulift.{0, u} (α := Fin r → ℤ)).toAddMonoidHom.toAddHom
    (AddEquiv.ulift.{0, u} (α := Fin r → ℤ)).injective inferInstance

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The hypothesis of `SDExistGlue` is the peer's Step 2. -/
theorem SDLocS_uniqCoact (hX : IsAlgebraicSpace B S hS X) : SDExist_UniqCoact X :=
  by
    intro _ _ _ _ _ _ _ _ _ hι _ _ π i i₀ hπ x y h
    exact SDUnique_uniq_coact hX.diagonal_representable hι π i i₀ hπ x y h

/-- `Γ = ℤ^r` uniqueness in **Lemma D**. -/
theorem SDLocS_uniqZr (hX : IsAlgebraicSpace B S hS X) : UniqZr X :=
  fun _ _ _ _ _ _ _ δ j hj hk T _ x y h => SDUnique_uniq_of_isAlgebraicSpace hX δ j hj hk T x y h

/-- Part B, Steps 3-4 for all `ℤ^r`. -/
def SDLocS_LocalFactorAll (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ r : ℕ, SDExist_LocalFactor X (Lat.{u} r)

/-- `Γ = ℤ^r` existence in **Lemma D**. -/
theorem SDLocS_descZr (hX : IsAlgebraicSpace B S hS X) (hL : SDLocS_LocalFactorAll X) : DescZr X :=
  fun r _ _ _ _ _ _ δ j hj hk T _ x hx =>
    SDExist_desc hX (SDLocS_uniqCoact hX) (hL r) δ j hj hk T x hx

/-- **Lemma D** for an algebraic space. -/
theorem lemmaD_space (hX : IsAlgebraicSpace B S hS X) (hL : SDLocS_LocalFactorAll X) : DescentProp X :=
  descentProp_space hX (SDLocS_uniqZr hX) (SDLocS_descZr hX hL)

/-- **Proposition 3.32 (ii)** for an algebraic space. -/
theorem prop332_space (hX : IsAlgebraicSpace B S hS X) (hL : SDLocS_LocalFactorAll X) {M : Type u}
    [AddCommGroup M] [AddGroup.FG M] {aX : AAction (fppfO B S hS) M X} {N L : AddSubmonoid M}
    (T : BigFppfOver B S hS) :
    Function.Bijective (iterOfInf : AttractorPt aX (N ⊓ L) T → IterPt aX N L T) :=
  AlgMag.SDTorus.prop332 hX (SDLocS_uniqZr hX) (SDLocS_descZr hX hL) T

/-- **Proposition 3.31 (ii)** for an algebraic space. -/
theorem prop331_space (hX : IsAlgebraicSpace B S hS X) (hL : SDLocS_LocalFactorAll X) {M Z : Type u}
    [AddCommGroup M] [AddCommGroup Z] [AddGroup.FG M] [AddGroup.FG Z] {f : M →+ Z} {Y : AddSubmonoid Z}
    {aX : AAction (fppfO B S hS) M X} (T : BigFppfOver B S hS) :
    Function.Bijective (ptAlong aX : AttractorPt aX (Y.comap f) T → AttractorPt (actAlong f aX) Y T) :=
  AlgMag.SDTorus.prop331 hX (SDLocS_uniqZr hX) (SDLocS_descZr hX hL) T

/-- **Proposition 15.1** for a separated algebraic space and a finitely generated abelian group `M`. -/
theorem prop151_space (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X) (hL : SDLocS_LocalFactorAll X)
    {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {aX : AAction (fppfO B S hS) M X} (N : AddSubmonoid M) :
    IsPure (attractorImage aX) N ↔ ∀ L, L < N → attractorImage aX L < attractorImage aX N :=
  prop151_of_descent hX hsep (lemmaD_space hX hL) N

end AlgMag.SD

#print axioms AlgMag.SD.lemmaD_space
#print axioms AlgMag.SD.prop332_space
#print axioms AlgMag.SD.prop331_space
#print axioms AlgMag.SD.prop151_space
