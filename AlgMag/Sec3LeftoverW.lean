/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Remaining
import AlgMag.GeneralBaseCore
import StacksFrontier.AlgebraicGeometry.Descent.SitePullbackSectionsModule

/-!
# Algebraic Magnetism, Definition 2.20: `W(F)(T) = Γ(T, p^* F)`

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). For an `𝒪_S`-module `F`, the functor
`W(F)` on `Sch/S` sends `p : T → S` to the global sections of `p^* F`; it is the presheaf of Stacks
03DS of the library, `sitePullbackSectionsPresheaf`. `AlgMag.W.AModule` is Definition 2.20: an
`𝒪_S`-linear action of `𝔸(M)_S` on `W(F)`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.W

open AlgMag.GB

variable {S : Scheme.{u}} (F : S.Modules)

/-- `W(F)`, with its abelian groups: `W(F)(T) = Γ(T, p^* F)` for `p : T → S`. -/
abbrev WAb : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} := sitePullbackSectionsPresheaf S F (𝟭 (Over S))

/-- `W(F)` as a functor to sets. -/
abbrev WF : (Over S)ᵒᵖ ⥤ Type u := WAb F ⋙ forget AddCommGrpCat

/-- `W(F)(T)` is the group of global sections of `p^* F`. -/
def WIso (T : Over S) : (WAb F).obj (op T) ≅ AddCommGrpCat.of Γ((Scheme.Modules.pullback T.hom).obj F, ⊤) :=
  (quasiCoherentPresheafConstruction S F).objIso (op T)

instance instAddCommGroupW (U : (Over S)ᵒᵖ) : AddCommGroup ((WF F).obj U) :=
  inferInstanceAs (AddCommGroup ((WAb F).obj U))

instance instModuleW (U : (Over S)ᵒᵖ) : Module ((overO S).obj U) ((WF F).obj U) :=
  sitePullbackSectionsModule S F (𝟭 (Over S)) U

variable (M : Type u) [AddCommMonoid M]

/-- **Definition 2.20.** An `𝔸(M)_S`-`𝒪_S`-module structure on `F`: an `𝒪_S`-linear action of the
`S`-monoid `𝔸(M)_S` on `W(F)`, compatible with morphisms `T' → T`. -/
abbrev AModule : Type _ := ModuleAAction (overO S) M (WF F)

end AlgMag.W
