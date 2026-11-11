/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover221Gr
import AlgMag.Sec3Leftover328V
import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Algebraic Magnetism, Propositions 2.21 and 3.28 for a quasi-coherent `𝔸(M)_S`-`𝒪_S`-module

`AlgMag.P221.grOfAction`: a quasi-coherent `𝔸(M)_S`-`𝒪_S`-module `F` (Definition 2.20) is `M`-graded.
`AlgMag.P221.prop328_action`: Proposition 3.28 in the printed form, starting from the action.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9 AlgMag.VB

variable {S : Scheme.{u}} {F : S.Modules} [F.IsQuasicoherent] {M : Type u} [AddCommMonoid M]
  (D : Decomp (assocPMod F) M)

/-- `E_m` is the cokernel of `1 - π_m`. -/
def EmIsoCoker (m : M) : cokernel (𝟙 F - pi D m) ≅ Em D m where
  hom := cokernel.desc _ (retr D m) (by
    rw [Preadditive.sub_comp, Category.id_comp, pi_retr, sub_self])
  inv := incl D m ≫ cokernel.π _
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    have h : cokernel.π (𝟙 F - pi D m) = pi D m ≫ cokernel.π (𝟙 F - pi D m) := by
      have := cokernel.condition (𝟙 F - pi D m)
      rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at this
      exact this
    simp only [Category.comp_id, coequalizer_as_cokernel, cokernel.π_desc_assoc]
    rw [← Category.assoc, retr_incl]
    exact h.symm
  inv_hom_id := by
    simp only [Category.assoc, cokernel.π_desc, incl_retr]

instance isQuasicoherent_Em (m : M) : (Em D m).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso (EmIsoCoker D m)
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _)

variable (A : HModule (Hm M S) (assocPMod F))

/-- The decomposition of `W(F)` attached to an action (Proposition 9.11). -/
def decompOfAction : Decomp (assocPMod F) M :=
  hModuleEquivDecomp (isQCoh_assocPMod F) A

/-- **Proposition 2.21**, on objects: the grading of a quasi-coherent `𝔸(M)_S`-`𝒪_S`-module. Its
underlying module is `F` by definition. -/
def grOfAction : GrMod S M := grOf (decompOfAction A)

instance (m : M) : ((grOfAction A).P m).IsQuasicoherent :=
  isQuasicoherent_Em (decompOfAction A) m

/-- On an open `V`, the projection of `F` onto `E_m` is the component `ρ_m` of the action on `W(F)`. -/
lemma grOfAction_section (m : M) (V : S.Opens) (s : Γ(F, V)) :
    eV F V ((pi (decompOfAction A) m).app V s) =
      (decompOfAction A).comp m (TV V) (eV F V s) :=
  e_pi _ m V s

/-- **Proposition 3.28.** Let `E` be a quasi-coherent `𝔸(M)_S`-`𝒪_S`-module and `N` a magnet of `M`.
Then `V(E)^N` is canonically `V(E_N)`, with `E_N` the `N`-graded component of `E` for the action. -/
def prop328_action (N : AddSubmonoid M) :
    RepresentsAttractor (vActionS (grOfAction A)) N (yoneda.obj (VEN (grOfAction A) N)) :=
  prop328 (grOfAction A) N

end AlgMag.P221
