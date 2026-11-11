/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover221Pi
import AlgMag.Sec3LeftoverAct

/-!
# Algebraic Magnetism, Proposition 2.21: a decomposition of `W(F)` grades `F`

The orthogonal idempotents `ρ_m` of a decomposition (Proposition 9.11) of `W(F)` are endomorphisms `π_m`
of the `𝒪_S`-module `F`; `E_m` is the image of `π_m`, and `F = ⨁_m E_m`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9 AlgMag.VB

open scoped Classical

variable {S : Scheme.{u}} {F : S.Modules} [F.IsQuasicoherent] {M : Type u} [AddCommMonoid M]
  (D : Decomp (assocPMod F) M)

/-- `ρ_m`, as a natural family. -/
def Rm (m : M) : LinNat F := ⟨D.comp m, D.natural m⟩

/-- `π_m : F → F`. -/
def pi (m : M) : F ⟶ F := piOf (Rm D m)

lemma e_pi (m : M) (V : S.Opens) (s : Γ(F, V)) :
    eV F V ((pi D m).app V s) = D.comp m (TV V) (eV F V s) :=
  piOf_spec (Rm D m) V s

lemma hom_ext_app {A B : S.Modules} {f g : A ⟶ B} (h : ∀ V (s : Γ(A, V)), f.app V s = g.app V s) :
    f = g :=
  Scheme.Modules.hom_ext f g fun U => by ext s; exact h U s

lemma comp_app_apply {A B C : S.Modules} (f : A ⟶ B) (g : B ⟶ C) (V : S.Opens) (s : Γ(A, V)) :
    (f ≫ g).app V s = g.app V (f.app V s) := by
  rw [Scheme.Modules.Hom.comp_app]; rfl

lemma pi_idem (m : M) : pi D m ≫ pi D m = pi D m := by
  refine hom_ext_app fun V s => (eV_bijective F V).1 ?_
  rw [comp_app_apply, e_pi, e_pi, D.same]

lemma pi_ortho (m k : M) (h : k ≠ m) : pi D k ≫ pi D m = 0 := by
  refine hom_ext_app fun V s => (eV_bijective F V).1 ?_
  rw [comp_app_apply, e_pi, e_pi, D.ne m k _ _ h]
  change _ = eV F V ((0 : F ⟶ F).app V s)
  rw [Scheme.Modules.Hom.zero_app]
  exact (map_zero (eV F V)).symm

lemma pi_finite (V : S.Opens) (hV : IsAffineOpen V) (s : Γ(F, V)) :
    (Function.support fun m => (pi D m).app V s).Finite := by
  haveI : IsAffine (TV V).left := hV
  refine (D.finite (TV V) (eV F V s)).subset fun m hm h0 => hm ?_
  apply (eV_bijective F V).1
  rw [e_pi, map_zero]
  exact h0

lemma pi_sum (V : S.Opens) (hV : IsAffineOpen V) (s : Γ(F, V)) :
    ∑ᶠ m, (pi D m).app V s = s := by
  haveI : IsAffine (TV V).left := hV
  apply (eV_bijective F V).1
  rw [AddMonoidHom.map_finsum _ (pi_finite D V hV s)]
  simp only [e_pi]
  exact D.sum (TV V) (eV F V s)

/-- `E_m`, the image of `π_m`. -/
def Em (m : M) : S.Modules := kernel (𝟙 F - pi D m)

/-- `E_m → F`. -/
def incl (m : M) : Em D m ⟶ F := kernel.ι _

/-- `F → E_m`. -/
def retr (m : M) : F ⟶ Em D m :=
  kernel.lift _ (pi D m) (by rw [Preadditive.comp_sub, Category.comp_id, pi_idem, sub_self])

lemma retr_incl (m : M) : retr D m ≫ incl D m = pi D m := kernel.lift_ι _ _ _

lemma incl_pi (m : M) : incl D m ≫ pi D m = incl D m := by
  have := kernel.condition (𝟙 F - pi D m)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
  exact this.symm

instance (m : M) : Mono (incl D m) := inferInstanceAs (Mono (kernel.ι _))

lemma incl_retr (m : M) : incl D m ≫ retr D m = 𝟙 _ := by
  rw [← cancel_mono (incl D m), Category.assoc, retr_incl, incl_pi, Category.id_comp]

lemma pi_retr (m : M) : pi D m ≫ retr D m = retr D m := by
  rw [← retr_incl, Category.assoc, incl_retr, Category.comp_id]

lemma incl_retr_ne (m k : M) (h : k ≠ m) : incl D m ≫ retr D k = 0 := by
  rw [← pi_retr D k, ← incl_pi D m, Category.assoc, ← Category.assoc (pi D m), pi_ortho D k m h.symm]
  simp

variable {Q : S.Modules} (c : ∀ m, Em D m ⟶ Q)

/-- `h_m : F → E_m → Q`. -/
def hm (m : M) : F ⟶ Q := retr D m ≫ c m

lemma hm_finite (V : S.Opens) (hV : IsAffineOpen V) (s : Γ(F, V)) :
    (Function.support fun m => (hm D c m).app V s).Finite := by
  refine (pi_finite D V hV s).subset fun m hm' h0 => hm' ?_
  change (hm D c m).app V s = 0
  have : hm D c m = pi D m ≫ hm D c m := by rw [hm, ← Category.assoc, pi_retr]
  rw [this, comp_app_apply]
  have h0' : (pi D m).app V s = 0 := h0
  rw [h0', map_zero]

/-- The affine opens, as a basis. -/
lemma basis_aff : Opens.IsBasis (Set.range (fun V : S.affineOpens => (V : S.Opens))) := by
  simpa using S.isBasis_affineOpens

lemma incl_hm (m : M) : incl D m ≫ hm D c m = c m := by
  rw [hm, ← Category.assoc, incl_retr, Category.id_comp]

lemma incl_hm_ne (m k : M) (h : k ≠ m) : incl D m ≫ hm D c k = 0 := by
  rw [hm, ← Category.assoc, incl_retr_ne D m k h, zero_comp]

/-- `s ↦ ∑ h_m(s)` on an affine open. -/
def gAff (V : S.affineOpens) : Γ(F, (V : S.Opens)) →+ Γ(Q, (V : S.Opens)) where
  toFun s := ∑ᶠ m, (hm D c m).app V s
  map_zero' := by
    simp only [map_zero]
    exact finsum_zero
  map_add' a b := by
    simp only [map_add]
    exact finsum_add_distrib (hm_finite D c V V.2 a) (hm_finite D c V V.2 b)

lemma exists_desc : ∃ φ : F ⟶ Q, ∀ (V : S.affineOpens) (s : Γ(F, (V : S.Opens))),
    φ.app V s = gAff D c V s := by
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis (M := F) (N := Q)
    (fun V : S.affineOpens => (V : S.Opens)) basis_aff (gAff D c) ?_ ?_
  · intro V W h s
    change ∑ᶠ m, (hm D c m).app W (F.presheaf.map (homOfLE h).op s) =
      Q.presheaf.map (homOfLE h).op (∑ᶠ m, (hm D c m).app V s)
    rw [AddMonoidHom.map_finsum (Q.presheaf.map (homOfLE h).op).hom (hm_finite D c V V.2 s)]
    refine finsum_congr fun m => ?_
    exact PresheafOfModules.naturality_apply (hm D c m).val (homOfLE h).op s
  · intro V r s
    change ∑ᶠ m, (hm D c m).app V (r • s) = r • ∑ᶠ m, (hm D c m).app V s
    rw [smul_finsum' r (hm_finite D c V V.2 s)]
    exact finsum_congr fun m => Scheme.Modules.Hom.app_smul _ r s

/-- `F` is the direct sum of the `E_m`. -/
def isColimitEm : IsColimit (Cofan.mk F (incl D)) :=
  mkCofanColimit _ (fun s => (exists_desc D s.inj).choose)
    (fun s m => by
      refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis basis_aff fun V x => ?_
      refine (comp_app_apply (incl D m) _ _ x).trans ?_
      refine ((exists_desc D s.inj).choose_spec V _).trans ?_
      change ∑ᶠ k, (hm D s.inj k).app V ((incl D m).app V x) = _
      rw [finsum_eq_single _ m]
      · rw [← comp_app_apply, incl_hm]
      · intro k hk
        rw [← comp_app_apply, incl_hm_ne D s.inj m k hk, Scheme.Modules.Hom.zero_app]
        rfl)
    (fun s f hf => by
      refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis basis_aff fun V x => ?_
      refine Eq.trans ?_ ((exists_desc D s.inj).choose_spec V x).symm
      change f.app V x = ∑ᶠ k, (hm D s.inj k).app V x
      conv_lhs => rw [← pi_sum D V V.2 x]
      rw [AddMonoidHom.map_finsum (f.app V).hom (pi_finite D V V.2 x)]
      refine finsum_congr fun m => ?_
      have e : hm D s.inj m = pi D m ≫ f := by
        rw [hm, ← hf m, ← retr_incl]
        simp [Category.assoc]
      rw [e, comp_app_apply])

/-- **Proposition 2.21**, from a decomposition to a grading. -/
def grOf : GrMod S M where
  E := F
  P := Em D
  ι := incl D
  isColimit := isColimitEm D

end AlgMag.P221
