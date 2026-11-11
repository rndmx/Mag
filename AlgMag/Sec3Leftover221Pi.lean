/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SecLeftoverQCoh
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basis
import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Algebraic Magnetism, Proposition 2.21: from sections on `Sch/S` to endomorphisms of `F`

A family of natural linear endomorphisms of `W(F) : T ↦ Γ(T, p^* F)` is determined by its values on the
open subschemes of `S`, and gives an endomorphism of the `𝒪_S`-module `F`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]

/-- The open `V` as an `S`-scheme. -/
abbrev TV (V : S.Opens) : Over S := Over.mk V.ι

lemma top_le (V : S.Opens) : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2

/-- `Γ(F, V) → Γ(V, ι^* F)`. -/
def eV (V : S.Opens) : Γ(F, V) →+ (assocPMod F).obj (op (TV V)) :=
  (pullbackSectionHom V.ι F V ⊤ (top_le V)).hom

/-- A function on `V`, as a function on the `S`-scheme `V`. -/
def cV (V : S.Opens) (r : Γ(S, V)) : (GB.overO S).obj (op (TV V)) :=
  (V.ι.appLE V ⊤ (top_le V)).hom r

lemma eV_smul (V : S.Opens) (r : Γ(S, V)) (x : Γ(F, V)) :
    eV F V (r • x) = cV V r • eV F V x :=
  pullbackSectionHom_smul V.ι F V ⊤ (top_le V) r x

lemma eV_bijective (V : S.Opens) : Function.Bijective (eV F V) := by
  have hW : V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V := V.ι_image_top
  have hle : V.ι ''ᵁ (⊤ : V.toScheme.Opens) ≤ V := hW.le
  have h1 : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ (V.ι ''ᵁ ⊤) := (V.ι.preimage_image_eq ⊤).ge
  have hm : Function.Bijective (F.presheaf.map (homOfLE hle).op) := by
    have : IsIso (homOfLE hle).op := by
      have : IsIso (homOfLE hle) := ⟨homOfLE hW.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE hle).op)
  have hp : Function.Bijective (pullbackSectionHom V.ι F (V.ι ''ᵁ ⊤) ⊤ h1) := by
    have ht : ∀ t : Γ(F, V.ι ''ᵁ ⊤), pullbackSectionHom V.ι F (V.ι ''ᵁ ⊤) ⊤ h1 t =
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app F).val.app (op ⊤) t := by
      intro t
      have h2 := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection V.ι F (V.ι ''ᵁ ⊤) ⊤ h1
        le_rfl t
      have hid : F.val.map (homOfLE (le_refl (V.ι ''ᵁ (⊤ : V.toScheme.Opens)))).op t = t := by
        rw [show (homOfLE (le_refl (V.ι ''ᵁ (⊤ : V.toScheme.Opens)))).op = 𝟙 _ from Subsingleton.elim _ _]
        simp
        rfl
      rw [hid] at h2
      refine Eq.symm (Eq.trans (congrArg (fun y : (Scheme.Modules.restrict F V.ι).val.obj (op ⊤) =>
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app F).val.app (op ⊤) y) h2.symm) ?_)
      exact congrArg (fun k : (Scheme.Modules.pullback V.ι).obj F ⟶ (Scheme.Modules.pullback V.ι).obj F =>
        k.val.app (op ⊤) (Scheme.Modules.pullbackSection V.ι F (V.ι ''ᵁ ⊤) ⊤ h1 t))
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F).inv_hom_id
    refine (Function.bijective_iff_has_inverse).2
      ⟨fun y => ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app F).val.app (op ⊤) y, ?_, ?_⟩
    · intro t
      rw [ht]
      exact congrArg (fun k : (Scheme.Modules.restrict F V.ι) ⟶ (Scheme.Modules.restrict F V.ι) =>
        k.val.app (op ⊤) t) ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F).hom_inv_id
    · intro y
      refine (ht _).trans ?_
      exact congrArg (fun k : (Scheme.Modules.pullback V.ι).obj F ⟶ (Scheme.Modules.pullback V.ι).obj F =>
        k.val.app (op ⊤) y) ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F).inv_hom_id
  have hc : (eV F V : Γ(F, V) → _) = (pullbackSectionHom V.ι F (V.ι ''ᵁ ⊤) ⊤ h1) ∘
      (F.presheaf.map (homOfLE hle).op) := by
    funext a
    exact (pullbackSectionHom_map V.ι F V _ hle ⊤ h1 (top_le V) a).symm
  rw [hc]
  exact hp.comp hm

/-- `eV` as an additive equivalence. -/
def eVE (V : S.Opens) : Γ(F, V) ≃+ (assocPMod F).obj (op (TV V)) :=
  AddEquiv.ofBijective (eV F V) (eV_bijective F V)

/-- The inclusion of opens as a morphism of `S`-schemes. -/
def iLE {W V : S.Opens} (h : W ≤ V) : TV W ⟶ TV V :=
  Over.homMk (S.homOfLE h) (by simp)

lemma eV_res {W V : S.Opens} (h : W ≤ V) (x : Γ(F, V)) :
    eV F W (F.presheaf.map (homOfLE h).op x) = (assocPMod F).map (iLE h).op (eV F V x) := by
  have h1 := pullbackSectionHom_map W.ι F V W h ⊤ (top_le W)
    (fun y _ => h y.2) x
  have h2 := pullbackSectionsMap_pullbackSectionHom F (iLE h) V (top_le V)
    (fun y _ => h y.2) x
  exact h1.trans h2.symm

/-- A natural family of linear endomorphisms of `W(F)`. -/
structure LinNat where
  /-- value at `T` -/
  rho : ∀ T : Over S, (assocPMod F).obj (op T) →ₗ[(GB.overO S).obj (op T)] (assocPMod F).obj (op T)
  nat : ∀ {T T' : Over S} (s : T' ⟶ T) (v : (assocPMod F).obj (op T)),
    rho T' ((assocPMod F).map s.op v) = (assocPMod F).map s.op (rho T v)

variable {F}

lemma basis_id : Opens.IsBasis (Set.range (fun V : S.Opens => V)) := by
  rw [Opens.isBasis_iff_nbhd]
  exact fun {U x} hx => ⟨U, ⟨U, rfl⟩, hx, le_rfl⟩

lemma exists_pi (R : LinNat F) : ∃ π : F ⟶ F, ∀ (V : S.Opens) (s : Γ(F, V)),
    eV F V (π.app V s) = R.rho (TV V) (eV F V s) := by
  let g : ∀ V : S.Opens, Γ(F, V) →+ Γ(F, V) := fun V =>
    { toFun := fun s => (eVE F V).symm (R.rho (TV V) (eV F V s))
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hg : ∀ V s, eV F V (g V s) = R.rho (TV V) (eV F V s) := fun V s =>
    (eVE F V).apply_symm_apply _
  obtain ⟨φ, hφ⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.exists_hom_of_isBasis
    (M := F) (N := F) (fun V : S.Opens => V) basis_id g
    (fun V W h s => by
      apply (eV_bijective F W).1
      rw [hg, eV_res, eV_res, hg, R.nat])
    (fun V r s => by
      apply (eV_bijective F V).1
      rw [hg, eV_smul, eV_smul, hg]
      exact (R.rho (TV V)).map_smul _ _)
  exact ⟨φ, fun V s => by rw [hφ, hg]⟩

/-- The endomorphism of `F` attached to a natural family. -/
def piOf (R : LinNat F) : F ⟶ F := (exists_pi R).choose

lemma piOf_spec (R : LinNat F) (V : S.Opens) (s : Γ(F, V)) :
    eV F V ((piOf R).app V s) = R.rho (TV V) (eV F V s) :=
  (exists_pi R).choose_spec V s

end AlgMag.P221
