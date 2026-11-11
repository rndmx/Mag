/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover221Act

/-!
# Algebraic Magnetism, Proposition 2.21: the two constructions are inverse on objects
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9 AlgMag.VB

open scoped Classical

variable {S : Scheme.{u}} {F : S.Modules} [F.IsQuasicoherent]

lemma IsBC.ind {R R' E E' : Type u} [CommRing R] [CommRing R'] [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] {φ : R →+* R'} {f : E →+ E'}
    {hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x} (h : IsBC φ f hf) {C : E' → Prop} (h0 : C 0)
    (hadd : ∀ a b, C a → C b → C (a + b)) (hs : ∀ (r : R') a, C a → C (r • a))
    (hm : ∀ v, C (f v)) (x : E') : C x := by
  letI := φ.toAlgebra
  letI : Module R E' := Module.compHom E' φ
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  exact IsBaseChange.inductionOn h x C h0 hm hs hadd

lemma isBC_induction {T T' : Over S} (s : T' ⟶ T) [IsAffine T.left] [IsAffine T'.left]
    {C : (assocPMod F).obj (op T') → Prop} (h0 : C 0)
    (hadd : ∀ a b, C a → C b → C (a + b))
    (hs : ∀ (r : (GB.overO S).obj (op T')) a, C a → C (r • a))
    (hm : ∀ v, C ((assocPMod F).map s.op v)) (x : (assocPMod F).obj (op T')) : C x := by
  exact IsBC.ind ((isQCoh_assocPMod F).base_change s) h0 hadd hs hm x

/-- A natural linear endomorphism of `W(F)` is determined by its values on the affine opens of `S`. -/
lemma linNat_ext {R R' : LinNat F}
    (h : ∀ (V : S.Opens), IsAffineOpen V → ∀ v, R.rho (TV V) v = R'.rho (TV V) v)
    (T : Over S) (x : (assocPMod F).obj (op T)) : R.rho T x = R'.rho T x := by
  have hF := isQCoh_assocPMod F
  let I := { W : T.left.Opens // IsAffineOpen W ∧ ∃ V : S.Opens, IsAffineOpen V ∧ W ≤ T.hom ⁻¹ᵁ V }
  have hcov : (⨆ i : I, (i.1 : T.left.Opens)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨V, hV, hyV, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (T.hom y)) isOpen_univ
    obtain ⟨V, hV', rfl⟩ := hV
    obtain ⟨W, hW, hyW, hWle⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ ((T.hom ⁻¹ᵁ (V : S.Opens) : T.left.Opens) : Set T.left) from hyV) (T.hom ⁻¹ᵁ _).isOpen
    obtain ⟨W, hW', rfl⟩ := hW
    exact Opens.mem_iSup.2 ⟨⟨W, hW', V, hV', hWle⟩, hyW⟩
  let 𝒰 := T.left.openCoverOfIsOpenCover (fun i : I => (i.1 : T.left.Opens)) (IsOpenCover.mk hcov)
  refine sep_cover hF T 𝒰 fun i => ?_
  rw [← R.nat, ← R'.nat]
  obtain ⟨V, hV, hWV⟩ := i.2.2
  have hW : IsAffineOpen (i.1 : T.left.Opens) := i.2.1
  haveI : IsAffine (coverPiece T 𝒰 i).left := hW
  haveI : IsAffine (TV V).left := hV
  have hr : Set.range (𝒰.f i ≫ T.hom) ⊆ Set.range V.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWV y.2
  let s : coverPiece T 𝒰 i ⟶ TV V :=
    Over.homMk (IsOpenImmersion.lift V.ι (𝒰.f i ≫ T.hom) hr) (IsOpenImmersion.lift_fac _ _ _)
  refine isBC_induction s (C := fun y => R.rho _ y = R'.rho _ y) ?_ ?_ ?_ ?_ _
  · rw [map_zero, map_zero]
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]
  · intro r a ha
    rw [map_smul, map_smul, ha]
  · intro v
    rw [R.nat, R'.nat, h V hV]

variable {M : Type u} [AddCommMonoid M]

/-- Two decompositions with the same components are equal. -/
lemma Decomp.ext' {D D' : Decomp (assocPMod F) M} (h : D.comp = D'.comp) : D = D' := by
  cases D; cases D'; cases h; rfl

instance instQcGrOf (D : Decomp (assocPMod F) M) (m : M) : ((grOf D).P m).IsQuasicoherent :=
  isQuasicoherent_Em D m

lemma pr_grOf (D : Decomp (assocPMod F) M) (m : M) : pr (grOf D) m = pi D m := by
  refine (grOf D).hom_ext fun k => ?_
  change incl D k ≫ pr (grOf D) m = incl D k ≫ pi D m
  refine (ι_pr (grOf D) m k).trans ?_
  change (if k = m then incl D k else 0) = _
  split_ifs with h
  · subst h; exact (incl_pi D k).symm
  · rw [← incl_pi D k, Category.assoc, pi_ortho D m k h, comp_zero]

/-- The natural family of a morphism of modules. -/
def lnOf (θ : F ⟶ F) : LinNat F where
  rho T :=
    { toFun := fun x => ((Scheme.Modules.pullback T.hom).map θ).app ⊤ x
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ r x }
  nat {T T'} s v := (pullbackSectionsMap_natural θ s v).symm

lemma lnOf_eV (θ : F ⟶ F) (V : S.Opens) (s : Γ(F, V)) :
    (lnOf θ).rho (TV V) (eV F V s) = eV F V (θ.app V s) :=
  (pullbackSectionHom_natural θ V.ι V ⊤ (top_le V) s).symm

/-- Every component of a decomposition is the pullback of `π_m`. -/
lemma comp_eq_pull (D : Decomp (assocPMod F) M) (m : M) (T : Over S)
    (x : (assocPMod F).obj (op T)) : D.comp m T x = (lnOf (pi D m)).rho T x := by
  refine linNat_ext (R := Rm D m) (R' := lnOf (pi D m)) (fun V _ v => ?_) T x
  obtain ⟨s, rfl⟩ := (eV_bijective F V).2 v
  rw [lnOf_eV]
  exact (e_pi D m V s).symm

/-- **Proposition 2.21**: a decomposition is recovered from its grading. -/
theorem decompOfGr_grOf (D : Decomp (assocPMod F) M) : decompOfGr (grOf D) = D := by
  refine Decomp.ext' ?_
  funext m T
  refine LinearMap.ext fun x => ?_
  refine Eq.trans ?_ (comp_eq_pull D m T x).symm
  change ((Scheme.Modules.pullback T.hom).map (pr (grOf D) m)).app ⊤ x = _
  rw [pr_grOf]
  rfl

/-- **Proposition 2.21**: an action is recovered from its grading. -/
theorem actionOfGr_grOfAction (A : HModule (Hm M S) (assocPMod F)) :
    actionOfGr (grOfAction A) = A := by
  exact (congrArg (hModuleEquivDecomp (isQCoh_assocPMod F)).symm
    (decompOfGr_grOf (decompOfAction A))).trans
    ((hModuleEquivDecomp (isQCoh_assocPMod F)).symm_apply_apply A)

end AlgMag.P221
