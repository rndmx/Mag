/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBReal
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenCoverQuasicoherence

/-!
# §9 of *Algebraic Magnetism* over `B`: `IsQCoh` and sheaves of modules on the fppf sites of the `T`

An object of the site of `B` over `T` is a scheme over `T`, so a module `F` on the site of `B` restricts
to a family of values on `(Sch/T)_fppf`. `RestrIso F T G` says that this family is the sheaf of modules
`G` on `(Sch/T)_fppf`.

* `localAssoc_of_cokernelFree`: if `G` is a cokernel of free modules, `F` has the local datum of
  Tag 03DX (1), with no hypothesis (Stacks: the local step, Tag 070S (1), Tag 03DT).
* `isQCoh_iff_fppf`: `IsQCoh F` if and only if `F` is a Zariski sheaf and, over each affine `T`, it
  restricts to a quasi-coherent sheaf of modules on `(Sch/T)_fppf`. The implication from right to left
  takes essential surjectivity of Tag 03DX (1) as the hypothesis `Fppf03DX`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9BP

open AlgMag.S9B AlgMag.S9BF AlgMag.Leftover AlgMag.S9BS AlgMag.S9BR
open AlgMag.S9 (PMod IsBC)

/-- The scheme of an object of the site of `B` is a scheme of the big site. -/
abbrev hT (T : SB Bsp) : Bs.Contains T.left := T.obj.left.property

/-- `u : U ⟶ T`, as an object of `(Sch/T)_fppf`. -/
abbrev bigObj {U T : SB Bsp} (u : U ⟶ T) : BigFppfOver Bs T.left (hT T) :=
  Over.mk (SB.kmap (hT U) (hT T) (SB.Hom.left u))

/-- A morphism over `T`, as a morphism of `(Sch/T)_fppf`. -/
def bigHom {U U' T : SB Bsp} (s : U' ⟶ U) (u : U ⟶ T) : bigObj (s ≫ u) ⟶ bigObj u :=
  Over.homMk (SB.kmap (hT U') (hT U) (SB.Hom.left s)) (by
    ext
    exact (SB.comp_left s u).symm)

/-- The restriction of `F` to `(Sch/T)_fppf` is the sheaf of modules `G`. -/
structure RestrIso (F : PMod (OB Bsp)) (T : SB Bsp)
    (G : SheafOfModules.{u} (BigFppfOver.structureSheaf Bs T.left (hT T))) where
  /-- the identification of values -/
  e : ∀ {U : SB Bsp} (u : U ⟶ T), F.obj (op U) ≃+ G.val.obj (op (bigObj u))
  smul : ∀ {U : SB Bsp} (u : U ⟶ T) (a : (OB Bsp).obj (op U)) (x : F.obj (op U)),
    e u (a • x) =
      (show (BigFppfOver.structureSheaf Bs T.left (hT T)).obj.obj (op (bigObj u)) from a) • e u x
  nat : ∀ {U U' : SB Bsp} (s : U' ⟶ U) (u : U ⟶ T) (x : F.obj (op U)),
    e (s ≫ u) (F.map s.op x) = G.val.map (bigHom s u).op (e u x)

variable {T : SB Bsp}

/-- Stacks Tag 070S (1) and Tag 03DT: the values of `𝓕^a` are the sections `Γ(U, f^* 𝓕)`. -/
def sectionsIso (𝓕 : T.left.Modules) [𝓕.IsQuasicoherent]
    {G : SheafOfModules.{u} (BigFppfOver.structureSheaf Bs T.left (hT T))}
    (i : (BigFppfOver.associatedModule Bs T.left (hT T)).obj 𝓕 ≅ G) :
    BigFppfOver.sectionsPresheafOfModules Bs T.left (hT T) 𝓕 ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (BigFppfOver.structureSheaf Bs T.left (hT T)).obj)).obj G :=
  haveI := BigFppfOver.isIso_sheafificationAdjunction_unit_app Bs T.left (hT T)
    (BigFppfOver.sectionsPresheafOfModules Bs T.left (hT T) 𝓕)
    (BigFppfOver.isSheaf_sectionsPresheafOfModules Bs T.left (hT T)
      fpqcDescentOfQuasicoherentHoms 𝓕)
  asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (BigFppfOver.structureSheaf Bs T.left (hT T)).obj)).unit.app
        (BigFppfOver.sectionsPresheafOfModules Bs T.left (hT T) 𝓕)) ≪≫
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (BigFppfOver.structureSheaf Bs T.left (hT T)).obj)).mapIso
      ((BigFppfOver.associatedModuleIsoSections Bs T.left (hT T) 𝓕).symm ≪≫ i)

section Aux

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} {P P' : PresheafOfModules.{u} R}

/-- An isomorphism of presheaves of modules on values. -/
def pEquiv (φ : P ≅ P') (V : Cᵒᵖ) : P.obj V ≃+ P'.obj V where
  toFun := (φ.hom.app V).hom
  invFun := (φ.inv.app V).hom
  left_inv y := congrArg (fun k => (PresheafOfModules.Hom.app k V).hom y) φ.hom_inv_id
  right_inv y := congrArg (fun k => (PresheafOfModules.Hom.app k V).hom y) φ.inv_hom_id
  map_add' := map_add _

lemma pEquiv_smul (φ : P ≅ P') (V : Cᵒᵖ) (a : R.obj V) (x : P.obj V) :
    pEquiv φ V (a • x) = a • pEquiv φ V x :=
  (φ.hom.app V).hom.map_smul a x

lemma pEquiv_nat (φ : P ≅ P') {V V' : Cᵒᵖ} (f : V ⟶ V') (x : P.obj V) :
    pEquiv φ V' (P.map f x) = P'.map f (pEquiv φ V x) :=
  PresheafOfModules.naturality_apply φ.hom f x

end Aux

/-- The comparison over `T`, on values. -/
structure Cmp (𝓕 : T.left.Modules) [𝓕.IsQuasicoherent] (G : SheafOfModules.{u}
      (BigFppfOver.structureSheaf Bs T.left (hT T))) where
  /-- the identification of sections -/
  c : ∀ {U : SB Bsp} (u : U ⟶ T), (assocPMod 𝓕).obj (op (Over.mk (SB.Hom.left u))) ≃+
    G.val.obj (op (bigObj u))
  smul : ∀ {U : SB Bsp} (u : U ⟶ T) (a : (OB Bsp).obj (op U)) x,
    c u ((show (GB.overO T.left).obj (op (Over.mk (SB.Hom.left u))) from a) • x) =
      (show (BigFppfOver.structureSheaf Bs T.left (hT T)).obj.obj (op (bigObj u)) from a) • c u x
  nat : ∀ {U U' : SB Bsp} (s : U' ⟶ U) (u : U ⟶ T) x,
    c (s ≫ u) ((assocPMod 𝓕).map (Over.homMk (V := Over.mk (SB.Hom.left u))
        (U := Over.mk (SB.Hom.left (s ≫ u))) (SB.Hom.left s) (SB.comp_left s u).symm).op x) =
      G.val.map (bigHom s u).op (c u x)

/-- Stacks Tag 070S (1) and Tag 03DT, on values. -/
def cmp (𝓕 : T.left.Modules) [𝓕.IsQuasicoherent]
    {G : SheafOfModules.{u} (BigFppfOver.structureSheaf Bs T.left (hT T))}
    (φ : BigFppfOver.sectionsPresheafOfModules Bs T.left (hT T) 𝓕 ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 (BigFppfOver.structureSheaf Bs T.left (hT T)).obj)).obj G) : Cmp 𝓕 G where
  c u := pEquiv φ (op (bigObj u))
  smul u a x := pEquiv_smul φ (op (bigObj u)) a x
  nat s u x := pEquiv_nat φ (bigHom s u).op x

/-- **Bridge.** If the restriction of `F` to `(Sch/T)_fppf` is `𝓕^a`, then `F` has the local datum over
`T`. -/
def localAssocOfRestr {F : PMod (OB Bsp)} {G : SheafOfModules.{u}
      (BigFppfOver.structureSheaf Bs T.left (hT T))} (D : RestrIso F T G)
    (𝓕 : T.left.Modules) [h𝓕 : 𝓕.IsQuasicoherent] (K : Cmp 𝓕 G) : LocalAssoc F T where
  G := 𝓕
  qc := h𝓕
  ι u := (D.e u).trans (K.c u).symm
  smul u a x := by
    change (K.c u).symm (D.e u (a • x)) = _
    rw [D.smul, AddEquiv.symm_apply_eq, K.smul]
    change _ = _ • (K.c u) ((K.c u).symm (D.e u x))
    rw [AddEquiv.apply_symm_apply]
  nat s u x := (K.c (s ≫ u)).injective (by
    have h1 := K.nat s u ((K.c u).symm (D.e u x))
    rw [AddEquiv.apply_symm_apply] at h1
    exact ((K.c (s ≫ u)).apply_symm_apply _).trans ((D.nat s u x).trans h1.symm))

/-- Conversely, the local datum gives the identification with `𝓕^a`. -/
def restrOfLocal {F : PMod (OB Bsp)} (L : LocalAssoc F T) {G : SheafOfModules.{u}
      (BigFppfOver.structureSheaf Bs T.left (hT T))} (K : @Cmp _ _ _ _ T L.G L.qc G) : RestrIso F T G where
  e u := haveI := L.qc; (L.ι u).trans (K.c u)
  smul u a x := by
    haveI := L.qc
    change K.c u (L.ι u (a • x)) = _
    rw [L.smul, K.smul]
    rfl
  nat s u x := by
    haveI := L.qc
    change K.c (s ≫ u) (L.ι (s ≫ u) (F.map s.op x)) = _
    rw [L.nat, K.nat]
    rfl

/-- **Unconditional bridge.** If the restriction of `F` to `(Sch/T)_fppf` is a cokernel of free modules
(a presentation), then `F` has the local datum over `T`, hence the base change property over `T`
if `T` is affine. -/
theorem localAssoc_of_cokernelFree {F : PMod (OB Bsp)} {G : SheafOfModules.{u}
      (BigFppfOver.structureSheaf Bs T.left (hT T))} (D : RestrIso F T G) {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := BigFppfOver.structureSheaf Bs T.left (hT T)) I₂ ⟶
      SheafOfModules.free I₁)
    {π : SheafOfModules.free (R := BigFppfOver.structureSheaf Bs T.left (hT T)) I₁ ⟶ G}
    (hπ : α ≫ π = 0) (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    Nonempty (LocalAssoc F T) := by
  obtain ⟨𝓕, h𝓕, ⟨i⟩⟩ :=
    BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree' Bs T.left (hT T) α hπ hc
  haveI := h𝓕
  exact ⟨localAssocOfRestr D 𝓕 (cmp 𝓕 (sectionsIso 𝓕 i))⟩

/-- Essential surjectivity in Tag 03DX (1), for `τ = fppf` and every scheme of the site. The library
proves it over Tag 023T (`quasicoherentIsEssImageAssociatedModule_of_isEffective`). -/
def Fppf03DX (Bs : BigFppfSite.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (hX : Bs.Contains X) (G : SheafOfModules.{u} (BigFppfOver.structureSheaf Bs X hX)),
    G.IsQuasicoherentOnSite → ∃ 𝓕 : X.Modules, 𝓕.IsQuasicoherent ∧
      Nonempty ((BigFppfOver.associatedModule Bs X hX).obj 𝓕 ≅ G)

/-- `F` restricts over `T` to a quasi-coherent sheaf of modules on `(Sch/T)_fppf`: the printed notion
of §9, read on the localization of the site of `B` at `T`. -/
def IsQCohAt (F : PMod (OB Bsp)) (T : SB Bsp) : Prop :=
  ∃ G : SheafOfModules.{u} (BigFppfOver.structureSheaf Bs T.left (hT T)),
    G.IsQuasicoherentOnSite ∧ Nonempty (RestrIso F T G)

/-- **Bridge from the fppf sites of the `T`.** Given Tag 03DX (1) (`Fppf03DX`), a module which restricts
to a quasi-coherent sheaf of modules on `(Sch/T)_fppf` has the local datum over `T`. -/
theorem localAssoc_of_isQCohAt (h : Fppf03DX Bs) {F : PMod (OB Bsp)} (hF : IsQCohAt F T) :
    Nonempty (LocalAssoc F T) := by
  obtain ⟨G, hG, ⟨D⟩⟩ := hF
  obtain ⟨𝓕, h𝓕, ⟨i⟩⟩ := h T.left (hT T) G hG
  haveI := h𝓕
  exact ⟨localAssocOfRestr D 𝓕 (cmp 𝓕 (sectionsIso 𝓕 i))⟩

/-- A module restricting over every `T` to a quasi-coherent sheaf of modules on `(Sch/T)_fppf` has
`AlgMag.S9B.IsQCoh`, given Tag 03DX (1). -/
theorem isQCoh_of_isQCohAt (h : Fppf03DX Bs) {F : PMod (OB Bsp)} (hF : ∀ T : SB Bsp, IsQCohAt F T) :
    IsQCoh F :=
  isQCoh_of_localAssoc F fun T => (localAssoc_of_isQCohAt h (hF T)).some

/-- **`IsQCoh` is the printed notion.** With Tag 03DX (1): `IsQCoh F` if and only if `F` is a Zariski
sheaf and, over each affine `T`, it restricts to a quasi-coherent sheaf of modules on `(Sch/T)_fppf`.
The implication from left to right does not use `Fppf03DX`. -/
theorem isQCoh_iff_fppf (h : Fppf03DX Bs) (F : PMod (OB Bsp)) :
    IsQCoh F ↔
      (∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
        coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows) ∧
      ∀ (T : SB Bsp) [IsAffine T.left], IsQCohAt F T := by
  rw [isQCoh_iff_affine_local]
  refine and_congr_right fun _ => ?_
  refine forall_congr' fun T => ?_
  refine ⟨fun H _ => ?_, fun H _ => localAssoc_of_isQCohAt h H⟩
  obtain ⟨L⟩ := H
  haveI := L.qc
  exact ⟨(BigFppfOver.associatedModule Bs T.left (hT T)).obj L.G,
    BigFppfOver.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent Bs T.left (hT T) L.G L.qc,
    ⟨restrOfLocal L (cmp L.G (sectionsIso L.G (Iso.refl _)))⟩⟩

end AlgMag.S9BP

#print axioms AlgMag.S9BP.localAssocOfRestr
#print axioms AlgMag.S9BP.restrOfLocal
#print axioms AlgMag.S9BP.localAssoc_of_cokernelFree
#print axioms AlgMag.S9BP.localAssoc_of_isQCohAt
#print axioms AlgMag.S9BP.isQCoh_of_isQCohAt
#print axioms AlgMag.S9BP.isQCoh_iff_fppf
