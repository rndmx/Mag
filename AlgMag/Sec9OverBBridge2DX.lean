/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge2Flat

/-!
# Stacks 03DX (1), essential surjectivity, for `τ = fppf`

`Fppf03DX`, the hypothesis of `AlgMag.S9BP.isQCoh_iff_fppf`, is discharged by `fppf03DX`: a
quasi-coherent module `𝒢` on `(Sch/X)_fppf` is `𝓕^a`, with `𝓕` its restriction to `X_Zar`.

The proof does not go through the descent datum of the source, which the library leaves open
(`BigFppfOver.AssociatedModuleGlueDescentDatum`). It follows the counit argument the library uses at
`τ = étale` (`SmallEtale.isIso_counit`). The difference with the étale site is that a morphism of the
big site is not flat, so it has two steps: `𝒢` has base change along flat morphisms (`cart_of_flat`),
which gives the quasi-coherence of `𝓕` and the counit over the members of a flat cover; and it has
base change over those members (`cart_of_hasLocal`), which gives the counit above them.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open Stacks.PresheafOfModules

noncomputable section

namespace AlgMag.B2

open BigFppfOver

variable {B : BigFppfSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The structure map of `(Sch/X)_fppf → X_Zar`, valued in commutative rings. -/
def commStructureMap (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) :
    X.presheaf ⟶ (opensToBig B X hX).op ⋙ commStructurePresheaf B X hX where
  app U := (Scheme.Opens.topIso U.unop).inv
  naturality _ _ h := (Scheme.Opens.topIso_inv_appTop (X := X) (leOfHom h.unop)).symm

/-- **The restriction to `X_Zar` of a quasi-coherent module on `(Sch/X)_fppf` is quasi-coherent**:
its base change between nested affine opens is `cart_of_flat` along an open immersion. -/
theorem isQuasicoherent_restrictModule (G : SheafOfModules.{u} (structureSheaf B X hX))
    (hG : G.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ((restrictModule B X hX).obj G) := by
  refine Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction
    _ fun V V' hV hV' hle => ?_
  have hc : Cart B X hX G.val (opensHom B X hX hle) :=
    cart_of_flat G hG (U := opensObj B X hX V') (V := opensObj B X hX V) hV' hV _
      (inferInstanceAs (Flat (X.homOfLE hle)))
  exact Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars
    (commStructureMap B X hX)
    (fun U => inferInstanceAs (IsIso (Scheme.Opens.topIso U.unop).inv))
    ((PresheafOfModules.pushforward₀ (opensToBig B X hX)
      (commStructurePresheaf B X hX ⋙ forget₂ CommRingCat RingCat)).obj G.val)
    (homOfLE hle).op hc

variable (G : SheafOfModules.{u} (structureSheaf B X hX))

/-- The counit `𝓕^a ⟶ 𝒢`. -/
abbrev θ : (associatedModule B X hX).obj ((restrictModule B X hX).obj G) ⟶ G :=
  (associatedModuleAdjunction B X hX).counit.app G

variable {G}

lemma bij_val_app {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (hφ : IsIso φ) (T : Cᵒᵖ) :
    Function.Bijective (φ.val.app T) := by
  have := hφ
  have : IsIso (φ.val.app T) := (SheafOfModules.evaluation _ T).map_isIso φ
  exact ConcreteCategory.bijective_of_isIso _

/-- The counit is bijective over an open of `X`: the triangle identity and Stacks 0GN7. -/
theorem bij_θ_opens (hG : G.IsQuasicoherentOnSite) (V : X.Opens) :
    Function.Bijective ((θ G).val.app (op (opensObj B X hX V))) := by
  have h := isQuasicoherent_restrictModule G hG
  have hu : IsIso ((associatedModuleAdjunction B X hX).unit.app
      ((restrictModule B X hX).obj G)) :=
    unitIsoOnQuasicoherent B X hX ⟨(restrictModule B X hX).obj G, h⟩
  have hcomp : IsIso ((associatedModuleAdjunction B X hX).unit.app
      ((restrictModule B X hX).obj G) ≫
      (restrictModule B X hX).map ((associatedModuleAdjunction B X hX).counit.app G)) := by
    rw [(associatedModuleAdjunction B X hX).right_triangle_components G]
    infer_instance
  have hi : IsIso ((restrictModule B X hX).map (θ G)) :=
    IsIso.of_isIso_comp_left ((associatedModuleAdjunction B X hX).unit.app
      ((restrictModule B X hX).obj G)) _
  exact bij_val_app _ hi (op V)

/-- If `𝓕^a` and `𝒢` have base change along `f : U ⟶ V` and the counit is bijective over `V`, it is
bijective over `U`. -/
theorem bij_θ_step {U V : BigFppfOver B X hX} (f : U ⟶ V)
    (hA : Cart B X hX ((associatedModule B X hX).obj ((restrictModule B X hX).obj G)).val f)
    (hC : Cart B X hX G.val f) (hV : Function.Bijective ((θ G).val.app (op V))) :
    Function.Bijective ((θ G).val.app (op U)) := by
  classical
  have hVi : IsIso ((θ G).val.app (op V)) := (ConcreteCategory.isIso_iff_bijective _).2 hV
  have hE : Function.Bijective ((ModuleCat.extendScalars
      ((commStructurePresheaf B X hX).map f.op).hom).map ((θ G).val.app (op V))) :=
    ConcreteCategory.bijective_of_isIso
      (((ModuleCat.extendScalars ((commStructurePresheaf B X hX).map f.op).hom).mapIso
        (@asIso _ _ _ _ _ hVi)).hom)
  have hsq := restrictionBaseChange_naturality (R := commStructurePresheaf B X hX) (θ G).val f.op
  have hpt : ∀ x, restrictionBaseChange (R := commStructurePresheaf B X hX) G.val f.op
        ((ModuleCat.extendScalars ((commStructurePresheaf B X hX).map f.op).hom).map
          ((θ G).val.app (op V)) x) =
      (θ G).val.app (op U) (restrictionBaseChange (R := commStructurePresheaf B X hX)
        ((associatedModule B X hX).obj ((restrictModule B X hX).obj G)).val f.op x) :=
    fun x => ConcreteCategory.congr_hom hsq x
  have hcomp : Function.Bijective (fun x => (θ G).val.app (op U)
      (restrictionBaseChange (R := commStructurePresheaf B X hX)
        ((associatedModule B X hX).obj ((restrictModule B X hX).obj G)).val f.op x)) := by
    refine (funext hpt : _ = _) ▸ ?_
    exact hC.comp hE
  exact (hA.of_comp_iff _).1 hcomp

/-- A sieve containing the maps from the objects where the counit is bijective is covering. -/
theorem mem_topology_of_good (hG : G.IsQuasicoherentOnSite) (T : BigFppfOver B X hX) (R : Sieve T)
    (hR : ∀ {Y : BigFppfOver B X hX} (h : Y ⟶ T), Function.Bijective ((θ G).val.app (op Y)) → R h) :
    R ∈ topology B X hX T := by
  classical
  haveI := isQuasicoherent_restrictModule G hG
  -- affine opens of `T` over affine opens of `X`
  let J₁ := ULift.{u + 1} {A : (T.left.obj : Scheme.{u}).Opens //
    IsAffineOpen A ∧ ∃ V : X.Opens, IsAffineOpen V ∧ A ≤ T.hom.hom ⁻¹ᵁ V}
  let Wo : J₁ → B.Schemes := fun i => B.obj (contains_opens B T.left.property i.down.1)
  let m : ∀ i : J₁, Wo i ⟶ T.left := fun i =>
    ObjectProperty.homMk (X := Wo i) (Y := T.left) i.down.1.ι
  have hfl : ∀ i, Flat (B.inclusion.map (m i)) := fun i => inferInstanceAs (Flat i.down.1.ι)
  have hlf : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (m i)) := fun i =>
    inferInstanceAs (LocallyOfFinitePresentation i.down.1.ι)
  have hsu : ∀ x : (B.inclusion.obj T.left), ∃ i : J₁, x ∈ Set.range (B.inclusion.map (m i)) := by
    intro x
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
      (x := T.hom.hom x) (U := ⊤) trivial
    obtain ⟨A, hA, hxA, hAV⟩ := exists_isAffineOpen_mem_and_subset (X := T.left.obj)
      (x := x) (U := T.hom.hom ⁻¹ᵁ V) hxV
    refine ⟨⟨⟨A, hA, V, hV, hAV⟩⟩, ⟨x, hxA⟩, rfl⟩
  have hS1 := mem_topology_of_family B X hX Wo m hfl hlf hsu
  refine (topology B X hX).transitive hS1 R ?_
  rintro Y f ⟨Y', a, b, ⟨i⟩, rfl⟩
  obtain ⟨⟨A, hA, V, hV, hAV⟩⟩ := i
  rw [Sieve.pullback_comp]
  refine (topology B X hX).pullback_stable a ?_
  let P : BigFppfOver B X hX := Over.mk (m ⟨⟨A, hA, V, hV, hAV⟩⟩ ≫ T.hom)
  have hPaff : Aff B X hX P := hA
  let e : P ⟶ T := Over.homMk (m ⟨⟨A, hA, V, hV, hAV⟩⟩)
  have hVa : Aff B X hX (opensObj B X hX V) := hV
  let k : P ⟶ opensObj B X hX V := homOfRangeLe B X hX V (by
    rintro _ ⟨y, rfl⟩
    exact hAV y.2)
  obtain ⟨I, hI, W, g, hW, hL, hfl', hcover⟩ := exists_family G hG hVa
  have hcoverP : Sieve.ofArrows (fun i => pullback k (g i))
      (fun i => pullback.fst k (g i)) ∈ topology B X hX P := by
    refine (topology B X hX).superset_covering ?_ ((topology B X hX).pullback_stable k hcover)
    intro Z h hh
    obtain ⟨Y, g₁, g₂, ⟨i⟩, hg⟩ := hh
    have hmem := (Sieve.ofArrows (fun i => pullback k (g i))
        (fun i => pullback.fst k (g i))).downward_closed
      (Sieve.ofArrows_mk (fun i => pullback k (g i)) (fun i => pullback.fst k (g i)) i)
      (pullback.lift h g₁ hg.symm)
    rwa [pullback.lift_fst] at hmem
  refine (topology B X hX).superset_covering ?_ hcoverP
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  have hPi := aff_pullback hPaff hVa (hW i) k (g i)
  have h1 : Function.Bijective ((θ G).val.app (op (W i))) :=
    bij_θ_step (g i) (cart_assoc _ (hW i) hVa _) (cart_of_flat G hG (hW i) hVa _ (hfl' i))
      (bij_θ_opens hG V)
  have h2 : Function.Bijective ((θ G).val.app (op (pullback k (g i)))) :=
    bij_θ_step (pullback.snd k (g i)) (cart_assoc _ hPi (hW i) _)
      (cart_of_hasLocal G (hL i) hPi (hW i) _ (𝟙 _)) h1
  exact hR (pullback.fst k (g i) ≫ e) h2

/-- **The counit is an isomorphism** at a quasi-coherent module on `(Sch/X)_fppf`. -/
theorem isIso_θ (hG : G.IsQuasicoherentOnSite) : IsIso (θ G) := by
  set t := θ G with ht
  have hinj : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf (structureSheaf B X hX)).map t) := by
    rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} x y hxy => mem_topology_of_good hG T.unop _ fun {Y} h hb => hb.1 ?_⟩
    have hn := fun z => ConcreteCategory.congr_hom
      (((sheafToPresheaf (topology B X hX) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf (structureSheaf B X hX)).map t)).naturality h.op) z
    exact (hn x).trans ((congrArg _ hxy).trans (hn y).symm)
  have hsurj : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (structureSheaf B X hX)).map t) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact ⟨fun {T} s => mem_topology_of_good hG T _ fun {Y} h hb => hb.2 _⟩
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((SheafOfModules.toSheaf (structureSheaf B X hX)).map t)).1 ⟨hinj, hsurj⟩
  exact (isIso_iff_of_reflects_iso t (SheafOfModules.toSheaf (structureSheaf B X hX))).1 hiso

/-- **Stacks 03DX (1), essential surjectivity, `τ = fppf`.** This discharges the hypothesis of
`AlgMag.S9BP.isQCoh_iff_fppf`. -/
theorem fppf03DX (B : BigFppfSite.{u}) : AlgMag.S9BP.Fppf03DX B := fun X hX G hG =>
  ⟨(restrictModule B X hX).obj G, isQuasicoherent_restrictModule G hG,
    ⟨@asIso _ _ _ _ _ (isIso_θ hG)⟩⟩

variable {S : Scheme.{u}} {hS : B.Contains S} {Bsp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

open AlgMag.S9B AlgMag.S9 in
/-- **`IsQCoh` is the printed notion, with no hypothesis.** `IsQCoh F` if and only if `F` is a Zariski
sheaf and, over each affine `T`, it restricts to a quasi-coherent sheaf of modules on `(Sch/T)_fppf`.
-/
theorem isQCoh_iff_printed (F : PMod (OB Bsp)) :
    IsQCoh F ↔
      (∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
        coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows) ∧
      ∀ (T : SB Bsp) [IsAffine T.left], AlgMag.S9BP.IsQCohAt F T :=
  AlgMag.S9BP.isQCoh_iff_fppf (fppf03DX B) F

end AlgMag.B2

#print axioms AlgMag.B2.fppf03DX
#print axioms AlgMag.B2.isQCoh_iff_printed
