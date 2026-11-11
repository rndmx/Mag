/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Limits
import AlgMag.Prop337General
import AlgMag.Thm153NonFGLimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Ring-level and site-level limits for `A(P)`, `P` not finitely generated

`X` an algebraic space locally of finite presentation over `S`, `T` affine, `δ : P → Γ`. Every point of
`X` over `A(P)_T = Spec R[P]` comes from `A(δ⁻¹ Γ_α)_T` for a finitely generated subgroup `Γ_α ⊂ Γ`
(Tag 049J through `AlgMag.isLimitPreserving_of_lfp`: `R[P]` is the directed union of the `R[δ⁻¹ Γ_α]`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.NonFG

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {Γ P : Type u} [AddCommGroup Γ] [AddCommMonoid P] (δ : P →+ Γ)

/-- `δ⁻¹ G`. -/
abbrev pre (G : {G : AddSubgroup Γ // G.FG}) : AddSubmonoid P := G.1.toAddSubmonoid.comap δ

lemma contains_pre (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (hP : #P < B.cutoff)
    (Q : AddSubmonoid P) : B.Contains (Spec (.of (AddMonoidAlgebra (RT T) Q))) :=
  P337.contains_alg ((mk_le_of_injective Subtype.val_injective).trans_lt hP) (contains_RT T)

lemma contains_P (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (hP : #P < B.cutoff) :
    B.Contains (Spec (.of (AddMonoidAlgebra (RT T) P))) :=
  P337.contains_alg hP (contains_RT T)

/-- A point of `X` over `A(P)_T` comes from
`A(δ⁻¹ Γ_α)_T`, `Γ_α` finitely generated. -/
theorem exists_fg_factor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X))
    (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (hP : #P < B.cutoff)
    (x : X.obj (op (spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) P)) (contains_P T hP)))) :
    ∃ (G : {G : AddSubgroup Γ // G.FG})
      (xG : X.obj (op (spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) (pre δ G)))
        (contains_pre T hP (pre δ G))))),
      X.map (spMap T (hC := contains_pre T hP (pre δ G)) (hC' := contains_P T hP)
        (AddMonoidAlgebra.mapDomainRingHom (RT T) (pre δ G).subtype)
        (by ext; simp)).op xG = x := by
  classical
  have hL := isLimitPreserving_of_lfp hX hfp
  refine hL T (fun G : {G : AddSubgroup Γ // G.FG} => AddMonoidAlgebra (RT T) (pre δ G))
    (fun G => algebraMap _ _) (fun G => contains_pre T hP (pre δ G))
    (fun G => AddMonoidAlgebra.mapDomainRingHom (RT T) (pre δ G).subtype) (fun G => by ext; simp)
    (fun G => AddMonoidAlgebra.mapDomain_injective Subtype.val_injective) (fun s => ?_) x
  let t : Finset Γ := (s.biUnion fun y => y.coeff.support).image δ
  refine ⟨⟨AddSubgroup.closure (t : Set Γ), ⟨t, rfl⟩⟩, fun y hy => mem_range_of_support' _ y fun p hp => ?_⟩
  refine AddSubgroup.subset_closure ?_
  simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion]
  exact ⟨p, ⟨y, hy, hp⟩, rfl⟩

end AlgMag.NonFG

namespace AlgMag.NonFGSite

open AlgMag.NonFG

variable {Γ : Type u} [AddCommGroup Γ] {P : Type u} [AddCommMonoid P] (δ : P →+ Γ)

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (hP : #P < B.cutoff)

/-- `Γ_α ↦ A(δ⁻¹ Γ_α)_T`, a cofiltered system in the site. -/
noncomputable def siteSys : (FGSub Γ)ᵒᵖ ⥤ BigFppfOver B S hS where
  obj G := spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) (preim δ G.unop)))
    (NonFG.contains_pre T hP (preim δ G.unop))
  map {G H} h := spMap T ((ringSys (RT T) δ).map h.unop).hom (by ext; simp [ringSys])
  map_id G := by
    refine site_hom_ext ?_
    change Spec.map ((ringSys (RT T) δ).map (𝟙 G.unop)) = 𝟙 _
    rw [(ringSys (RT T) δ).map_id, Spec.map_id]
  map_comp {G H K} f g := by
    refine site_hom_ext ?_
    change Spec.map ((ringSys (RT T) δ).map (g.unop ≫ f.unop)) =
      Spec.map ((ringSys (RT T) δ).map f.unop) ≫ Spec.map ((ringSys (RT T) δ).map g.unop)
    rw [(ringSys (RT T) δ).map_comp, Spec.map_comp]

/-- The cone with apex `A(P)_T`. -/
noncomputable def siteCone : Cone (siteSys δ T hP) where
  pt := spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) P)) (NonFG.contains_P T hP)
  π :=
    { app G := spMap T ((ringCocone (RT T) δ).ι.app G.unop).hom (by ext; simp [ringSys, ringCocone])
      naturality {G H} h := by
        refine site_hom_ext ?_
        change 𝟙 _ ≫ Spec.map ((ringCocone (RT T) δ).ι.app H.unop) =
          Spec.map ((ringCocone (RT T) δ).ι.app G.unop) ≫ Spec.map ((ringSys (RT T) δ).map h.unop)
        rw [Category.id_comp, ← Spec.map_comp, (ringCocone (RT T) δ).w] }

/-- The image of `siteCone` in schemes is a limit. -/
noncomputable def siteCone_isLimit : IsLimit ((BigFppfOver.toScheme B S hS).mapCone (siteCone δ T hP)) :=
  specCone_isLimit (RT T) δ

/-- Two (injectivity half of Stacks Tag 01ZC, via Tag 05N0) points
of `X` over `A(δ⁻¹ Γ_α)_T` which agree over `A(P)_T` agree over `A(δ⁻¹ Γ_β)_T` for some
finitely generated `Γ_β ⊃ Γ_α`. -/
theorem exists_fg_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {G : (FGSub Γ)ᵒᵖ}
    (x y : X.obj (op ((siteSys δ T hP).obj G)))
    (h : X.map ((siteCone δ T hP).π.app G).op x = X.map ((siteCone δ T hP).π.app G).op y) :
    ∃ (H : (FGSub Γ)ᵒᵖ) (f : H ⟶ G),
      X.map ((siteSys δ T hP).map f).op x = X.map ((siteSys δ T hP).map f).op y := by
  have hL := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1 hfp
  obtain ⟨hcol⟩ := hL (FGSub Γ)ᵒᵖ (siteSys δ T hP) (siteCone δ T hP) (siteCone_isLimit δ T hP)
    (fun G => inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (spObj T _ _))))
    (inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (spObj T _ _))))
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol (i := op G) x y).1 h
  exact ⟨j.unop, f.unop, hf⟩

end Site

end AlgMag.NonFGSite

#print axioms AlgMag.NonFG.exists_fg_factor
#print axioms AlgMag.NonFGSite.siteCone_isLimit
#print axioms AlgMag.NonFGSite.exists_fg_eq
