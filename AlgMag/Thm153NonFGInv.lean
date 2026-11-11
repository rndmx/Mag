/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Limits
import AlgMag.Prop337General
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Lemma 1.1 of `notes/thm153-wall.md`: finite-level invariance (general directed systems)

`X` an algebraic space locally of finite presentation over `S`, `T` affine, `δ : P → Γ`. Every point of
`X` over `A(P)_T = Spec R[P]` comes from `A(δ⁻¹ Γ_α)_T` for a finitely generated subgroup `Γ_α ⊂ Γ`
(Tag 049J through `AlgMag.isLimitPreserving_of_lfp`: `R[P]` is the directed union of the `R[δ⁻¹ Γ_α]`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

universe u

namespace AlgMag.NonFGI

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

lemma mem_range_supp {R : Type u} [CommRing R] {Q : AddSubmonoid P} (x : AddMonoidAlgebra R P)
    (hx : ∀ p ∈ x.coeff.support, p ∈ Q) :
    x ∈ RingHom.range (AddMonoidAlgebra.mapDomainRingHom R Q.subtype) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Subring.sum_mem _ fun p hp => ?_
  exact ⟨AddMonoidAlgebra.single ⟨p, hx p hp⟩ (x.coeff p), by
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]⟩

/-- **Lemma 1.1, factorisation** (thm153-wall.md): a point of `X` over `A(P)_T` comes from
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
  refine ⟨⟨AddSubgroup.closure (t : Set Γ), ⟨t, rfl⟩⟩, fun y hy => mem_range_supp y fun p hp => ?_⟩
  refine AddSubgroup.subset_closure ?_
  simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion]
  exact ⟨p, ⟨y, hy, hp⟩, rfl⟩

end AlgMag.NonFGI




namespace AlgMag.NonFGGen

variable {Γ : Type u} [AddCommGroup Γ]

/-- The finitely generated subgroups of `Γ`, directed by inclusion. -/
abbrev FGSub (Γ : Type u) [AddCommGroup Γ] := {G : AddSubgroup Γ // G.FG}

instance : IsDirectedOrder (FGSub Γ) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, AddSubgroup.FG.sup a.2 b.2⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

instance : Nonempty (FGSub Γ) := ⟨⟨⊥, ⟨∅, by simp⟩⟩⟩

variable (R : Type u) [CommRing R] {P : Type u} [AddCommMonoid P]
  (Q : FGSub Γ → AddSubmonoid P) (hQ : Monotone Q)

lemma md_comp {A B C : Type u} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C] (f : A → B)
    (g : B → C) (x : AddMonoidAlgebra R A) :
    AddMonoidAlgebra.mapDomain g (AddMonoidAlgebra.mapDomain f x) =
      AddMonoidAlgebra.mapDomain (g ∘ f) x := by
  simp only [AddMonoidAlgebra.mapDomain, AddMonoidAlgebra.coeff_ofCoeff]
  rw [← Finsupp.mapDomain_comp]

lemma md_id {A : Type u} [AddCommMonoid A] (x : AddMonoidAlgebra R A) :
    AddMonoidAlgebra.mapDomain id x = x := by
  simp [AddMonoidAlgebra.mapDomain]

/-- `Γ_α ↦ R[Q Γ_α]` for a monotone family `Q` of submonoids. -/
noncomputable def ringSys : FGSub Γ ⥤ CommRingCat.{u} where
  obj G := CommRingCat.of (AddMonoidAlgebra R (Q G))
  map {G H} h := CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainRingHom R (AddSubmonoid.inclusion (hQ h.le)))
  map_id G := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    exact md_id R x
  map_comp {G H K} f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change AddMonoidAlgebra.mapDomain _ x =
      AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x)
    exact (md_comp R (AddSubmonoid.inclusion (hQ f.le)) (AddSubmonoid.inclusion (hQ g.le)) x).symm

/-- The cocone with point `R[P]`. -/
noncomputable def ringCocone : Cocone (ringSys R Q hQ) where
  pt := CommRingCat.of (AddMonoidAlgebra R P)
  ι :=
    { app G := CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R (Q G).subtype)
      naturality {G H} h := by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x) =
          AddMonoidAlgebra.mapDomain _ x
        exact md_comp R (AddSubmonoid.inclusion (hQ h.le)) (Q H).subtype x }

lemma mem_range_of_support' {Q' : AddSubmonoid P} (x : AddMonoidAlgebra R P)
    (hx : ∀ p ∈ x.coeff.support, p ∈ Q') :
    x ∈ RingHom.range (AddMonoidAlgebra.mapDomainRingHom R Q'.subtype) := by
  classical
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Subring.sum_mem _ fun p hp => ?_
  exact ⟨AddMonoidAlgebra.single ⟨p, hx p hp⟩ (x.coeff p), by
    simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]⟩

/-- `R[P]` is the filtered colimit of the `R[Q Γ_α]` when the `Q Γ_α` exhaust `P`. -/
noncomputable def ringCocone_isColimit (hcov : ∀ s : Finset P, ∃ G, ∀ p ∈ s, p ∈ Q G) :
    IsColimit (ringCocone R Q hQ) := by
  classical
  have : ReflectsColimit (ringSys R Q hQ) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y h => ?_))
  · obtain ⟨G, hG⟩ := hcov x.coeff.support
    obtain ⟨xi, hxi⟩ := mem_range_of_support' R (Q' := Q G) x hG
    exact ⟨G, xi, hxi.symm⟩
  · refine ⟨i, 𝟙 i, ?_⟩
    have hinj : Function.Injective (AddMonoidAlgebra.mapDomain (R := R) (Q i).subtype) :=
      AddMonoidAlgebra.mapDomain_injective Subtype.val_injective
    rw [hinj h]

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (hP : #P < B.cutoff)

/-- `Γ_α ↦ Spec R_T[Q Γ_α]`, a cofiltered system in the site. -/
noncomputable def siteSys : (FGSub Γ)ᵒᵖ ⥤ BigFppfOver B S hS where
  obj G := spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) (Q G.unop)))
    (NonFGI.contains_pre T hP (Q G.unop))
  map {G H} h := spMap T ((ringSys (RT T) Q hQ).map h.unop).hom (by ext; simp [ringSys])
  map_id G := by
    refine site_hom_ext ?_
    change Spec.map ((ringSys (RT T) Q hQ).map (𝟙 G.unop)) = 𝟙 _
    rw [(ringSys (RT T) Q hQ).map_id, Spec.map_id]
  map_comp {G H K} f g := by
    refine site_hom_ext ?_
    change Spec.map ((ringSys (RT T) Q hQ).map (g.unop ≫ f.unop)) =
      Spec.map ((ringSys (RT T) Q hQ).map f.unop) ≫ Spec.map ((ringSys (RT T) Q hQ).map g.unop)
    rw [(ringSys (RT T) Q hQ).map_comp, Spec.map_comp]

/-- The cone with apex `Spec R_T[P]`. -/
noncomputable def siteCone : Cone (siteSys Q hQ T hP) where
  pt := spObj T (algebraMap (RT T) (AddMonoidAlgebra (RT T) P)) (NonFGI.contains_P T hP)
  π :=
    { app G := spMap T ((ringCocone (RT T) Q hQ).ι.app G.unop).hom (by ext; simp [ringSys, ringCocone])
      naturality {G H} h := by
        refine site_hom_ext ?_
        change 𝟙 _ ≫ Spec.map ((ringCocone (RT T) Q hQ).ι.app H.unop) =
          Spec.map ((ringCocone (RT T) Q hQ).ι.app G.unop) ≫
            Spec.map ((ringSys (RT T) Q hQ).map h.unop)
        rw [Category.id_comp, ← Spec.map_comp, (ringCocone (RT T) Q hQ).w] }

variable {Q hQ}

/-- **Lemma 1.1, finite-level agreement** for an exhausting family: two points of `X` over
`Spec R_T[Q Γ_α]` which agree over `Spec R_T[P]` agree over some `Spec R_T[Q Γ_β]`, `Γ_β ⊃ Γ_α`. -/
theorem exists_fg_eq (hcov : ∀ s : Finset P, ∃ G, ∀ p ∈ s, p ∈ Q G)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {G : (FGSub Γ)ᵒᵖ}
    (x y : X.obj (op ((siteSys Q hQ T hP).obj G)))
    (h : X.map ((siteCone Q hQ T hP).π.app G).op x = X.map ((siteCone Q hQ T hP).π.app G).op y) :
    ∃ (H : (FGSub Γ)ᵒᵖ) (f : H ⟶ G),
      X.map ((siteSys Q hQ T hP).map f).op x = X.map ((siteSys Q hQ T hP).map f).op y := by
  have hL := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1 hfp
  have hlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone (siteCone Q hQ T hP)) :=
    isLimitOfPreserves Scheme.Spec (ringCocone_isColimit (RT T) Q hQ hcov).op
  obtain ⟨hcol⟩ := hL (FGSub Γ)ᵒᵖ (siteSys Q hQ T hP) (siteCone Q hQ T hP) hlim
    (fun G => inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (spObj T _ _))))
    (inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (spObj T _ _))))
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol (i := op G) x y).1 h
  exact ⟨j.unop, f.unop, hf⟩

end Site


section Action

variable {Γ P : Type u} [AddCommGroup Γ] [AddCommMonoid P] (δ : P →+ Γ)

/-- `W_α = A(δ⁻¹ Γ_α)`: the family `δ⁻¹ Γ_α`. -/
abbrev Q₁ (G : FGSub Γ) : AddSubmonoid P := G.1.toAddSubmonoid.comap δ

/-- `D(Γ_α) × W_α = A(Γ_α × δ⁻¹ Γ_α)`. -/
abbrev Q₂ (G : FGSub Γ) : AddSubmonoid (Γ × P) := G.1.toAddSubmonoid.prod (Q₁ δ G)

lemma Q₁_mono : Monotone (Q₁ δ) := fun _ _ h _ hx => h hx

lemma Q₂_mono : Monotone (Q₂ δ) := fun _ _ h _ hx => ⟨h hx.1, h hx.2⟩

lemma Q₁_cov (s : Finset P) : ∃ G, ∀ p ∈ s, p ∈ Q₁ δ G := by
  classical
  refine ⟨⟨AddSubgroup.closure ((s.image δ : Finset Γ) : Set Γ), ⟨_, rfl⟩⟩, fun p hp => ?_⟩
  exact AddSubgroup.subset_closure (by simp; exact ⟨p, hp, rfl⟩)

lemma Q₂_cov (s : Finset (Γ × P)) : ∃ G, ∀ p ∈ s, p ∈ Q₂ δ G := by
  classical
  let t : Finset Γ := s.image Prod.fst ∪ s.image (fun q => δ q.2)
  refine ⟨⟨AddSubgroup.closure (t : Set Γ), ⟨t, rfl⟩⟩, fun p hp => ⟨?_, ?_⟩⟩
  · exact AddSubgroup.subset_closure (by simp [t]; exact Or.inl ⟨p.2, hp⟩)
  · exact AddSubgroup.subset_closure (by simp [t]; exact Or.inr ⟨p.1, p.2, hp, rfl⟩)

/-- The coaction `p ↦ (δ p, p)` at level `Γ_α`. -/
def actHom (G : FGSub Γ) : Q₁ δ G →+ Q₂ δ G where
  toFun p := ⟨(δ p, p), p.2, p.2⟩
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

/-- The projection `p ↦ (0, p)` at level `Γ_α`. -/
def prHom (G : FGSub Γ) : Q₁ δ G →+ Q₂ δ G where
  toFun p := ⟨(0, p), G.1.zero_mem, p.2⟩
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (hP : #P < B.cutoff)

variable (hΓP : #(Γ × P) < B.cutoff)

/-- The action `D(Γ_α) × W_α → W_α` in the site. -/
noncomputable def aMap (G : (FGSub Γ)ᵒᵖ) :
    (siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).obj G ⟶ (siteSys (Q₁ δ) (Q₁_mono δ) T hP).obj G :=
  spMap T (AddMonoidAlgebra.mapDomainRingHom (RT T) (actHom δ G.unop)) (by ext; simp)

/-- The projection `D(Γ_α) × W_α → W_α` in the site. -/
noncomputable def pMap (G : (FGSub Γ)ᵒᵖ) :
    (siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).obj G ⟶ (siteSys (Q₁ δ) (Q₁_mono δ) T hP).obj G :=
  spMap T (AddMonoidAlgebra.mapDomainRingHom (RT T) (prHom δ G.unop)) (by ext; simp)

/-- **Lemma 1.1, finite-level invariance** (thm153-wall.md): if `F_α ∈ X(W_α)` is invariant after
`D(Γ) × W → D(Γ_α) × W_α`, it is invariant after `D(Γ_β) × W_β → D(Γ_α) × W_α` for some
finitely generated `Γ_β ⊃ Γ_α`. -/
theorem exists_fg_inv {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) {G : (FGSub Γ)ᵒᵖ}
    (x : X.obj (op ((siteSys (Q₁ δ) (Q₁_mono δ) T hP).obj G)))
    (h : X.map ((siteCone (Q₂ δ) (Q₂_mono δ) T hΓP).π.app G ≫ aMap δ T hP hΓP G).op x =
      X.map ((siteCone (Q₂ δ) (Q₂_mono δ) T hΓP).π.app G ≫ pMap δ T hP hΓP G).op x) :
    ∃ (H : (FGSub Γ)ᵒᵖ) (f : H ⟶ G),
      X.map ((siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).map f ≫ aMap δ T hP hΓP G).op x =
        X.map ((siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).map f ≫ pMap δ T hP hΓP G).op x := by
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at h
  obtain ⟨H, f, hf⟩ := exists_fg_eq T hΓP (Q₂_cov δ) hX hfp _ _ h
  refine ⟨H, f, ?_⟩
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact hf

/-- Naturality of the action maps: `F_β := F_α ∘ (W_β → W_α)` is invariant at level `β` when
`F_α` is invariant after `D(Γ_β) × W_β → D(Γ_α) × W_α`. -/
lemma aMap_nat {G H : (FGSub Γ)ᵒᵖ} (f : H ⟶ G) :
    (siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).map f ≫ aMap δ T hP hΓP G =
      aMap δ T hP hΓP H ≫ (siteSys (Q₁ δ) (Q₁_mono δ) T hP).map f := by
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x) =
    AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x)
  rw [md_comp, md_comp]
  rfl

lemma pMap_nat {G H : (FGSub Γ)ᵒᵖ} (f : H ⟶ G) :
    (siteSys (Q₂ δ) (Q₂_mono δ) T hΓP).map f ≫ pMap δ T hP hΓP G =
      pMap δ T hP hΓP H ≫ (siteSys (Q₁ δ) (Q₁_mono δ) T hP).map f := by
  refine site_hom_ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x) =
    AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.mapDomain _ x)
  rw [md_comp, md_comp]
  rfl

end Action

end AlgMag.NonFGGen

#print axioms AlgMag.NonFGGen.exists_fg_inv
#print axioms AlgMag.NonFGGen.aMap_nat
#print axioms AlgMag.NonFGGen.pMap_nat

#print axioms AlgMag.NonFGGen.exists_fg_eq
