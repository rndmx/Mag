/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBFinal
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent

/-!
# §9 over an algebraic space: the hypotheses of `Sec9OverBFinal` for genuine spaces

For `p : X ⟶ Bsp` a morphism of presheaves on the big fppf site, `Vp p` is `X` as an object over `B`.

* `AlgMag.S9BS.affOverOfIsAffineHom`: `Space.IsAffineHom p` gives `AffOver (Vp p)`, so Propositions
  9.1, 9.9, 9.10 apply to an affine morphism of algebraic spaces `X → B`.
* `AlgMag.S9BS.qcCoverOfQuasiCompact`: a quasi-compact algebraic space `X` gives `QCCover (Vp p)`, so
  the literal direct sum of Proposition 9.12 applies (Tag 03H6).
* `AlgMag.S9BS.affOverHm`: `𝔸(M)_B → B` as `AffOver`, linking to Propositions 9.11-9.13 over `B`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp X : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9BS

open AlgMag.S9B AlgMag.S9BF

lemma nat_app (p : X ⟶ Bsp) {U V : (BigFppfOver Bs S hS)ᵒᵖ} (f : U ⟶ V) (x : X.obj U) :
    p.app V (X.map f x) = Bsp.map f (p.app U x) :=
  ConcreteCategory.congr_hom (p.naturality f) x

/-- `X → B` as an object over `B`: the points of `X` over a given point of `B`. -/
def Vp (p : X ⟶ Bsp) : (SB Bsp)ᵒᵖ ⥤ Type u where
  obj T := {x : X.obj (op T.unop.obj) // p.app _ x = T.unop.pt}
  map {T T'} f := ↾ fun x => ⟨X.map f.unop.hom.op x.1, by
    rw [nat_app, x.2]
    exact f.unop.w⟩
  map_id T := by
    ext1
    refine DFunLike.ext _ _ fun x => Subtype.ext ?_
    change X.map (𝟙 _ : (unop T).obj ⟶ (unop T).obj).op x.1 = x.1
    simp
  map_comp f g := by
    ext1
    refine DFunLike.ext _ _ fun x => Subtype.ext ?_
    change X.map (g.unop.hom ≫ f.unop.hom).op x.1 = X.map g.unop.hom.op (X.map f.unop.hom.op x.1)
    simp

/-- The fibre product `T ×_B X` for `T` affine, from `Space.IsAffineHom`. -/
lemma exists_fibre (p : X ⟶ Bsp) (hp : Space.IsAffineHom Bs S hS p) (T : SB Bsp)
    [hT : IsAffine T.left] :
    ∃ (W : BigFppfOver Bs S hS) (_ : IsAffine ((BigFppfOver.toScheme Bs S hS).obj W))
      (u : X.obj (op W)) (q : W ⟶ T.obj), p.app _ u = Bsp.map q.op T.pt ∧
      (∀ (W' : BigFppfOver Bs S hS) (t : W' ⟶ T.obj) (x : X.obj (op W')),
        p.app _ x = Bsp.map t.op T.pt → ∃ h : W' ⟶ W, h ≫ q = t ∧ X.map h.op u = x) ∧
      (∀ (W' : BigFppfOver Bs S hS) (h h' : W' ⟶ W), h ≫ q = h' ≫ q →
        X.map h.op u = X.map h'.op u → h = h') := by
  let g : yoneda.obj T.obj ⟶ Bsp := yonedaEquiv.symm T.pt
  obtain ⟨W, p0, q, hpb⟩ := hp ⟨T.obj, hT⟩ g
  have key : ∀ {W' : BigFppfOver Bs S hS} (t : W' ⟶ T.obj),
      yonedaEquiv (yoneda.map t ≫ g) = Bsp.map t.op T.pt := by
    intro W' t
    rw [← yonedaEquiv_naturality]
    simp [g]
  have key2 : ∀ {W' : BigFppfOver Bs S hS} (h : W' ⟶ W.obj),
      yonedaEquiv (yoneda.map h ≫ p0) = X.map h.op (yonedaEquiv p0) := by
    intro W' h
    exact (yonedaEquiv_naturality p0 h).symm
  refine ⟨W.obj, W.property, yonedaEquiv p0, q, ?_, ?_, ?_⟩
  · have h := congrArg yonedaEquiv hpb.w
    rw [key q, yonedaEquiv_comp] at h
    exact h
  · intro W' t x hx
    have hc : yonedaEquiv.symm x ≫ p = yoneda.map t ≫ g := by
      apply yonedaEquiv.injective
      rw [key t, yonedaEquiv_comp, Equiv.apply_symm_apply, hx]
    let l := hpb.lift _ _ hc
    refine ⟨yoneda.preimage l, ?_, ?_⟩
    · apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      exact hpb.lift_snd _ _ hc
    · rw [← key2, Functor.map_preimage, hpb.lift_fst, Equiv.apply_symm_apply]
  · intro W' h h' h1 h2
    apply yoneda.map_injective
    refine hpb.hom_ext ?_ ?_
    · apply yonedaEquiv.injective
      rw [key2, key2, h2]
    · rw [← Functor.map_comp, ← Functor.map_comp, h1]

/-- **`Space.IsAffineHom` to `AffOver`** (Tag 03WF): an affine morphism `X → B` has, for `T` affine
over `B`, the affine scheme `T ×_B X` required by Propositions 9.1, 9.9, 9.10 over `B`. -/
def affOverOfIsAffineHom (p : X ⟶ Bsp) (hp : Space.IsAffineHom Bs S hS p) : AffOver (Vp p) where
  P T _ := ⟨(exists_fibre p hp T).choose,
    Bsp.map (exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose.op T.pt⟩
  aff T _ := (exists_fibre p hp T).choose_spec.choose
  pr T _ := ⟨(exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose, rfl⟩
  univ T _ := ⟨(exists_fibre p hp T).choose_spec.choose_spec.choose,
    (exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.1⟩
  lift {T W} _ t x :=
    ⟨((exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.2.1 W.obj t.hom x.1
      (x.2.trans t.w.symm)).choose, by
      have h := ((exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.2.1 W.obj
        t.hom x.1 (x.2.trans t.w.symm)).choose_spec.1
      change Bsp.map _ (Bsp.map _ T.pt) = W.pt
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, h]
      exact t.w⟩
  lift_pr {T W} _ t x := SB.Hom.ext
    ((exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.2.1 W.obj t.hom x.1
      (x.2.trans t.w.symm)).choose_spec.1
  lift_univ {T W} _ t x := Subtype.ext
    ((exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.2.1 W.obj t.hom x.1
      (x.2.trans t.w.symm)).choose_spec.2
  uniq {T W} _ g g' h1 h2 := SB.Hom.ext
    ((exists_fibre p hp T).choose_spec.choose_spec.choose_spec.choose_spec.2.2 W.obj g.hom g'.hom
      (congrArg SB.Hom.hom h1) (congrArg Subtype.val h2))

/-- A surjective flat morphism of affine schemes is faithfully flat on global sections. -/
lemma faithfullyFlat_appTop {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (f : A' ⟶ A)
    [Flat f] [Surjective f] : f.appTop.hom.FaithfullyFlat := by
  have e : Spec.map f.appTop = A'.isoSpec.inv ≫ f ≫ A.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  refine (flat_and_surjective_SpecMap_iff f.appTop).1 ?_
  rw [e]
  exact ⟨inferInstance, inferInstance⟩

/-- **A quasi-compact algebraic space gives `QCCover`** (Tag 03H6): an affine étale surjective atlas
`U → X`; a point of `X` over an affine `E` lifts to `U` over an affine étale surjective `E' → E`. -/
theorem qcCoverOfQuasiCompact (p : X ⟶ Bsp) (hX : IsAlgebraicSpace Bs S hS X)
    (hq : Space.IsQuasiCompactSpace Bs S hS X) : Nonempty (QCCover (Vp p)) := by
  obtain ⟨U, f, hU, hs, he⟩ :=
    (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover Bs S hS X hX).1 hq
  have he' := Space.presheaf_etale_of_isEtale Bs S hS he
  refine ⟨⟨⟨U, p.app _ (yonedaEquiv f)⟩,
    inferInstanceAs (CompactSpace ((BigFppfOver.toScheme Bs S hS).obj U)),
    ⟨yonedaEquiv f, rfl⟩, ?_⟩⟩
  intro E hE t
  let g : yoneda.obj E.obj ⟶ X := yonedaEquiv.symm t.1
  have hr := hs.rep
  have s1 : Surjective ((BigFppfOver.toScheme Bs S hS).map (hr.snd g)) := hs.property_snd g
  have s2 : Etale ((BigFppfOver.toScheme Bs S hS).map (hr.snd g)) := he'.property_snd g
  obtain ⟨c', r, hc', hs', he'', -⟩ :=
    BigFppfOver.exists_affine_surjective_etale_refinement hE (hr.snd g) s1 s2
  haveI := hs'
  haveI := he''
  -- the point of `X` on the pullback, from the two legs
  have hpt : X.map (r ≫ hr.snd g).op t.1 = X.map (r ≫ hr.fst' g).op (yonedaEquiv f) := by
    have h1 : yoneda.map (r ≫ hr.fst' g) ≫ f = yoneda.map (r ≫ hr.snd g) ≫ g := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        hr.map_fst', hr.w g]
    have ha : X.map (r ≫ hr.snd g).op t.1 = yonedaEquiv (yoneda.map (r ≫ hr.snd g) ≫ g) := by
      rw [← yonedaEquiv_naturality]
      simp [g]
    rw [ha, yonedaEquiv_naturality, h1]
  have hptB : Bsp.map (r ≫ hr.fst' g).op (p.app _ (yonedaEquiv f)) =
      Bsp.map (r ≫ hr.snd g).op E.pt := by
    rw [← nat_app, ← hpt, nat_app, t.2]
  let W₀ : SB Bsp := ⟨U, p.app _ (yonedaEquiv f)⟩
  let E' : SB Bsp := ⟨c', Bsp.map (r ≫ hr.snd g).op E.pt⟩
  let e : E' ⟶ E := ⟨r ≫ hr.snd g, rfl⟩
  let a : E' ⟶ W₀ := ⟨r ≫ hr.fst' g, hptB⟩
  haveI : IsAffine E'.left := hc'
  haveI : Surjective (SB.Hom.left e) := hs'
  haveI : Etale (SB.Hom.left e) := he''
  have hff : ((OB Bsp).map e.op).hom.FaithfullyFlat := faithfullyFlat_appTop (SB.Hom.left e)
  exact ⟨E', hc', e, a, hff, Subtype.ext hpt.symm⟩

/-! ### `𝔸(M)_B → B` is affine -/

section AM

variable {M : Type u} [AddCommMonoid M] [Countable M]

/-- A morphism to `𝔸(M)_W` is determined by its projection to `W` and the universal point. -/
lemma Y_uniq {T W : SB Bsp} [IsAffine W.left] (g g' : T ⟶ Yobj M W)
    (h1 : g ≫ Ypr M W = g' ≫ Ypr M W)
    (h2 : APt.res g.op (univ M W) = APt.res g'.op (univ M W)) : g = g' := by
  have hφ : Yiota (N := M) W ≫ (SB.Hom.left g).appTop = Yiota (N := M) W ≫ (SB.Hom.left g').appTop := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext ?_ ?_)
    · intro r
      have hc : ∀ q : T ⟶ Yobj M W, (Yiota (N := M) W ≫ (SB.Hom.left q).appTop).hom
          (AddMonoidAlgebra.single 0 r) = (SB.Hom.left (q ≫ Ypr M W)).appTop.hom r := by
        intro q
        rw [SB.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Ypr_map,
          CommRingCat.comp_apply]
        rfl
      rw [hc, hc, h1]
    · intro m
      exact congrArg (fun a : APt (OB Bsp) M (op T) => (show Γ(T.left, ⊤) from
        a (Multiplicative.ofAdd m))) h2
  exact SB.hom_ext ((GB.homSpecEquiv T.left _).injective hφ)

/-- **`𝔸(M)_B → B` is affine**, as `AffOver`, for `M` countable: Propositions 9.1, 9.9, 9.10 of
`Sec9OverBFinal` apply to `H = 𝔸(M)_B`, the affine schemes being `T ×_B H = Spec Γ(T)[M]`. -/
def affOverHm : AffOver (Hm M Bsp ⋙ forget MonCat) where
  P T _ := Yobj M T
  aff T _ := inferInstance
  pr T _ := Ypr M T
  univ T _ := univ M T
  lift t x := classify t x
  lift_pr t x := classify_pr t x
  lift_univ t x := res_classify_univ t x
  uniq g g' h1 h2 := Y_uniq g g' h1 h2

end AM

end AlgMag.S9BS

#print axioms AlgMag.S9BS.affOverOfIsAffineHom
#print axioms AlgMag.S9BS.qcCoverOfQuasiCompact
#print axioms AlgMag.S9BS.affOverHm
