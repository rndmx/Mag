/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.CategoryTheory.Sites.Over
import AlgMag.GeneralBaseCore
import AlgMag.GeneralBaseChart

/-!
# The Zariski topology on `Over S`

Representable functors are Zariski sheaves on `Over S`, and every scheme over `S` is covered by
pieces lying over an affine open of `S`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.GB

variable {S : Scheme.{u}}

/-- Representable functors on `Over S` are sheaves for the Zariski topology. -/
theorem isSheaf_yoneda_over (Y : Over S) :
    Presieve.IsSheaf (Scheme.zariskiTopology.over S) (yoneda.obj Y) := by
  intro T R hR x hx
  have hR' : Sieve.overEquiv T R ∈ Scheme.zariskiTopology T.left := hR
  have shY : Presieve.IsSheafFor (yoneda.obj Y.left) (Sieve.overEquiv T R).arrows :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.zariskiTopology)
      (yoneda.obj Y.left) _ hR'
  have shS : Presieve.IsSheafFor (yoneda.obj S) (Sieve.overEquiv T R).arrows :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.zariskiTopology)
      (yoneda.obj S) _ hR'
  let x' : Presieve.FamilyOfElements (yoneda.obj Y.left) (Sieve.overEquiv T R).arrows :=
    fun W f hf => (x (Over.homMk f : Over.mk (f ≫ T.hom) ⟶ T)
      ((Sieve.overEquiv_iff _ _).1 hf)).left
  have hc : x'.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
    have := hx (Y₁ := Over.mk (f₁ ≫ T.hom)) (Y₂ := Over.mk (f₂ ≫ T.hom))
      (Z := Over.mk (g₁ ≫ f₁ ≫ T.hom)) (Over.homMk g₁) (Over.homMk g₂ (by
        change g₂ ≫ f₂ ≫ T.hom = g₁ ≫ f₁ ≫ T.hom
        rw [← Category.assoc, ← comm, Category.assoc])) (f₁ := Over.homMk f₁)
      (f₂ := Over.homMk f₂) ((Sieve.overEquiv_iff _ _).1 h₁) ((Sieve.overEquiv_iff _ _).1 h₂)
      (by
        refine Over.OverMorphism.ext ?_
        exact comm)
    exact congrArg (fun k : Over.mk (g₁ ≫ f₁ ≫ T.hom) ⟶ Y => k.left) this
  let t := shY.amalgamate x' hc
  have ht : ∀ {W} (f : W ⟶ T.left) (hf : (Sieve.overEquiv T R).arrows f), f ≫ t = x' f hf :=
    fun f hf => shY.valid_glue hc f hf
  have hw : t ≫ Y.hom = T.hom := by
    refine shS.isSeparatedFor.ext fun W f hf => ?_
    change f ≫ t ≫ Y.hom = f ≫ T.hom
    rw [← Category.assoc, ht f hf]
    exact Over.w (x (Over.homMk f : Over.mk (f ≫ T.hom) ⟶ T) ((Sieve.overEquiv_iff _ _).1 hf))
  refine ⟨Over.homMk t hw, ?_, ?_⟩
  · intro W f hf
    have hf' : (Sieve.overEquiv T R).arrows f.left := by
      rw [Sieve.overEquiv_iff]
      exact R.downward_closed hf (Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ W.hom = f.left ≫ T.hom
        rw [Category.id_comp, Over.w]) : Over.mk (f.left ≫ T.hom) ⟶ W)
    let c : W ⟶ Over.mk (f.left ≫ T.hom) := Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ f.left ≫ T.hom = W.hom
      rw [Category.id_comp, Over.w])
    have h1 := hx (𝟙 W) c hf ((Sieve.overEquiv_iff _ _).1 hf')
      (by
        refine Over.OverMorphism.ext ?_
        simp [c])
    refine Over.OverMorphism.ext ?_
    have h2 : f.left ≫ t = _ := ht f.left hf'
    have h3 := congrArg (fun k : W ⟶ Y => k.left) h1
    change (𝟙 W ≫ x f hf).left = (c ≫ _).left at h3
    simp only [Category.id_comp, Over.comp_left] at h3
    refine h2.trans ?_
    rw [h3]
    change _ = 𝟙 _ ≫ _
    rw [Category.id_comp]
  · intro y hy
    refine Over.OverMorphism.ext ?_
    refine shY.isSeparatedFor.ext fun W f hf => ?_
    change f ≫ y.left = f ≫ t
    rw [ht f hf]
    have := hy (Over.homMk f : Over.mk (f ≫ T.hom) ⟶ T) ((Sieve.overEquiv_iff _ _).1 hf)
    exact congrArg (fun k : Over.mk (f ≫ T.hom) ⟶ Y => k.left) this

/-- The sieve of the morphisms to `T` whose source lies over an affine open of `S`. -/
def sieveU (T : Over S) : Sieve T where
  arrows W _ := ∃ U : S.affineOpens, LiesOver W U.1
  downward_closed {W W'} f := by
    rintro ⟨U, hU⟩ g
    exact ⟨U, hU.of_hom g⟩

/-- Every scheme over `S` is covered by pieces lying over an affine open of `S`. -/
theorem sieveU_mem (T : Over S) : sieveU T ∈ Scheme.zariskiTopology.over S T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.mem_grothendieckTopology_iff.mpr ⟨S.directedAffineCover.pullback₁ T.hom, ?_⟩
  rintro W f ⟨U⟩
  rw [Sieve.overEquiv_iff]
  let U' : S.affineOpens := U
  refine ⟨U', liesOver_of_forall fun x => ?_⟩
  let x' : ↑(pullback T.hom U'.1.ι) := x
  have e : (pullback.fst T.hom U'.1.ι ≫ T.hom) x' = U'.1.ι (pullback.snd T.hom U'.1.ι x') := by
    rw [pullback.condition]
    exact Scheme.Hom.comp_apply _ _ _
  have h : (pullback.fst T.hom U'.1.ι ≫ T.hom) x' ∈ U'.1 := by
    rw [e]
    exact (pullback.snd T.hom U'.1.ι x').2
  exact h

end AlgMag.GB
