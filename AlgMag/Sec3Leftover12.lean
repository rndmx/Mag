/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover328

/-!
# Algebraic Magnetism, Example 1.2 over an arbitrary scheme

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026). `V = 𝔸^ι_S = V(𝒪_S^{(ι)})`, the coordinate `i`
of weight `w i`. Then `V^N(T)` is the set of vectors of `Γ(T, 𝒪_T)^ι` supported on coordinates of weight in
`N`: that is `V^N = ⨁_{n ∈ N} V_n`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

/-- `𝒪_S`. -/
abbrev oS (S : Scheme.{u}) : S.Modules := SheafOfModules.unit S.ringCatSheaf

/-- A morphism `𝒪_S → p_* 𝒪_T` is a global function on `T`. -/
def unitHom (T : Over S) : (oS S ⟶ pO T) ≃ Γ(T.left, ⊤) :=
  (SheafOfModules.unitHomEquiv _).trans
    { toFun := fun s => s.val (op ⊤)
      invFun := fun c =>
        { val := fun U => (T.left.presheaf.map (homOfLE le_top).op).hom c
          property := fun {U V} f => by
            change (T.left.presheaf.map _).hom ((T.left.presheaf.map _).hom c) =
              (T.left.presheaf.map _).hom c
            rw [← CommRingCat.comp_apply, ← Functor.map_comp]
            rfl }
      left_inv := fun s => by
        apply Subtype.ext
        funext U
        exact s.property (homOfLE (le_top : U.unop ≤ ⊤)).op
      right_inv := fun c => by
        change (T.left.presheaf.map (𝟙 (op (⊤ : T.left.Opens)))).hom c = c
        simp }

open scoped Classical

variable {ι : Type u} (w : ι → M)

/-- The component `(𝒪_S^{(ι)})_m = ⨁_{w i = m} 𝒪_S`. -/
def wP (S : Scheme.{u}) (m : M) : S.Modules := ∐ fun _ : {i // w i = m} => oS S

/-- `𝒪_S^{(ι)}` with the grading attached to the weights `w`. -/
def wG (S : Scheme.{u}) : GrMod S M where
  E := ∐ fun m => wP w S m
  P := wP w S
  ι := Sigma.ι _
  isColimit := coproductIsCoproduct _

variable (N : AddSubmonoid M) (T : Over S)

/-- The coordinate `i` of `(𝒪_S^{(ι)})_N`, `w i ∈ N`. -/
def coord (i : ι) (h : w i ∈ N) : oS S ⟶ (wG w S).EN N :=
  Sigma.ι (fun _ : {j // w j = w i} => oS S) ⟨i, rfl⟩ ≫ (wG w S).ιN N ⟨w i, h⟩

variable {w N T}

/-- The component at `n` of the morphism attached to a vector. -/
def dscIn (v : ι → Γ(T.left, ⊤)) (n : N) : (wG w S).P n ⟶ pO T :=
  (Sigma.desc fun i : {j // w j = n.1} => (unitHom T).symm (v i.1) : wP w S n.1 ⟶ pO T)

/-- The morphism `(𝒪_S^{(ι)})_N → p_* 𝒪_T` attached to a vector. -/
def dsc (v : ι → Γ(T.left, ⊤)) : (wG w S).EN N ⟶ pO T :=
  Sigma.desc fun n : N => dscIn v n

lemma ιN_dsc (v : ι → Γ(T.left, ⊤)) (n : N) : (wG w S).ιN N n ≫ dsc v = dscIn v n :=
  Sigma.ι_desc _ _

lemma ι_dscIn (v : ι → Γ(T.left, ⊤)) (n : N) (i : {j // w j = n.1}) :
    Sigma.ι (fun _ : {j // w j = n.1} => oS S) i ≫ dscIn v n = (unitHom T).symm (v i.1) :=
  Sigma.ι_desc _ _

lemma coord_dsc (v : ι → Γ(T.left, ⊤)) (i : ι) (h : w i ∈ N) :
    coord w N i h ≫ dsc v = (unitHom T).symm (v i) := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg _ (ιN_dsc v _)).trans ?_
  exact ι_dscIn v ⟨w i, h⟩ ⟨i, rfl⟩

lemma EN_hom_ext {f g : (wG w S).EN N ⟶ pO T}
    (h : ∀ i (hi : w i ∈ N), coord w N i hi ≫ f = coord w N i hi ≫ g) : f = g := by
  refine GrMod.EN_ext _ _ fun ⟨n, hn⟩ => ?_
  refine Sigma.hom_ext _ _ fun x => ?_
  obtain ⟨i, hi⟩ := x
  obtain rfl : w i = n := hi
  exact (Category.assoc _ _ _).symm.trans ((h i hn).trans (Category.assoc _ _ _))

variable (w N T)

/-- Morphisms `(𝒪_S^{(ι)})_N → p_* 𝒪_T` are vectors supported on the coordinates of weight in `N`. -/
def homENEquiv : ((wG w S).EN N ⟶ pO T) ≃ {v : ι → Γ(T.left, ⊤) // ∀ i, w i ∉ N → v i = 0} where
  toFun l := ⟨fun i => if h : w i ∈ N then unitHom T (coord w N i h ≫ l) else 0,
    fun i h => by simp [h]⟩
  invFun v := dsc v.1
  left_inv l := by
    refine EN_hom_ext fun i hi => ?_
    rw [coord_dsc]
    simp [hi]
  right_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : w i ∈ N
    · simp [h, coord_dsc]
    · simp only [h, dite_false]
      exact (v.2 i h).symm

/-- **Example 1.2.** `V = 𝔸^ι_S` over an arbitrary scheme `S`, the coordinates having weights `w`:
`V^N(T)` is the set of vectors of `Γ(T, 𝒪_T)^ι` supported on the coordinates of weight in `N`, that is
`V^N = ⨁_{n ∈ N} V_n`. -/
def ex12_general :
    AttractorPt (vAction (wG w S)) N T ≃ {v : ι → Γ(T.left, ⊤) // ∀ i, w i ∉ N → v i = 0} :=
  (vAttractorEquiv (wG w S) N T).trans (homENEquiv w N T)

end AlgMag.VB
