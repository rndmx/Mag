/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3LeftoverPts

/-!
# Algebraic Magnetism, Proposition 3.28: the action of `𝔸(M)_S` on `V(E)`

An `M`-graded `𝒪_S`-module is `E = ⨁_m E_m` in `S.Modules`. On `V(E)(T) = Hom_{𝒪_S}(E, p_* 𝒪_T)` the
monoid `𝔸(M)(T)` acts by multiplying the component `E_m → p_* 𝒪_T` by `h(m)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

variable (S : Scheme.{u}) (M : Type u) [AddCommMonoid M]

/-- An `M`-graded `𝒪_S`-module: `E = ⨁_{m ∈ M} E_m` in the category of `𝒪_S`-modules. -/
structure GrMod where
  /-- The module `E`. -/
  E : S.Modules
  /-- The component `E_m`. -/
  P : M → S.Modules
  /-- The inclusion `E_m → E`. -/
  ι : ∀ m, P m ⟶ E
  /-- `E` is the direct sum of the `E_m`. -/
  isColimit : IsColimit (Cofan.mk E ι)

variable {S M}
variable (G : GrMod S M)

lemma GrMod.hom_ext {Q : S.Modules} {f g : G.E ⟶ Q} (h : ∀ m, G.ι m ≫ f = G.ι m ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext G.isColimit _ _ h

/-- A morphism out of `E` from its components. -/
def GrMod.desc {Q : S.Modules} (c : ∀ m, G.P m ⟶ Q) : G.E ⟶ Q :=
  Cofan.IsColimit.desc G.isColimit c

@[reassoc (attr := simp)]
lemma GrMod.ι_desc {Q : S.Modules} (c : ∀ m, G.P m ⟶ Q) (m : M) : G.ι m ≫ G.desc c = c m :=
  Cofan.IsColimit.fac G.isColimit c m

/-- The functor of points `T ↦ Hom_{𝒪_S}(E, p_* 𝒪_T)` of `V(E)` (Stacks 01M2). -/
def VF (E : S.Modules) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := E ⟶ pO T.unop
  map f := ↾ fun ξ => ξ ≫ resO f.unop
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun ξ => ?_
    change ξ ≫ resO (𝟙 _) = ξ
    rw [resO_id, Category.comp_id]
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun ξ => ?_
    change ξ ≫ resO (g.unop ≫ f.unop) = (ξ ≫ resO f.unop) ≫ resO g.unop
    rw [resO_comp, Category.assoc]

/-- The linear action of `h ∈ 𝔸(M)(T)`: multiply the component `E_m` by `h(m)`. -/
def vSmul {T : Over S} (h : APt (overO S) M (op T)) (ξ : G.E ⟶ pO T) : G.E ⟶ pO T :=
  G.desc fun m => G.ι m ≫ ξ ≫ mulO T (h (Multiplicative.ofAdd m))

@[reassoc]
lemma ι_vSmul {T : Over S} (h : APt (overO S) M (op T)) (ξ : G.E ⟶ pO T) (m : M) :
    G.ι m ≫ vSmul G h ξ = G.ι m ≫ ξ ≫ mulO T (h (Multiplicative.ofAdd m)) :=
  G.ι_desc _ m

lemma vSmul_one {T : Over S} (ξ : G.E ⟶ pO T) : vSmul G (1 : APt (overO S) M (op T)) ξ = ξ := by
  refine G.hom_ext fun m => ?_
  refine (ι_vSmul G 1 ξ m).trans ?_
  change G.ι m ≫ ξ ≫ mulO T 1 = _
  rw [mulO_one, Category.comp_id]

lemma vSmul_mul {T : Over S} (g h : APt (overO S) M (op T)) (ξ : G.E ⟶ pO T) :
    vSmul G (g * h) ξ = vSmul G g (vSmul G h ξ) := by
  refine G.hom_ext fun m => ?_
  rw [ι_vSmul, ι_vSmul, ι_vSmul_assoc]
  exact congrArg (fun k => G.ι m ≫ ξ ≫ k)
    (mulO_mul T (g (Multiplicative.ofAdd m)) (h (Multiplicative.ofAdd m)))

lemma vSmul_res {T T' : Over S} (f : T' ⟶ T) (h : APt (overO S) M (op T)) (ξ : G.E ⟶ pO T) :
    vSmul G h ξ ≫ resO f = vSmul G (APt.res f.op h) (ξ ≫ resO f) := by
  refine G.hom_ext fun m => ?_
  rw [ι_vSmul_assoc, ι_vSmul]
  simp only [Category.assoc]
  congr 2
  exact mulO_resO f _

/-- **Proposition 3.28**, first assertion: `𝔸(M)_S` acts linearly on `V(E)`. -/
def vAction : AAction (overO S) M (VF G.E) where
  smul {U} h ξ := vSmul G (T := unop U) h ξ
  one_smul {U} ξ := vSmul_one G (T := unop U) ξ
  mul_smul {U} g h ξ := vSmul_mul G (T := unop U) g h ξ
  map_smul {U V} f h ξ := vSmul_res G (T := unop U) (T' := unop V) f.unop h ξ

end AlgMag.VB
