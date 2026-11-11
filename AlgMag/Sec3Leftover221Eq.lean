/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover221Rt

/-!
# Algebraic Magnetism, Proposition 2.21

`AlgMag.P221.prop221`: the category of quasi-coherent `𝔸(M)_S`-`𝒪_S`-modules is equivalent to the category
of quasi-coherent `M`-graded `𝒪_S`-modules.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgMag.P221

open AlgMag.Leftover AlgMag.S9 AlgMag.VB

open scoped Classical

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M]

section Maps

variable {F F' : S.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]

/-- A morphism of modules on `W(F)(T)`. -/
def pA (φ : F ⟶ F') (T : Over S) : (assocPMod F).obj (op T) →+ (assocPMod F').obj (op T) :=
  (((Scheme.Modules.pullback T.hom).map φ).app ⊤).hom

lemma pA_smul (φ : F ⟶ F') (T : Over S) (r : (GB.overO S).obj (op T)) (x : (assocPMod F).obj (op T)) :
    pA φ T (r • x) = r • pA φ T x :=
  Scheme.Modules.Hom.app_smul _ r x

lemma pA_map (φ : F ⟶ F') {T T' : Over S} (s : T' ⟶ T) (x : (assocPMod F).obj (op T)) :
    pA φ T' ((assocPMod F).map s.op x) = (assocPMod F').map s.op (pA φ T x) :=
  (pullbackSectionsMap_natural φ s x).symm

lemma pA_evalE (φ : F ⟶ F') {V T : Over S} (t : T ⟶ V) (a : APt (GB.overO S) M (op T))
    (z : M →₀ (assocPMod F).obj (op V)) :
    pA φ T (evalE t a z) = evalE t a (z.mapRange (pA φ V) (map_zero _)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a' b ha hb => simp only [map_add, Finsupp.mapRange_add (pA φ V).map_add, ha, hb]
  | single m f =>
    rw [Finsupp.mapRange_single, evalE_single, evalE_single, pA_smul, pA_map]

lemma eV_pA (φ : F ⟶ F') (V : S.Opens) (s : Γ(F, V)) :
    eV F' V (φ.app V s) = pA φ (TV V) (eV F V s) :=
  pullbackSectionHom_natural φ V.ι V ⊤ (top_le V) s

/-- A morphism of modules that commutes with the actions commutes with the components. -/
lemma rho_comm (A : HModule (Hm M S) (assocPMod F)) (A' : HModule (Hm M S) (assocPMod F')) (φ : F ⟶ F')
    (h : ∀ {T : Over S} (a : APt (GB.overO S) M (op T)) (x : (assocPMod F).obj (op T)),
      pA φ T (asmul A a x) = asmul A' a (pA φ T x))
    (E : Over S) [IsAffine E.left] (x : (assocPMod F).obj (op E)) (m : M) :
    (hModuleEquivDecomp (isQCoh_assocPMod F') A').comp m E (pA φ E x) =
      pA φ E ((hModuleEquivDecomp (isQCoh_assocPMod F) A).comp m E x) := by
  have e := rhoV_eq (A := A') (isQCoh_assocPMod F') (pA φ E x)
    ((rhoV A (isQCoh_assocPMod F) x).mapRange (pA φ E) (map_zero _))
    (fun {T} t a => by
      rw [← pA_evalE, ← smul_eq_evalE, h, pA_map])
  refine (compOf_affine (isQCoh_assocPMod F') A' m _).trans ?_
  rw [e, Finsupp.mapRange_apply]
  exact congrArg _ (compOf_affine (isQCoh_assocPMod F) A m x).symm

end Maps

variable (S M)

/-- A quasi-coherent `𝔸(M)_S`-`𝒪_S`-module (Definition 2.20). -/
structure QAMod where
  /-- the module -/
  F : S.Modules
  [qc : F.IsQuasicoherent]
  /-- the action -/
  A : HModule (Hm M S) (assocPMod F)

attribute [instance] QAMod.qc

/-- A quasi-coherent `M`-graded `𝒪_S`-module. -/
structure QGr where
  /-- the grading -/
  G : GrMod S M
  [hq : ∀ m, (G.P m).IsQuasicoherent]

attribute [instance] QGr.hq

variable {S M}

/-- Morphisms of `𝔸(M)_S`-`𝒪_S`-modules. -/
@[ext]
structure QAMod.Hom (X Y : QAMod S M) where
  /-- the morphism of modules -/
  φ : X.F ⟶ Y.F
  equivariant : ∀ {T : Over S} (a : APt (GB.overO S) M (op T)) (x : (assocPMod X.F).obj (op T)),
    pA φ T (asmul X.A a x) = asmul Y.A a (pA φ T x)

lemma pull_comp' {F F' F'' : S.Modules} (φ : F ⟶ F') (ψ : F' ⟶ F'') (T : Over S)
    (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map (φ ≫ ψ)).app ⊤ x =
      ((Scheme.Modules.pullback T.hom).map ψ).app ⊤ (((Scheme.Modules.pullback T.hom).map φ).app ⊤ x) := by
  rw [Functor.map_comp, comp_app_apply]

lemma pull_id {F : S.Modules} (T : Over S) (x : Γ((Scheme.Modules.pullback T.hom).obj F, ⊤)) :
    ((Scheme.Modules.pullback T.hom).map (𝟙 F)).app ⊤ x = x := by
  rw [CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
  rfl

lemma pA_comp {F F' F'' : S.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] [F''.IsQuasicoherent]
    (φ : F ⟶ F') (ψ : F' ⟶ F'') (T : Over S) (x : (assocPMod F).obj (op T)) :
    pA (φ ≫ ψ) T x = pA ψ T (pA φ T x) :=
  pull_comp' φ ψ T x

lemma pA_id {F : S.Modules} [F.IsQuasicoherent] (T : Over S) (x : (assocPMod F).obj (op T)) :
    pA (𝟙 F) T x = x :=
  pull_id T x

instance : Category (QAMod S M) where
  Hom := QAMod.Hom
  id X := ⟨𝟙 _, fun a x => by rw [pA_id, pA_id]⟩
  comp f g := ⟨f.φ ≫ g.φ, fun a x => by rw [pA_comp, pA_comp, f.equivariant, g.equivariant]⟩
  id_comp f := QAMod.Hom.ext (Category.id_comp _)
  comp_id f := QAMod.Hom.ext (Category.comp_id _)
  assoc f g h := QAMod.Hom.ext (Category.assoc _ _ _)

/-- Morphisms of graded modules are families of morphisms of the components. -/
instance : Category (QGr S M) where
  Hom X Y := ∀ m, X.G.P m ⟶ Y.G.P m
  id X m := 𝟙 _
  comp f g m := f m ≫ g m
  id_comp f := funext fun m => Category.id_comp _
  comp_id f := funext fun m => Category.comp_id _
  assoc f g h := funext fun m => Category.assoc _ _ _

section Gr

variable (G : GrMod S M)

/-- `E → E_m`. -/
def rG (m : M) : G.E ⟶ G.P m :=
  G.desc fun k => if h : k = m then eqToHom (congrArg G.P h) else 0

lemma ι_rG (m : M) : G.ι m ≫ rG G m = 𝟙 _ := by
  refine (G.ι_desc _ m).trans ?_
  rw [dif_pos rfl]
  rfl

lemma ι_mono (m : M) : Mono (G.ι m) :=
  ⟨fun a b e => by
    have := congrArg (· ≫ rG G m) e
    simpa [Category.assoc, ι_rG] using this⟩

variable [∀ m, (G.P m).IsQuasicoherent]

lemma rG_ι (m : M) : rG G m ≫ G.ι m = pr G m := by
  refine G.hom_ext fun k => ?_
  rw [← Category.assoc, rG, G.ι_desc, ι_pr]
  split_ifs with h
  · subst h; simp
  · simp

end Gr

section Comm
variable {G G' : GrMod S M} [∀ m, (G.P m).IsQuasicoherent] [∀ m, (G'.P m).IsQuasicoherent]

/-- The morphism of direct sums. -/
def sumMap (f : ∀ m, G.P m ⟶ G'.P m) : G.E ⟶ G'.E := G.desc fun m => f m ≫ G'.ι m

lemma ι_sumMap (f : ∀ m, G.P m ⟶ G'.P m) (m : M) : G.ι m ≫ sumMap f = f m ≫ G'.ι m :=
  G.ι_desc _ m

lemma sumMap_pr (f : ∀ m, G.P m ⟶ G'.P m) (m : M) : sumMap f ≫ pr G' m = pr G m ≫ sumMap f := by
  refine G.hom_ext fun k => ?_
  rw [← Category.assoc, ι_sumMap, Category.assoc, ι_pr, ← Category.assoc (G.ι k), ι_pr]
  split_ifs with h
  · exact (ι_sumMap f k).symm
  · simp

lemma asmul_gr {T : Over S} (a : APt (GB.overO S) M (op T)) (x : (assocPMod G.E).obj (op T)) :
    asmul (actionOfGr G) a x = dsmul (isQCoh_assocPMod G.E) (decompOfGr G) a x :=
  rfl

lemma comp_gr (m : M) (E : Over S) (y : (assocPMod G.E).obj (op E)) :
    (decompOfGr G).comp m E y = pA (pr G m) E y :=
  rfl

/-- A morphism commuting with the projections commutes with the actions. -/
lemma pA_actionOf {T : Over S} (φ : G.E ⟶ G'.E) (hφ : ∀ m, φ ≫ pr G' m = pr G m ≫ φ)
    (a : APt (GB.overO S) M (op T)) (x : (assocPMod G.E).obj (op T)) :
    pA φ T (asmul (actionOfGr G) a x) = asmul (actionOfGr G') a (pA φ T x) := by
  have hc : ∀ (m : M) (E : Over S) (y : (assocPMod G.E).obj (op E)),
      (decompOfGr G').comp m E (pA φ E y) = pA φ E ((decompOfGr G).comp m E y) := by
    intro m E y
    rw [comp_gr, comp_gr, ← pA_comp, ← pA_comp, hφ]
  rw [asmul_gr, asmul_gr]
  refine sep_affine (isQCoh_assocPMod G'.E) T fun E e _ => ?_
  rw [← pA_map, map_dsmul, map_dsmul, pA_evalE, ← pA_map]
  refine congrArg _ (Finsupp.ext fun m => ?_)
  rw [Finsupp.mapRange_apply]
  exact (hc m E _).symm

/-- A morphism commuting with the actions commutes with the projections. -/
lemma pr_comm (φ : G.E ⟶ G'.E)
    (h : ∀ {T : Over S} (a : APt (GB.overO S) M (op T)) (x : (assocPMod G.E).obj (op T)),
      pA φ T (asmul (actionOfGr G) a x) = asmul (actionOfGr G') a (pA φ T x)) (m : M) :
    φ ≫ pr G' m = pr G m ≫ φ := by
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis basis_aff fun V s => ?_
  haveI : IsAffine (TV (V : S.Opens)).left := V.2
  have key := rho_comm (actionOfGr G) (actionOfGr G') φ h (TV (V : S.Opens)) (eV G.E V s) m
  have e1 : hModuleEquivDecomp (isQCoh_assocPMod G.E) (actionOfGr G) = decompOfGr G :=
    (hModuleEquivDecomp (isQCoh_assocPMod G.E)).apply_symm_apply _
  have e2 : hModuleEquivDecomp (isQCoh_assocPMod G'.E) (actionOfGr G') = decompOfGr G' :=
    (hModuleEquivDecomp (isQCoh_assocPMod G'.E)).apply_symm_apply _
  rw [e1, e2] at key
  apply (eV_bijective G'.E V).1
  rw [comp_app_apply, comp_app_apply, eV_pA, eV_pA, eV_pA, eV_pA]
  exact key

lemma sumMap_recover (φ : G.E ⟶ G'.E) (hc : ∀ m, φ ≫ pr G' m = pr G m ≫ φ) :
    sumMap (fun m => G.ι m ≫ φ ≫ rG G' m) = φ := by
  refine G.hom_ext fun m => ?_
  rw [ι_sumMap, Category.assoc, Category.assoc, rG_ι, hc, ← Category.assoc, ι_pr, if_pos rfl]

end Comm

/-- **Proposition 2.21**, the functor from graded modules to `𝔸(M)_S`-`𝒪_S`-modules. -/
def grToAct : QGr S M ⥤ QAMod S M where
  obj X := { F := X.G.E, A := actionOfGr X.G }
  map {X Y} f := ⟨sumMap f, fun a x => pA_actionOf _ (sumMap_pr f) a x⟩
  map_id X := QAMod.Hom.ext (X.G.hom_ext fun m => by
    refine (ι_sumMap _ m).trans ?_
    exact (Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp {X Y Z} f g := QAMod.Hom.ext (X.G.hom_ext fun m => by
    refine (ι_sumMap _ m).trans ?_
    change (f m ≫ g m) ≫ _ = _ ≫ sumMap f ≫ sumMap g
    rw [Category.assoc, ← Category.assoc (X.G.ι m), ι_sumMap, Category.assoc, ι_sumMap])

instance : (grToAct (S := S) (M := M)).Faithful where
  map_injective {X Y} {f g} h := by
    funext m
    have := congrArg (fun k => X.G.ι m ≫ QAMod.Hom.φ k) h
    change X.G.ι m ≫ sumMap f = X.G.ι m ≫ sumMap g at this
    rw [ι_sumMap, ι_sumMap] at this
    exact (ι_mono Y.G m).right_cancellation _ _ this

instance : (grToAct (S := S) (M := M)).Full where
  map_surjective {X Y} φ :=
    ⟨fun m => X.G.ι m ≫ QAMod.Hom.φ φ ≫ rG Y.G m, QAMod.Hom.ext (sumMap_recover _
      (pr_comm _ (fun a x => QAMod.Hom.equivariant φ a x)))⟩

instance : (grToAct (S := S) (M := M)).EssSurj where
  mem_essImage X := by
    refine ⟨⟨grOfAction X.A⟩, ⟨eqToIso ?_⟩⟩
    obtain ⟨F, A⟩ := X
    exact congrArg (QAMod.mk (F := F)) (actionOfGr_grOfAction A)

instance : (grToAct (S := S) (M := M)).IsEquivalence where

/-- **Proposition 2.21.** Let `S` be a scheme. The category of quasi-coherent `𝔸(M)_S`-`𝒪_S`-modules is
equivalent to the category of quasi-coherent `M`-graded `𝒪_S`-modules. -/
def prop221 : QGr S M ≌ QAMod S M := (grToAct (S := S) (M := M)).asEquivalence

end AlgMag.P221
