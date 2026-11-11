/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartActionGrading
import AlgMag.ChartGraded

/-!
# Equivariant maps and graded ring maps; the corrected chart statement; the tower of §2

* `AlgMag.ChartLemmaStatementFG`: the chart lemma with the hypothesis `AddMonoid.FG M`, which
  `AlgMag.ChartLemmaStatement` omits although its docstring and the chart-lemma proof have it.
* `AlgMag.ChartMain.equivariant_iff`: a map of affine objects with `D(M)`-action is equivariant iff
  it is a graded ring map.
* `AlgMag.ChartMain.OrbitTower.toThickeningSystem`: the inverse system of §2 from a tower of affine
  equivariant thickenings.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry DirectSum

universe u

namespace AlgMag

/-- **The chart lemma** with `M` finitely generated (chart-lemma proof, Theorem). -/
def ChartLemmaStatementFG (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (M : Type u)
    [AddCommGroup M] : Prop :=
  AddMonoid.FG M → ChartLemmaStatement B S hS M

namespace ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {U V : BigFppfOver B S hS}
variable [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (actU : AAction (fppfO B S hS) M (yoneda.obj U)) (actV : AAction (fppfO B S hS) M (yoneda.obj V))

omit [AddMonoid.FG M] hU hV in
lemma smulAt_comp_of_equivariant {f : U ⟶ V}
    (hf : IsEquivariant actU actV (yoneda.map f)) {T : BigFppfOver B S hS}
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) :
    smulAt actU h t ≫ f = smulAt actV h (t ≫ f) :=
  hf (T := op T) h t

/-- An equivariant map preserves degrees. -/
theorem map_mem_homog {f : U ⟶ V} (hf : IsEquivariant actU actV (yoneda.map f)) {d : M}
    {a : RT V} (ha : a ∈ homog actV d) :
    ((SCH).map f).appTop.hom a ∈ homog actU d := by
  change coact actU _ = _
  apply (spSec_bijective U (ι1 U (M := M)) contains1).1
  rw [spSec_coact]
  have e : (SCH).map (univMap actU) ≫ (SCH).map f =
      (SCH).map (smulAt actV univPt1 (spToT U (ι1 U (M := M)) contains1 ≫ f)) := by
    rw [← Functor.map_comp]
    exact congrArg _ (smulAt_comp_of_equivariant actU actV hf _ _)
  have e₂ := congrArg (fun z => z.appTop.hom a) e
  simp only [Scheme.Hom.comp_appTop] at e₂
  refine e₂.trans ?_
  rw [appTop_smul_of_mem actV _ _ ha, Functor.map_comp, Scheme.Hom.comp_appTop]
  change ((SCH).map (spToT U (ι1 U (M := M)) contains1)).appTop.hom _ * spSec U _ _ _ = _
  rw [spToT_appTop, ← map_mul]
  congr 1
  change AddMonoidAlgebra.single 0 _ * AddMonoidAlgebra.single d 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rfl

lemma smulAt_comp_of_map_mem [DecidableEq M] {f : U ⟶ V}
    (hf : ∀ d, ∀ a ∈ homog actV d, ((SCH).map f).appTop.hom a ∈ homog actU d)
    {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ U) :
    smulAt actU h t ≫ f = smulAt actV h (t ≫ f) := by
  let _ := gradedRingOfAction actV
  refine siteExt (toAffine_ext (ringHom_ext_homogeneous (homog actV) fun d a ha => ?_))
  rw [appTop_smul_of_mem actV _ _ ha, Functor.map_comp, Scheme.Hom.comp_appTop, Functor.map_comp,
    Scheme.Hom.comp_appTop]
  exact appTop_smul_of_mem actU _ _ (hf d a ha)

/-- A graded ring map is equivariant. -/
theorem equivariant_of_map_mem [DecidableEq M] {f : U ⟶ V}
    (hf : ∀ d, ∀ a ∈ homog actV d, ((SCH).map f).appTop.hom a ∈ homog actU d) :
    IsEquivariant actU actV (yoneda.map f) :=
  fun {T} h t => smulAt_comp_of_map_mem actU actV hf (T := T.unop) h t

/-- **Bridge**: a map of affine objects with action is equivariant iff it preserves degrees. -/
theorem equivariant_iff [DecidableEq M] {f : U ⟶ V} :
    IsEquivariant actU actV (yoneda.map f) ↔
      ∀ d, ∀ a ∈ homog actV d, ((SCH).map f).appTop.hom a ∈ homog actU d :=
  ⟨fun hf _ _ ha => map_mem_homog actU actV hf ha, equivariant_of_map_mem actU actV⟩

end ChartMain

namespace ChartMain

section Tower

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-- A graded map commutes with components. -/
lemma decompose_map {A A' : Type*} [CommRing A] [CommRing A'] (𝒜 : M → AddSubgroup A)
    (𝒜' : M → AddSubgroup A') [GradedRing 𝒜] [GradedRing 𝒜'] (f : A →+* A')
    (hf : ∀ d, ∀ a ∈ 𝒜 d, f a ∈ 𝒜' d) (r : A) (e : M) :
    (decompose 𝒜' (f r) e : A') = f (decompose 𝒜 r e : A) := by
  induction r using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [decompose_coe, decompose_of_mem 𝒜' (hf i _ a.2)]
    by_cases h : i = e
    · subst h; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]; simp
  | add a b ha hb => simp [map_add, decompose_add, ha, hb]

/-- The kernel of a graded map is homogeneous. -/
lemma ker_isHomogeneous {A A' : Type*} [CommRing A] [CommRing A'] (𝒜 : M → AddSubgroup A)
    (𝒜' : M → AddSubgroup A') [GradedRing 𝒜] [GradedRing 𝒜'] (f : A →+* A')
    (hf : ∀ d, ∀ a ∈ 𝒜 d, f a ∈ 𝒜' d) : (RingHom.ker f).IsHomogeneous 𝒜 := by
  intro e r hr
  rw [RingHom.mem_ker] at hr ⊢
  rw [← decompose_map 𝒜 𝒜' f hf, hr]
  simp

/-- The rings of a tower of equivariant thickenings of the orbit (`O_n = Γ(X_n)`, §2): each
`O_{n+1} → O_n` is a graded surjection with kernel the `(n+1)`-st power of the ideal `I_{n+1}` of
`O_0`, and `I_{n+1}^{n+2} = 0`. -/
structure OrbitTower (M : Type*) [AddCommGroup M] [DecidableEq M] where
  /-- `O_n` -/
  O : ℕ → Type*
  [ring : ∀ n, CommRing (O n)]
  /-- the grading -/
  𝒜 : ∀ n, M → AddSubgroup (O n)
  [gr : ∀ n, GradedRing (𝒜 n)]
  /-- transition maps -/
  π : ∀ n, O (n + 1) →+* O n
  π_mem : ∀ n d y, y ∈ 𝒜 (n + 1) d → π n y ∈ 𝒜 n d
  π_surj : ∀ n, Function.Surjective (π n)
  /-- the map to the orbit -/
  toO : ∀ n, O n →+* O 0
  toO_zero : toO 0 = RingHom.id _
  toO_succ : ∀ n, toO (n + 1) = (toO n).comp (π n)
  nil : ∀ n, RingHom.ker (toO n) ^ (n + 1) = ⊥
  ker_π : ∀ n, RingHom.ker (π n) = RingHom.ker (toO (n + 1)) ^ (n + 1)
  I_fg : (RingHom.ker (toO 1)).FG

attribute [instance] OrbitTower.ring OrbitTower.gr

namespace OrbitTower

variable (Y : OrbitTower M)

lemma toO_mem (n : ℕ) : ∀ d y, y ∈ Y.𝒜 n d → Y.toO n y ∈ Y.𝒜 0 d := by
  induction n with
  | zero => intro d y hy; rw [Y.toO_zero]; exact hy
  | succ n ih =>
    intro d y hy
    rw [Y.toO_succ]
    exact ih d _ (Y.π_mem n d y hy)

lemma toO_surj (n : ℕ) : Function.Surjective (Y.toO n) := by
  induction n with
  | zero => rw [Y.toO_zero]; exact Function.surjective_id
  | succ n ih => rw [Y.toO_succ]; exact ih.comp (Y.π_surj n)

/-- **§2**: the `ThickeningSystem` of a tower. -/
def toThickeningSystem : ChartGraded.ThickeningSystem M where
  O := Y.O
  𝒜 := Y.𝒜
  π := Y.π
  π_mem := Y.π_mem
  π_surj := Y.π_surj
  I n := RingHom.ker (Y.toO n)
  I_hom n := ker_isHomogeneous _ _ _ (Y.toO_mem n)
  I_zero := by
    rw [Y.toO_zero]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  I_nil := Y.nil
  I_map n := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [RingHom.mem_ker, Y.toO_succ] at hy
      exact hy
    · intro y hy
      obtain ⟨z, rfl⟩ := Y.π_surj n y
      refine Ideal.mem_map_of_mem _ ?_
      rw [RingHom.mem_ker, Y.toO_succ]
      exact hy
  ker_π := Y.ker_π
  I_fg := Y.I_fg

end OrbitTower

end Tower

end ChartMain

end AlgMag

#print axioms AlgMag.ChartMain.equivariant_iff
#print axioms AlgMag.ChartMain.OrbitTower.toThickeningSystem
