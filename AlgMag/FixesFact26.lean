/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3Leftover2D

/-!
# Algebraic Magnetism, Fact 2.6 (i): the quasi-coherent bialgebra of `𝔸(N)_S` is `𝒪_S[N]`

Definition 2.3 (ii): `𝒪_S[N]` is the sheafification of the presheaf `U ↦ 𝒪_S(U)[N]`. Here, with
`q : 𝔸(N)_S → S`:

* `AlgMag.GB.cmp`: the morphism of presheaves of rings `𝒪_S(-)[N] → q_* 𝒪`, `X^n ↦ X^n`.
* `AlgMag.GB.fact26_i_sheafification`: `q_* 𝒪` is a sheaf and `cmp` is locally injective and locally
  surjective, so `q_* 𝒪` is the sheafification `𝒪_S[N]`; `cmp` is bijective on affine opens.
* `AlgMag.GB.fact26_i_comul`, `fact26_i_counit`: on every open `U`, `cmp` carries the comultiplication and
  the counit of `𝒪_S(U)[N]` to the multiplication and the unit of the monoid scheme `𝔸(N)_S`.
* `AlgMag.GB.fact26_i_tensor_bijective`: for `U` affine,
  `𝒪_S(U)[N] ⊗ 𝒪_S(U)[N] → Γ(𝔸(N)_S ×_S 𝔸(N)_S, -)` is bijective.

The printed proof goes through `Spec ℤ` and Tags 01ID, 01SA, 01AJ. Here the base change is `isPullback_jS`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory TopologicalSpace
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

noncomputable section

namespace AlgMag.GB

section Eval

variable {S : Scheme.{u}} (N : Type u) [AddCommMonoid N]

/-- The restriction to `q⁻¹ U` of a point of `𝔸(N)` over `T`. -/
def resPt (T : Over S) (x : APt (overO S) N (op T)) (U : S.Opens) :
    Multiplicative N →* Γ(T.left, T.hom ⁻¹ᵁ U) :=
  ((T.left.presheaf.map (homOfLE le_top).op).hom : Γ(T.left, ⊤) →+* _).toMonoidHom.comp x

/-- `r ↦ r`, `X^n ↦ x(n)`: the ring map `𝒪_S(U)[N] → Γ(T, T⁻¹ U)` of a point `x` of `𝔸(N)` over `T`. -/
def evalU (T : Over S) (x : APt (overO S) N (op T)) (U : S.Opens) :
    AddMonoidAlgebra Γ(S, U) N →+* Γ(T.left, T.hom ⁻¹ᵁ U) :=
  AddMonoidAlgebra.liftNCRingHom (T.hom.app U).hom (resPt N T x U) fun _ _ => Commute.all _ _

variable {N}

@[simp] lemma evalU_single_one (T : Over S) (x : APt (overO S) N (op T)) (U : S.Opens) (n : N) :
    evalU N T x U (AddMonoidAlgebra.single n 1) = resPt N T x U (Multiplicative.ofAdd n) := by
  simp [evalU]

@[simp] lemma evalU_single_zero (T : Over S) (x : APt (overO S) N (op T)) (U : S.Opens) (r : Γ(S, U)) :
    evalU N T x U (AddMonoidAlgebra.single 0 r) = (T.hom.app U).hom r := by
  have : resPt N T x U (Multiplicative.ofAdd 0) = 1 := map_one _
  simp [evalU, this]

/-- A ring map from `𝒪_S(U)[N]` is determined by `r ↦`, `X^n ↦`. -/
lemma ringHom_ext_U {U : S.Opens} {B : Type u} [Semiring B]
    {f g : AddMonoidAlgebra Γ(S, U) N →+* B}
    (h0 : ∀ r, f (AddMonoidAlgebra.single 0 r) = g (AddMonoidAlgebra.single 0 r))
    (h1 : ∀ n, f (AddMonoidAlgebra.single n 1) = g (AddMonoidAlgebra.single n 1)) : f = g :=
  AddMonoidAlgebra.ringHom_ext h0 h1

/-- The pull-back of sections along a morphism over `S`. -/
def overPull {T T' : Over S} (f : T ⟶ T') (U : S.Opens) :
    Γ(T'.left, T'.hom ⁻¹ᵁ U) ⟶ Γ(T.left, T.hom ⁻¹ᵁ U) :=
  f.left.appLE (T'.hom ⁻¹ᵁ U) (T.hom ⁻¹ᵁ U) (by
    rw [← Over.w f]
    exact le_of_eq rfl)

lemma app_eq_appLE_of_eq {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b) (U : Y.Opens) (e : a ⁻¹ᵁ U ≤ b ⁻¹ᵁ U) :
    a.app U = b.appLE U (a ⁻¹ᵁ U) e := by
  subst h
  exact Scheme.Hom.app_eq_appLE _

lemma app_overPull {T T' : Over S} (f : T ⟶ T') (U : S.Opens) :
    T'.hom.app U ≫ overPull f U = T.hom.app U := by
  have h : T.hom = f.left ≫ T'.hom := (Over.w f).symm
  have e : T.hom ⁻¹ᵁ U ≤ (f.left ≫ T'.hom) ⁻¹ᵁ U := by rw [h]
  rw [app_eq_appLE_of_eq h U e, Scheme.Hom.comp_appLE]
  rfl

lemma overPull_app_apply {T T' : Over S} (f : T ⟶ T') (U : S.Opens) (r : Γ(S, U)) :
    (overPull f U).hom ((T'.hom.app U).hom r) = (T.hom.app U).hom r :=
  congrArg (fun k => k.hom r) (app_overPull f U)

lemma overPull_resPt {T T' : Over S} (f : T ⟶ T') (x : APt (overO S) N (op T')) (U : S.Opens)
    (n : Multiplicative N) :
    (overPull f U).hom (resPt N T' x U n) = resPt N T (APt.res f.op x) U n := by
  have h : T'.left.presheaf.map (homOfLE le_top).op ≫ overPull f U =
      f.left.appTop ≫ T.left.presheaf.map (homOfLE le_top).op := by
    have ht : f.left.appTop = f.left.appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE f.left
    rw [overPull, Scheme.Hom.map_appLE, ht]
    exact (Scheme.Hom.appLE_map _ _ _).symm
  exact congrArg (fun k => k.hom (x n)) h

/-- `evalU` is compatible with pull-backs. -/
lemma overPull_evalU {T T' : Over S} (f : T ⟶ T') (x : APt (overO S) N (op T')) (U : S.Opens) :
    (overPull f U).hom.comp (evalU N T' x U) = evalU N T (APt.res f.op x) U := by
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
  · simp only [RingHom.comp_apply, evalU_single_zero, overPull_app_apply]
  · simp only [RingHom.comp_apply, evalU_single_one, overPull_resPt]

end Eval

section Presheaf

variable (N : Type u) [AddCommMonoid N] (S : Scheme.{u})

/-- The presheaf of rings `U ↦ 𝒪_S(U)[N]` of **Definition 2.3 (ii)**. -/
def preON : (Opens S)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (AddMonoidAlgebra Γ(S, unop U) N)
  map f := CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom N (S.presheaf.map f).hom)
  map_id U := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_) <;> simp
  map_comp f g := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_) <;> simp

/-- `q_* 𝒪` for `q : 𝔸(N)_S → S`. -/
abbrev qStar : TopCat.Presheaf CommRingCat.{u} S := (A N S).hom.base _* (A N S).left.presheaf

/-- The universal point of `𝔸(N)` over `𝔸(N)_S`. -/
abbrev univ : APt (overO S) N (op (A N S)) := pts (A N S) (𝟙 _)

/-- The morphism of presheaves of rings `𝒪_S(-)[N] → q_* 𝒪`, `X^n ↦ X^n`. -/
def cmp : preON N S ⟶ qStar N S where
  app U := CommRingCat.ofHom (evalU N (A N S) (univ N S) (unop U))
  naturality {U V} i := by
    refine CommRingCat.hom_ext (AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_)
    · have h := congrArg (fun k => k.hom r) ((A N S).hom.naturality i)
      change evalU N (A N S) (univ N S) (unop V) (AddMonoidAlgebra.mapRingHom N (S.presheaf.map i).hom
        (AddMonoidAlgebra.single 0 r)) = ((A N S).left.presheaf.map ((Opens.map (A N S).hom.base).map i.unop).op).hom
          (evalU N (A N S) (univ N S) (unop U) (AddMonoidAlgebra.single 0 r))
      rw [AddMonoidAlgebra.mapRingHom_single, evalU_single_zero, evalU_single_zero]
      exact h
    · change evalU N (A N S) (univ N S) (unop V) (AddMonoidAlgebra.mapRingHom N (S.presheaf.map i).hom
        (AddMonoidAlgebra.single n 1)) = ((A N S).left.presheaf.map ((Opens.map (A N S).hom.base).map i.unop).op).hom
          (evalU N (A N S) (univ N S) (unop U) (AddMonoidAlgebra.single n 1))
      rw [AddMonoidAlgebra.mapRingHom_single, map_one, evalU_single_one, evalU_single_one]
      change _ = ((A N S).left.presheaf.map ((Opens.map (A N S).hom.base).map i.unop).op).hom
        (((A N S).left.presheaf.map (homOfLE le_top).op).hom _)
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl

/-- `cmp` commutes with restrictions, on elements. -/
lemma cmp_res {U V : S.Opens} (i : V ⟶ U) (z : AddMonoidAlgebra Γ(S, U) N) :
    evalU N (A N S) (univ N S) V (AddMonoidAlgebra.mapRingHom N (S.presheaf.map i.op).hom z) =
      ((qStar N S).map i.op).hom (evalU N (A N S) (univ N S) U z) :=
  congrArg (fun k => k.hom z) ((cmp N S).naturality i.op)

lemma univ_eq : univ N S = ptsZ _ (toAZ N S) := by
  have h : Over.Hom.left (𝟙 (A N S)) ≫ toAZ N S = toAZ N S := by
    rw [Over.id_left, Category.id_comp]
  exact congrArg (ptsZ (A N S).left) h

/-- `cmp` is bijective on affine opens: `q_* 𝒪 (U) = 𝒪_S(U)[N]` (Definition 2.3 (ii), last assertion). -/
theorem cmp_bijective {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (evalU N (A N S) (univ N S) U) := by
  obtain ⟨e, h1, h0⟩ := fact26_i_sections N hU
  have hc : e.toRingHom.comp (evalU N (A N S) (univ N S) U) = RingHom.id _ := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
    · simp only [RingHom.comp_apply, evalU_single_zero, RingHom.id_apply]
      exact h0 r
    · simp only [RingHom.comp_apply, evalU_single_one, RingHom.id_apply]
      rw [univ_eq]
      exact h1 n
  have hb : Function.Bijective (⇑e ∘ evalU N (A N S) (univ N S) U) := by
    have : ⇑e ∘ evalU N (A N S) (univ N S) U = id := funext fun z => DFunLike.congr_fun hc z
    rw [this]
    exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff' e.bijective _).1 hb

lemma exists_affine_le {W : S.Opens} (x : S) (hx : x ∈ W) :
    ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  exact ⟨V, hV, hxV, hVW⟩

lemma cmp_locallyInjective : Presheaf.IsLocallyInjective (Opens.grothendieckTopology S) (cmp N S) := by
  refine ⟨fun {W} x y h => ?_⟩
  intro p hp
  obtain ⟨V, hV, hpV, hVW⟩ := exists_affine_le S p hp
  refine ⟨V, homOfLE hVW, ?_, hpV⟩
  apply (cmp_bijective N S hV).1
  exact (cmp_res N S (homOfLE hVW) x).trans ((congrArg _ h).trans (cmp_res N S (homOfLE hVW) y).symm)

lemma cmp_locallySurjective : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S) (cmp N S) := by
  refine ⟨fun {W} y => ?_⟩
  intro p hp
  obtain ⟨V, hV, hpV, hVW⟩ := exists_affine_le S p hp
  refine ⟨V, homOfLE hVW, ?_, hpV⟩
  obtain ⟨z, hz⟩ := (cmp_bijective N S hV).2 (((qStar N S).map (homOfLE hVW).op).hom y)
  exact ⟨z, hz⟩

/-- **Fact 2.6 (i)**, the algebra: `q_* 𝒪` is a sheaf, and `cmp` is locally injective and locally
surjective. So `q_* 𝒪` is the sheafification of `U ↦ 𝒪_S(U)[N]`, that is `𝒪_S[N]`. -/
theorem fact26_i_sheafification :
    (qStar N S).IsSheaf ∧
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology S) (cmp N S) ∧
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology S) (cmp N S) :=
  ⟨TopCat.Sheaf.pushforward_sheaf_of_sheaf _ (A N S).left.sheaf.2, cmp_locallyInjective N S,
    cmp_locallySurjective N S⟩

end Presheaf

section Bialgebra

variable (N : Type u) [AddCommMonoid N] {S : Scheme.{u}}

/-- `evalU` as a map of `𝒪_S(U)`-algebras. -/
def evalAlg (T : Over S) (x : APt (overO S) N (op T)) (U : S.Opens) :
    letI := (T.hom.app U).hom.toAlgebra
    AddMonoidAlgebra Γ(S, U) N →ₐ[Γ(S, U)] Γ(T.left, T.hom ⁻¹ᵁ U) :=
  letI := (T.hom.app U).hom.toAlgebra
  { evalU N T x U with
    commutes' := fun r => evalU_single_zero T x U r }

/-- `a ⊗ b ↦ x(a) y(b)`: the ring map `𝒪_S(U)[N] ⊗ 𝒪_S(U)[N] → Γ(T, T⁻¹ U)` of two points of `𝔸(N)`
over `T`. -/
def evalTensor (T : Over S) (x y : APt (overO S) N (op T)) (U : S.Opens) :
    AddMonoidAlgebra Γ(S, U) N ⊗[Γ(S, U)] AddMonoidAlgebra Γ(S, U) N →+* Γ(T.left, T.hom ⁻¹ᵁ U) :=
  letI := (T.hom.app U).hom.toAlgebra
  (Algebra.TensorProduct.productMap (evalAlg N T x U) (evalAlg N T y U)).toRingHom

variable {N}

lemma evalTensor_tmul (T : Over S) (x y : APt (overO S) N (op T)) (U : S.Opens)
    (a b : AddMonoidAlgebra Γ(S, U) N) :
    evalTensor N T x y U (a ⊗ₜ b) = evalU N T x U a * evalU N T y U b := by
  letI := (T.hom.app U).hom.toAlgebra
  exact Algebra.TensorProduct.productMap_apply_tmul (evalAlg N T x U) (evalAlg N T y U) a b

variable (N S)

/-- The universal pair of points of `𝔸(N)` over `𝔸(N)_S ×_S 𝔸(N)_S`. -/
abbrev A2 : Over S := A N S ⊗ A N S

/-- `S`, over `S`. -/
abbrev baseO : Over S := Over.mk (𝟙 S)

/-- The unit section of the monoid scheme `𝔸(N)_S`: the point `1`. -/
def unitA : baseO S ⟶ A N S := (pts (baseO S)).symm 1

lemma comul_single_eq (R : Type u) [CommRing R] (n : N) (r : R) :
    Coalgebra.comul (R := R) (AddMonoidAlgebra.single n r) =
      AddMonoidAlgebra.single n (1 : R) ⊗ₜ[R] AddMonoidAlgebra.single n r := by
  simp [AddMonoidAlgebra.comul_single, TensorProduct.smul_tmul']

/-- **Fact 2.6 (i)**, the comultiplication: on every open `U` of `S`, `cmp` carries the comultiplication of
`𝒪_S(U)[N]` to the multiplication of the monoid scheme `𝔸(N)_S`. -/
theorem fact26_i_comul (U : S.Opens) :
    (overPull (mul N S) U).hom.comp (evalU N (A N S) (univ N S) U) =
      (evalTensor N (A2 N S) (pts _ (fst _ _)) (pts _ (snd _ _)) U).comp
        (Bialgebra.comulAlgHom Γ(S, U) (AddMonoidAlgebra Γ(S, U) N)).toRingHom := by
  rw [overPull_evalU]
  have hm : APt.res (mul N S).op (univ N S) = pts _ (fst _ _) * pts _ (snd _ _) := by
    rw [← pts_comp, Category.comp_id]
    have h := pts_mul (fst (A N S) (A N S)) (snd (A N S) (A N S))
    rwa [lift_fst_snd, Category.id_comp] at h
  rw [hm]
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
  · refine (evalU_single_zero _ _ _ r).trans ?_
    change _ = evalTensor N (A2 N S) _ _ U (Coalgebra.comul (AddMonoidAlgebra.single 0 r))
    rw [comul_single_eq, evalTensor_tmul, evalU_single_one, evalU_single_zero, ofAdd_zero, map_one, one_mul]
  · refine (evalU_single_one _ _ _ n).trans ?_
    change _ = evalTensor N (A2 N S) _ _ U (Coalgebra.comul (AddMonoidAlgebra.single n 1))
    rw [comul_single_eq, evalTensor_tmul, evalU_single_one, evalU_single_one]
    exact map_mul (((A2 N S).left.presheaf.map (homOfLE le_top).op).hom : _ →+* _) _ _

/-- **Fact 2.6 (i)**, the counit: on every open `U` of `S`, `cmp` carries the counit of `𝒪_S(U)[N]` to the
unit section of `𝔸(N)_S`. -/
theorem fact26_i_counit (U : S.Opens) :
    (overPull (unitA N S) U).hom.comp (evalU N (A N S) (univ N S) U) =
      ((baseO S).hom.app U).hom.comp
        (Bialgebra.counitAlgHom Γ(S, U) (AddMonoidAlgebra Γ(S, U) N)).toRingHom := by
  rw [overPull_evalU]
  have hm : APt.res (unitA N S).op (univ N S) = 1 := by
    rw [← pts_comp, Category.comp_id, unitA, Equiv.apply_symm_apply]
  rw [hm]
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
  · refine (evalU_single_zero _ _ _ r).trans (congrArg (⇑((baseO S).hom.app U).hom) ?_)
    exact ((AddMonoidAlgebra.counit_single _ _).trans (by simp)).symm
  · have h1 : resPt N (baseO S) 1 U (Multiplicative.ofAdd n) = 1 :=
      map_one ((baseO S).left.presheaf.map (homOfLE le_top).op).hom
    refine ((evalU_single_one _ _ _ n).trans h1).trans ?_
    refine Eq.symm ((congrArg (⇑((baseO S).hom.app U).hom)
      ((AddMonoidAlgebra.counit_single _ _).trans (by simp))).trans (map_one _))

/-- The comultiplication is that of the monoid scheme. -/
theorem pts_fst_mul_snd :
    pts _ (mul N S) = pts (A2 N S) (fst _ _) * pts _ (snd _ _) := by
  have h := pts_mul (fst (A N S) (A N S)) (snd (A N S) (A N S))
  rwa [lift_fst_snd, Category.id_comp] at h

/-- **Fact 2.6 (i)**: for `U` affine, `𝒪_S(U)[N] ⊗ 𝒪_S(U)[N] = Γ(𝔸(N)_S ×_S 𝔸(N)_S, -)`. So the sections
above identify the comultiplication of the bialgebra of `𝔸(N)_S` with that of `𝒪_S(U)[N]`. -/
theorem fact26_i_tensor_bijective {U : S.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (evalTensor N (A2 N S) (pts _ (fst _ _)) (pts _ (snd _ _)) U) := by
  let q := (A N S).hom
  have hAff : IsAffineHom q := inferInstance
  have hU' : IsAffineOpen (q ⁻¹ᵁ U) := hU.preimage q
  have hP : IsPullback (snd (A N S) (A N S)).left (fst (A N S) (A N S)).left q q :=
    (IsPullback.of_hasPullback q q).flip
  obtain ⟨E, hE1, hE0⟩ : ∃ E : Γ((A2 N S).left, (A2 N S).hom ⁻¹ᵁ U) ≃+*
        AddMonoidAlgebra Γ((A N S).left, q ⁻¹ᵁ U) N,
      (∀ n : N, E (((A2 N S).left.presheaf.map (homOfLE le_top).op).hom
        ((snd (A N S) (A N S)).left.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)))) =
          AddMonoidAlgebra.single n 1) ∧
      ∀ r : Γ((A N S).left, q ⁻¹ᵁ U), E (((fst (A N S) (A N S)).left.app (q ⁻¹ᵁ U)).hom r) =
        AddMonoidAlgebra.single 0 r :=
    sections_of_isPullback N hP hU'
  let c := evalU N (A N S) (univ N S) U
  have hcb : Function.Bijective c := cmp_bijective N S hU
  let G : AddMonoidAlgebra Γ(S, U) N ≃+* Γ((A N S).left, q ⁻¹ᵁ U) := RingEquiv.ofBijective c hcb
  let Ψ₀ := AddMonoidAlgebra.scalarTensorEquiv (M := N) Γ(S, U) (AddMonoidAlgebra Γ(S, U) N)
  let Gm := AddMonoidAlgebra.mapRingEquiv N G
  have hov : overPull (fst (A N S) (A N S)) U = (fst (A N S) (A N S)).left.app (q ⁻¹ᵁ U) :=
    (Scheme.Hom.app_eq_appLE _).symm
  have hbr : ∀ r', E ((overPull (fst (A N S) (A N S)) U).hom r') = AddMonoidAlgebra.single 0 r' := fun r' =>
    (congrArg (fun k => E (CommRingCat.Hom.hom k r')) hov).trans (hE0 r')
  have hfst : ∀ a, E ((evalU N (A2 N S) (pts _ (fst _ _)) U) a) = AddMonoidAlgebra.single 0 (c a) := by
    intro a
    have h := DFunLike.congr_fun (overPull_evalU (fst (A N S) (A N S)) (univ N S) U) a
    rw [← pts_comp, Category.comp_id] at h
    rw [← h]
    exact hbr (c a)
  have hG : ∀ (m : N) s, Gm (AddMonoidAlgebra.single m s) = AddMonoidAlgebra.single m (c s) := by
    intro m s
    simp [Gm, G]
  have hsnd : ∀ b, E ((evalU N (A2 N S) (pts _ (snd _ _)) U) b) =
      Gm (AddMonoidAlgebra.mapAlgHom N (Algebra.ofId Γ(S, U) (AddMonoidAlgebra Γ(S, U) N)) b) := by
    intro b
    have hrh : E.toRingHom.comp (evalU N (A2 N S) (pts _ (snd _ _)) U) =
        Gm.toRingHom.comp (AddMonoidAlgebra.mapAlgHom N
          (Algebra.ofId Γ(S, U) (AddMonoidAlgebra Γ(S, U) N))).toRingHom := by
      refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun n => ?_
      · change E ((evalU N (A2 N S) (pts _ (snd _ _)) U) (AddMonoidAlgebra.single 0 r)) =
          Gm (AddMonoidAlgebra.mapAlgHom N (Algebra.ofId Γ(S, U) (AddMonoidAlgebra Γ(S, U) N))
            (AddMonoidAlgebra.single 0 r))
        rw [evalU_single_zero, ← overPull_app_apply (fst (A N S) (A N S)) U r, hbr]
        simp only [AddMonoidAlgebra.mapAlgHom_single, hG]
        congr 1
        exact (evalU_single_zero _ _ U r).symm
      · change E ((evalU N (A2 N S) (pts _ (snd _ _)) U) (AddMonoidAlgebra.single n 1)) =
          Gm (AddMonoidAlgebra.mapAlgHom N (Algebra.ofId Γ(S, U) (AddMonoidAlgebra Γ(S, U) N))
            (AddMonoidAlgebra.single n 1))
        rw [evalU_single_one]
        simp only [AddMonoidAlgebra.mapAlgHom_single, hG, map_one]
        have h0 : pts _ (snd (A N S) (A N S)) (Multiplicative.ofAdd n) =
            (snd (A N S) (A N S)).left.appTop.hom (ptsZ _ (toAZ N S) (Multiplicative.ofAdd n)) := by
          change ptsZ _ ((snd (A N S) (A N S)).left ≫ toAZ N S) _ = _
          rw [ptsZ_comp]
          rfl
        change E (((A2 N S).left.presheaf.map (homOfLE le_top).op).hom
          (pts _ (snd (A N S) (A N S)) (Multiplicative.ofAdd n))) = _
        rw [h0]
        exact hE1 n
    exact DFunLike.congr_fun hrh b
  have hsm : ∀ (a : AddMonoidAlgebra Γ(S, U) N) (y : AddMonoidAlgebra (AddMonoidAlgebra Γ(S, U) N) N),
      Gm (a • y) = AddMonoidAlgebra.single 0 (c a) * Gm y := by
    intro a y
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, mul_add, hx, hy]
    | single m s =>
      rw [AddMonoidAlgebra.smul_single, hG, hG, AddMonoidAlgebra.single_mul_single, zero_add, smul_eq_mul,
        map_mul]
  have hmain : ∀ z, E (evalTensor N (A2 N S) (pts _ (fst _ _)) (pts _ (snd _ _)) U z) = Gm (Ψ₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul a b =>
      rw [evalTensor_tmul, map_mul, hfst, hsnd, AddMonoidAlgebra.scalarTensorEquiv_tmul, hsm]
  have hb : Function.Bijective (⇑E ∘ evalTensor N (A2 N S) (pts _ (fst _ _)) (pts _ (snd _ _)) U) := by
    have : ⇑E ∘ evalTensor N (A2 N S) (pts _ (fst _ _)) (pts _ (snd _ _)) U = ⇑Gm ∘ ⇑Ψ₀ := funext hmain
    rw [this]
    exact Gm.bijective.comp Ψ₀.bijective
  exact (Function.Bijective.of_comp_iff' E.bijective _).1 hb

end Bialgebra

end AlgMag.GB

#print axioms AlgMag.GB.cmp
#print axioms AlgMag.GB.cmp_bijective
#print axioms AlgMag.GB.fact26_i_sheafification
#print axioms AlgMag.GB.fact26_i_comul
#print axioms AlgMag.GB.fact26_i_counit
#print axioms AlgMag.GB.fact26_i_tensor_bijective
