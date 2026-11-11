/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3LeftoverKey

/-!
# Algebraic Magnetism, Proposition 3.28: `V(E)^N = V(E_N)`, as functors

For `E = ⨁_m E_m` an `M`-graded `𝒪_S`-module over an arbitrary scheme `S`, and `N` a magnet of `M`, the
attractor of `V(E)` is `T ↦ Hom_{𝒪_S}(E_N, p_* 𝒪_T)` with `E_N = ⨁_{n ∈ N} E_n`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism TopologicalSpace

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

variable {S : Scheme.{u}}

lemma sec_map {P : S.Modules} {T : Over S} (ξ : P ⟶ pO T) {U V : S.Opens} (h : V ≤ U) (x : Γ(P, U)) :
    sec ξ V (P.presheaf.map (homOfLE h).op x) =
      (T.left.presheaf.map ((Opens.map T.hom.base).map (homOfLE h)).op).hom (sec ξ U x) :=
  ConcreteCategory.congr_hom (ξ.mapPresheaf.naturality (homOfLE h).op) x

lemma map_appLE_map {X Y : Scheme.{u}} (f : X ⟶ Y) (A A' : Y.Opens) (h : A' ≤ A) (B : X.Opens)
    (e : B ≤ f ⁻¹ᵁ A') (C : X.Opens) (hC : C ≤ B) (hC' : C ≤ f ⁻¹ᵁ A) :
    Y.presheaf.map (homOfLE h).op ≫ f.appLE A' B e ≫ X.presheaf.map (homOfLE hC).op =
      f.app A ≫ X.presheaf.map (homOfLE hC').op := by
  rw [← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  rfl

/-- Morphisms to `p_* 𝒪_T` are determined on affine test schemes over affine opens of `S`. -/
lemma local_ext {P : S.Modules} {T : Over S} {ξ ξ' : P ⟶ pO T}
    (H : ∀ (V : S.Opens) (hV : IsAffineOpen V) (D : CommAlgCat.{u} Γ(S, V)) (s : Phi hV D ⟶ T)
      (x : Γ(P, V)), val hV (liesOver_Phi hV D) (ξ ≫ resO s) x =
        val hV (liesOver_Phi hV D) (ξ' ≫ resO s) x) : ξ = ξ' := by
  refine pO_ext fun U x₀ => ?_
  refine TopCat.Presheaf.section_ext T.left.sheaf _ _ _ fun y hy => ?_
  have hy' : T.hom y ∈ U := hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open hy' U.2
  have hVU' : V ≤ U := hVU
  have hV' : IsAffineOpen V := hV
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWA⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ T.hom ⁻¹ᵁ V from hyV)
      (T.hom ⁻¹ᵁ V).2
  have hWA' : W ≤ T.hom ⁻¹ᵁ V := hWA
  let WO : Over S := Over.mk ((Scheme.Opens.ι W) ≫ T.hom)
  let j : WO ⟶ T := Over.homMk (Scheme.Opens.ι W) rfl
  have hWO : LiesOver WO V := liesOver_of_forall fun z => by
    let z' : (Scheme.Opens.toScheme W) := z
    have h : T.hom ((Scheme.Opens.ι W) z') ∈ V := hWA' z'.2
    have e : ((Scheme.Opens.ι W) ≫ T.hom) z' = T.hom ((Scheme.Opens.ι W) z') :=
      Scheme.Hom.comp_apply _ _ _
    rw [← e] at h
    exact h
  haveI : IsAffine WO.left := (show IsAffineOpen W from hW)
  let e := toSpecHom hV' WO hWO
  let i : Phi hV' (Ga hV' WO hWO) ⟶ WO := inv e
  have hiL : IsIso i.left := inferInstanceAs (IsIso ((Over.forget S).map i))
  have ginj : Function.Injective (gpull hV' hWO (liesOver_Phi hV' _) i) := by
    have : IsIso i.left.appTop := inferInstanceAs (IsIso (i.left.app ⊤))
    exact ((ConcreteCategory.isIso_iff_bijective i.left.appTop).mp this).1
  let x : Γ(P, V) := P.presheaf.map (homOfLE hVU').op x₀
  have q := H V hV' (Ga hV' WO hWO) (i ≫ j) x
  rw [resO_comp, ← Category.assoc, ← Category.assoc,
    val_res hV' hWO (liesOver_Phi hV' _) (ξ ≫ resO j) i x,
    val_res hV' hWO (liesOver_Phi hV' _) (ξ' ≫ resO j) i x] at q
  have q' := ginj q
  -- the restriction to `W`
  have hle : (⊤ : (Scheme.Opens.toScheme W).Opens) ≤ (Scheme.Opens.ι W) ⁻¹ᵁ (T.hom ⁻¹ᵁ U) := fun z _ => hVU' (hWA' z.2)
  have R : ∀ ζ : P ⟶ pO T, val hV' hWO (ζ ≫ resO j) x =
      ((Scheme.Opens.toScheme W).presheaf.map (homOfLE hle).op).hom ((Scheme.Opens.ι W).app (T.hom ⁻¹ᵁ U) |>.hom (sec ζ U x₀)) := by
    intro ζ
    change (WO.left.presheaf.map _).hom (((Scheme.Opens.ι W).appLE (T.hom ⁻¹ᵁ V) (WO.hom ⁻¹ᵁ V) _).hom (sec ζ V x)) = _
    rw [sec_map]
    have h1 := map_appLE_map (Scheme.Opens.ι W) (T.hom ⁻¹ᵁ U) (T.hom ⁻¹ᵁ V)
      ((Opens.map T.hom.base).map (homOfLE hVU')).le (WO.hom ⁻¹ᵁ V) (preimage_le j V) ⊤
      (le_of_eq hWO.symm) hle
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) (sec ζ U x₀)
  rw [R, R] at q'
  let y₀ : (Scheme.Opens.toScheme W) := ⟨y, hyW⟩
  have hinj : Function.Injective ((Scheme.Opens.ι W).stalkMap y₀) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  refine hinj ?_
  have g1 := Scheme.Hom.germ_stalkMap_apply (Scheme.Opens.ι W) (T.hom ⁻¹ᵁ U) y₀ hy (sec ξ U x₀)
  have g2 := Scheme.Hom.germ_stalkMap_apply (Scheme.Opens.ι W) (T.hom ⁻¹ᵁ U) y₀ hy (sec ξ' U x₀)
  refine g1.trans (Eq.trans ?_ g2.symm)
  have r1 := TopCat.Presheaf.germ_res_apply (Scheme.Opens.toScheme W).presheaf (homOfLE hle) y₀ trivial
    ((Scheme.Opens.ι W).app (T.hom ⁻¹ᵁ U) |>.hom (sec ξ U x₀))
  have r2 := TopCat.Presheaf.germ_res_apply (Scheme.Opens.toScheme W).presheaf (homOfLE hle) y₀ trivial
    ((Scheme.Opens.ι W).app (T.hom ⁻¹ᵁ U) |>.hom (sec ξ' U x₀))
  exact r1.symm.trans ((congrArg _ q').trans r2)

end AlgMag.VB
