/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge
import AlgMag.Sec9OverBSpaces

/-!
# §9 of *Algebraic Magnetism* over an algebraic space `B`: genuine instances and the status of `IsQCoh`

Statements for genuine affine morphisms of algebraic spaces, and the comparison of `AlgMag.S9B.IsQCoh`
with Stacks quasi-coherent modules on the objects of the site.

* `AlgMag.S9BR.prop91_canonical`: Proposition 9.1, with the printed canonical map, on affine `T`.
* `AlgMag.S9BR.prop91_of_local`: its base change, from the local datum (Tag 03DX).
* `AlgMag.S9BR.prop99_space`, `AlgMag.S9BR.prop910_space`: Propositions 9.9, 9.10 for
  `Space.IsAffineHom`.
* `AlgMag.S9BR.coactionEquivDecomp`, `coaction_eq_rhoV`, `decomp_comp_eq_coeff`: Propositions 9.10 and
  9.11 linked for `H = 𝔸(M)_B`.
* `AlgMag.S9BR.prop912_space`, `prop913_of_coaction`: Propositions 9.12, 9.13 linked.
* `AlgMag.S9BR.isQCoh_iff_affine_local`: `IsQCoh F` if and only if `F` is a Zariski sheaf and has the
  local datum over each affine `T`. Through it, every `IsQCoh` module has the local datum over affine
  `T` (`localAssoc_of_isQCoh`), the module on `T` being `F(T)^~`; `localAssoc_restr` is the case of a
  module pulled back from a scheme.

## Remarks on the hypotheses

* `AlgMag.S9BF.prop91` (`Sec9OverBFinal.lean`) is a field projection of `hG : IsQCoh G`: it unfolds the
  definition and carries no content by itself. The statements with content are `prop91_canonical`
  (the canonical map) and `prop91_of_local`.
* Results with hypothesis `IsQCoh` over a genuine space `B` remain conditional on that hypothesis: no
  instance from a Stacks quasi-coherent module on `B` is constructed.
* `AlgMag.S9BF.isQCoh_of_localAssoc` asks for `LocalAssoc` over every `T`, also non-affine; no such
  term is constructed for non-affine `T`. `isQCoh_iff_affine_local` needs affine `T` only.
* The coherence of `Space.modulePullbackCompIso` is `Space.modulePullbackCompIsoAssoc`.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

namespace AlgMag.S9BR

open AlgMag.S9B AlgMag.S9BF AlgMag.Leftover AlgMag.S9BS
open AlgMag.S9 (PMod IsBC HModule)

attribute [local instance] AffOver.aff

lemma exists_qc_top (X : Scheme.{u}) [IsAffine X] (M : Type u) [AddCommGroup M] [Module Γ(X, ⊤) M] :
    ∃ G : X.Modules, G.IsQuasicoherent ∧ ∃ e : M ≃+ Γ(G, ⊤),
      ∀ (r : Γ(X, ⊤)) (m : M), e (r • m) = r • e m := by
  let f : X ⟶ Spec Γ(X, ⊤) := X.isoSpec.hom
  let N : ModuleCat Γ(X, ⊤) := ModuleCat.of _ M
  let T := AlgebraicGeometry.tilde N
  have htop : f ''ᵁ ⊤ = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.opensRange_of_isIso f
  have hb : Function.Bijective (tilde.toOpen N (f ''ᵁ ⊤)).hom := by
    rw [htop]
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  refine ⟨T.restrict f, inferInstance, ?_⟩
  refine ⟨AddEquiv.ofBijective (tilde.toOpen N (f ''ᵁ ⊤)).hom.toAddMonoidHom hb, ?_⟩
  intro r m
  change (show Γ(T, f ''ᵁ ⊤) from (tilde.toOpen N (f ''ᵁ ⊤)).hom (r • m)) = (f.appIso ⊤).inv r • (show Γ(T, f ''ᵁ ⊤) from (tilde.toOpen N (f ''ᵁ ⊤)).hom m)
  have h1 := (tilde.toOpen N (f ''ᵁ ⊤)).hom.map_smul r m
  refine h1.trans ?_
  have key : (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ (Spec Γ(X, ⊤)).presheaf.map (f ''ᵁ ⊤).leTop.op =
      (f.appIso ⊤).inv := by
    refine (Iso.comp_hom_eq_id _).1 ?_
    have h2 : f.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := Scheme.toSpecΓ_appTop X
    rw [Scheme.Hom.appIso_hom, Category.assoc]
    have e : ∀ q : (op ⊤ : X.Opensᵒᵖ) ⟶ op ⊤, X.presheaf.map q = 𝟙 _ := fun q => by
      rw [Subsingleton.elim q (𝟙 _)]
      exact X.presheaf.map_id _
    rw [← Category.assoc ((Spec Γ(X, ⊤)).presheaf.map _), Scheme.Hom.naturality, Category.assoc,
      ← Functor.map_comp]
    refine Eq.trans (congrArg (fun k => (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ Scheme.Hom.app f ⊤ ≫ k) (e _)) ?_
    exact (congrArg (fun k => (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ k) (Category.comp_id f.appTop)).trans
      ((congrArg (fun k => (Scheme.ΓSpecIso Γ(X, ⊤)).inv ≫ k) h2).trans (Iso.inv_hom_id _))
  have h4 : (f.appIso ⊤).inv r = (Spec Γ(X, ⊤)).presheaf.map (f ''ᵁ ⊤).leTop.op
      ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) := by rw [← key]; rfl
  rw [h4]
  rfl

section Algebra
variable {R R' E E' D D' : Type u} [CommRing R] [CommRing R']
  [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']
  [AddCommGroup D] [Module R D] [AddCommGroup D'] [Module R' D']

/-- Induction on a base change. -/
lemma bc_induction (φ : R →+* R') (f : E →+ E') (hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x)
    (h : IsBC φ f hf) {P : E' → Prop} (h0 : P 0) (h1 : ∀ x, P (f x))
    (h2 : ∀ (c : R') y, P y → P (c • y)) (h3 : ∀ y z, P y → P z → P (y + z)) (y : E') : P y := by
  letI := φ.toAlgebra
  letI : Module R E' := Module.compHom E' φ
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  have h' : IsBaseChange R' ({ toFun := f, map_add' := f.map_add, map_smul' := hf } : E →ₗ[R] E') := h
  refine h'.inductionOn y P h0 ?_ h2 h3
  · intro x; exact h1 x

/-- Two base changes of isomorphic modules are isomorphic. -/
lemma exists_bc_equiv (φ : R →+* R') (f : E →+ E') (hf : ∀ (r : R) (x : E), f (r • x) = φ r • f x)
    (g : D →+ D') (hg : ∀ (r : R) (x : D), g (r • x) = φ r • g x)
    (hfb : IsBC φ f hf) (hgb : IsBC φ g hg) (e : E ≃+ D) (he : ∀ (r : R) (x : E), e (r • x) = r • e x) :
    ∃ e' : E' ≃+ D', (∀ (r : R') (x : E'), e' (r • x) = r • e' x) ∧ ∀ x, e' (f x) = g (e x) := by
  letI := φ.toAlgebra
  letI : Module R E' := Module.compHom E' φ
  letI : Module R D' := Module.compHom D' φ
  haveI : IsScalarTower R R' E' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  haveI : IsScalarTower R R' D' := ⟨fun r s x => by
    change (φ r * s) • x = φ r • s • x
    rw [mul_smul]⟩
  have hf' : IsBaseChange R' ({ toFun := f, map_add' := f.map_add, map_smul' := hf } : E →ₗ[R] E') := hfb
  have hg' : IsBaseChange R' ({ toFun := g, map_add' := g.map_add, map_smul' := hg } : D →ₗ[R] D') := hgb
  let eL : E ≃ₗ[R] D := { e with map_smul' := he }
  let T : R' ⊗[R] E ≃ₗ[R'] R' ⊗[R] D :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eL
  let e1 : E' ≃ₗ[R'] D' := hf'.equiv.symm.trans (T.trans hg'.equiv)
  refine ⟨e1.toAddEquiv, fun r x => e1.map_smul r x, fun x => ?_⟩
  change hg'.equiv (T (hf'.equiv.symm (f x))) = _
  have h1 : hf'.equiv.symm (f x) = (1 : R') ⊗ₜ x := by
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rfl
  rw [h1]
  change hg'.equiv ((1 : R') ⊗ₜ eL x) = _
  rw [IsBaseChange.equiv_tmul, one_smul]
  rfl

end Algebra

/-- Global sections of a pull-back along the identity. -/
lemma exists_top_pullback {X : Scheme.{u}} (G : X.Modules) (a : X ⟶ X) (h : a = 𝟙 X) :
    ∃ e : Γ(G, ⊤) ≃+ Γ((Scheme.Modules.pullback a).obj G, ⊤),
      ∀ (r : Γ(X, ⊤)) (x : Γ(G, ⊤)), e (r • x) = r • e x := by
  subst h
  let i : (Scheme.Modules.pullback (𝟙 X)).obj G ≅ G := (Scheme.Modules.pullbackId X).app G
  have h1 : ∀ x, (Scheme.Modules.Hom.app i.inv ⊤).hom ((Scheme.Modules.Hom.app i.hom ⊤).hom x) = x := by
    intro x
    have e : Scheme.Modules.Hom.app (i.hom ≫ i.inv) ⊤ = Scheme.Modules.Hom.app (𝟙 _) ⊤ := by rw [i.hom_inv_id]
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact congrArg (fun k => k.hom x) e
  have h2 : ∀ x, (Scheme.Modules.Hom.app i.hom ⊤).hom ((Scheme.Modules.Hom.app i.inv ⊤).hom x) = x := by
    intro x
    have e : Scheme.Modules.Hom.app (i.inv ≫ i.hom) ⊤ = Scheme.Modules.Hom.app (𝟙 _) ⊤ := by rw [i.inv_hom_id]
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at e
    exact congrArg (fun k => k.hom x) e
  refine ⟨{ toFun := (Scheme.Modules.Hom.app i.inv ⊤).hom, invFun := (Scheme.Modules.Hom.app i.hom ⊤).hom,
            left_inv := h2, right_inv := h1, map_add' := map_add _ }, ?_⟩
  intro r x
  exact Scheme.Modules.Hom.app_smul i.inv r x

section Slice
variable {T : SB Bsp} {H : PMod (GB.overO T.left)}

lemma mp_mp {W A C : SB Bsp} (s' : W ⟶ A) (s : A ⟶ C) (k : C ⟶ T) (k' : A ⟶ T) (k'' : W ⟶ T)
    (h : s ≫ k = k') (h' : s' ≫ k' = k'') (x : H.obj (op (overT k))) :
    H.map (mpT s' k' k'' h').op (H.map (mpT s k k' h).op x) =
      H.map (mpT (s' ≫ s) k k'' (by rw [Category.assoc, h, h'])).op x := by
  rw [← H.map_comp, ← op_comp]
  congr 2

instance (W : SB Bsp) (i : W.left.affineCover.I₀) :
    IsAffine (coverPiece W W.left.affineCover i).left := by
  change IsAffine (W.left.affineCover.X i)
  infer_instance

/-- Separation over an open cover of an object over `T`. -/
lemma sep_piece {W : SB Bsp} (hH : AlgMag.S9.IsQCoh H) (w : W ⟶ T) (𝒱 : Scheme.OpenCover.{u} W.left)
    {y y' : H.obj (op (overT w))}
    (h : ∀ j, H.map (mpT (coverHom W 𝒱 j) w _ rfl).op y = H.map (mpT (coverHom W 𝒱 j) w _ rfl).op y') :
    y = y' := by
  refine AlgMag.S9.sep_cover hH (overT w) 𝒱 fun j => ?_
  let v : AlgMag.S9.coverPiece (overT w) 𝒱 j ⟶ overT (coverHom W 𝒱 j ≫ w) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ SB.Hom.left (coverHom W 𝒱 j ≫ w) = 𝒱.f j ≫ SB.Hom.left w
      rw [Category.id_comp, SB.comp_left]
      rfl)
  have e : AlgMag.S9.coverHom (overT w) 𝒱 j = v ≫ mpT (coverHom W 𝒱 j) w _ rfl :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  rw [e, op_comp, H.map_comp, H.map_comp, h]

lemma sep_aff {W : SB Bsp} (hH : AlgMag.S9.IsQCoh H) (w : W ⟶ T) {y y' : H.obj (op (overT w))}
    (h : ∀ (A : SB Bsp) (a : A ⟶ W) [IsAffine A.left],
      H.map (mpT a w _ rfl).op y = H.map (mpT a w _ rfl).op y') : y = y' :=
  sep_piece hH w W.left.affineCover fun j => h _ _

/-- Separation, tested on affine schemes through the pieces of an open cover. -/
lemma sep_aff_piece {W : SB Bsp} (hH : AlgMag.S9.IsQCoh H) (w : W ⟶ T) (𝒱 : Scheme.OpenCover.{u} W.left)
    {y y' : H.obj (op (overT w))}
    (h : ∀ j (A : SB Bsp) (b : A ⟶ coverPiece W 𝒱 j) [IsAffine A.left],
      H.map (mpT (b ≫ coverHom W 𝒱 j) w _ rfl).op y = H.map (mpT (b ≫ coverHom W 𝒱 j) w _ rfl).op y') :
    y = y' := by
  refine sep_piece hH w 𝒱 fun j => sep_aff hH _ fun A a _ => ?_
  rw [mp_mp, mp_mp]
  have h0 := h j A a
  let cst : overT (a ≫ coverHom W 𝒱 j ≫ w) ⟶ overT ((a ≫ coverHom W 𝒱 j) ≫ w) :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ SB.Hom.left ((a ≫ coverHom W 𝒱 j) ≫ w) = SB.Hom.left (a ≫ coverHom W 𝒱 j ≫ w)
      rw [Category.id_comp, Category.assoc])
  have h3 := congrArg (H.map cst.op) h0
  rw [← H.map_comp, ← H.map_comp] at h3
  have e : mpT (a ≫ coverHom W 𝒱 j) w (a ≫ coverHom W 𝒱 j ≫ w) (Category.assoc _ _ _) =
      cst ≫ mpT (a ≫ coverHom W 𝒱 j) w _ rfl := Over.OverMorphism.ext (Category.id_comp _).symm
  rw [e]
  exact h3

/-- **Gluing**: a compatible family of sections over affine schemes over `U` comes from a section
over `U` of a module with `AlgMag.S9.IsQCoh` on `T`. -/
theorem glueH (hH : AlgMag.S9.IsQCoh H) {U : SB Bsp} (u : U ⟶ T)
    (val : ∀ (A : SB Bsp) (a : A ⟶ U) (k : A ⟶ T) (_ : a ≫ u = k) [IsAffine A.left],
      H.obj (op (overT k)))
    (compat : ∀ (A A' : SB Bsp) (s : A' ⟶ A) (a : A ⟶ U) (k : A ⟶ T) (hk : a ≫ u = k)
      (a' : A' ⟶ U) (k' : A' ⟶ T) (hk' : a' ≫ u = k') [IsAffine A.left] [IsAffine A'.left],
      s ≫ a = a' → ∀ hs : s ≫ k = k', H.map (mpT s k k' hs).op (val A a k hk) = val A' a' k' hk') :
    ∃ y : H.obj (op (overT u)), ∀ (A : SB Bsp) (a : A ⟶ U) (k : A ⟶ T) (hk : a ≫ u = k)
      [IsAffine A.left], H.map (mpT a u k hk).op y = val A a k hk := by
  let 𝒰 := U.left.affineCover
  let c := fun i => coverHom U 𝒰 i
  let v : ∀ i, H.obj (op (overT (c i ≫ u))) := fun i => val _ (c i) (c i ≫ u) rfl
  have key : ∀ {Q : SB Bsp} (i j : 𝒰.I₀) (q1 : Q ⟶ coverPiece U 𝒰 i) (q2 : Q ⟶ coverPiece U 𝒰 j)
      (hq : q1 ≫ c i = q2 ≫ c j) (kQ : Q ⟶ T) (h1 : q1 ≫ c i ≫ u = kQ) (h2 : q2 ≫ c j ≫ u = kQ),
      H.map (mpT q1 (c i ≫ u) kQ h1).op (v i) = H.map (mpT q2 (c j ≫ u) kQ h2).op (v j) := by
    intro Q i j q1 q2 hq kQ h1 h2
    refine sep_aff hH kQ fun A b _ => ?_
    rw [mp_mp, mp_mp]
    have hA := compat _ A (b ≫ q1) (c i) (c i ≫ u) rfl (b ≫ q1 ≫ c i) (b ≫ kQ)
      (by rw [Category.assoc, Category.assoc, h1]) (by simp) (by rw [Category.assoc, h1])
    have hB := compat _ A (b ≫ q2) (c j) (c j ≫ u) rfl (b ≫ q1 ≫ c i) (b ≫ kQ)
      (by rw [Category.assoc, Category.assoc, h1]) (by rw [hq]; simp)
      (by rw [Category.assoc, h2])
    exact hA.trans hB.symm
  have wd : ∀ {W : Over T.left} (i j : 𝒰.I₀) (m : W ⟶ overT (c i ≫ u)) (w : W ⟶ overT (c j ≫ u)),
      m.left ≫ 𝒰.f i = w.left ≫ 𝒰.f j → H.map m.op (v i) = H.map w.op (v j) := by
    intro W i j m w hm
    let q1 := coverHom (coverPiece U 𝒰 i) (𝒰.pullback₁ (SB.Hom.left (c i))) j
    let q2 := pieceMap 𝒰 (c i) j
    have hq : q1 ≫ c i = q2 ≫ c j := (pieceMap_ι 𝒰 (c i) j).symm
    let kQ := q1 ≫ c i ≫ u
    have h2 : q2 ≫ c j ≫ u = kQ := by
      rw [← Category.assoc, ← hq, Category.assoc]
    let l : W ⟶ overT kQ := Over.homMk (pullback.lift m.left w.left hm) (by
      change pullback.lift m.left w.left hm ≫ SB.Hom.left (q1 ≫ c i ≫ u) = W.hom
      rw [SB.comp_left]
      change pullback.lift m.left w.left hm ≫ pullback.fst _ _ ≫ _ = W.hom
      rw [← Category.assoc]
      exact (congrArg (fun k => k ≫ SB.Hom.left (c i ≫ u)) (pullback.lift_fst _ _ hm)).trans (Over.w m))
    have hu : m = l ≫ mpT q1 (c i ≫ u) kQ rfl :=
      Over.OverMorphism.ext (pullback.lift_fst _ _ hm).symm
    have hv : w = l ≫ mpT q2 (c j ≫ u) kQ h2 :=
      Over.OverMorphism.ext (pullback.lift_snd _ _ hm).symm
    rw [hu, hv, op_comp, op_comp, H.map_comp, H.map_comp, key i j q1 q2 hq kQ rfl h2]
  have lift : ∀ {W : Over T.left} (g : W ⟶ overT u), (AlgMag.S9.coverSieve (overT u) 𝒰).arrows g →
      ∃ (i : 𝒰.I₀) (m : W ⟶ overT (c i ≫ u)), g.left = m.left ≫ 𝒰.f i := by
    rintro W g ⟨i, t, ht⟩
    refine ⟨i, Over.homMk t ?_, ht⟩
    have hw := Over.w g
    rw [ht] at hw
    change t ≫ SB.Hom.left (c i ≫ u) = W.hom
    rw [SB.comp_left]
    rw [Category.assoc] at hw
    exact hw
  choose ci cu chu using @lift
  let z : Presieve.FamilyOfElements H.toPresheaf (AlgMag.S9.coverSieve (overT u) 𝒰).arrows :=
    fun W g hg => H.map (cu g hg).op (v (ci g hg))
  have hz : z.Compatible := by
    refine (Presieve.compatible_iff_sieveCompatible z).2 ?_
    intro W W' g h hg
    refine Eq.trans ?_ (H.map_comp (cu g hg).op h.op (v (ci g hg)))
    refine wd _ _ _ _ ?_
    rw [← chu, Over.comp_left, chu g hg, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  obtain ⟨y, hy, -⟩ := hH.sheaf _ (AlgMag.S9.coverSieve_mem (overT u) 𝒰) z hz
  have hyi : ∀ i, H.map (mpT (c i) u _ rfl).op y = v i := by
    intro i
    have hg : (AlgMag.S9.coverSieve (overT u) 𝒰).arrows (mpT (c i) u _ rfl) :=
      ⟨i, 𝟙 _, (Category.id_comp _).symm⟩
    refine (hy _ hg).trans ((wd _ i _ (𝟙 _) ?_).trans (H.map_id _ _))
    rw [← chu]
    exact (Category.id_comp _).symm
  have claim : ∀ (j : 𝒰.I₀) {B : SB Bsp} (t : B ⟶ coverPiece U 𝒰 j) (e : B ⟶ U) (k : B ⟶ T)
      (hk : e ≫ u = k) [IsAffine B.left], t ≫ c j = e →
      H.map (mpT e u k hk).op y = val B e k hk := by
    intro j B t e k hk _ he
    subst he
    have hk' : t ≫ c j ≫ u = k := by rw [← hk, Category.assoc]
    have h1 := mp_mp (H := H) t (c j) u (c j ≫ u) k rfl hk' y
    have h2 := compat _ B t (c j) (c j ≫ u) rfl (t ≫ c j) k hk rfl hk'
    exact h1.symm.trans ((congrArg _ (hyi j)).trans h2)
  refine ⟨y, fun A a k hk _ => ?_⟩
  subst hk
  refine sep_aff_piece hH (a ≫ u) (𝒰.pullback₁ (SB.Hom.left a)) fun j B b _ => ?_
  let ch := coverHom A (𝒰.pullback₁ (SB.Hom.left a)) j
  have ep : ch ≫ a = pieceMap 𝒰 a j ≫ c j := (pieceMap_ι 𝒰 a j).symm
  have h5 := mp_mp (H := H) (b ≫ ch) a u (a ≫ u) ((b ≫ ch) ≫ a ≫ u) rfl rfl y
  exact h5.trans ((claim j (b ≫ pieceMap 𝒰 a j) ((b ≫ ch) ≫ a) _ _
    (by rw [Category.assoc, Category.assoc, ep])).trans
    (compat _ B (b ≫ ch) a (a ≫ u) rfl ((b ≫ ch) ≫ a) _ _ rfl _).symm)

end Slice

section Transport
variable {T : SB Bsp} [hT : IsAffine T.left] {H : PMod (GB.overO T.left)} {F : PMod (OB Bsp)}

/-- The data of the transport: `F` and `H` agree on the affine `T`. -/
structure TopIso (F : PMod (OB Bsp)) (H : PMod (GB.overO T.left)) where
  /-- the identification over `T` -/
  e : F.obj (op T) ≃+ H.obj (op (overT (𝟙 T)))
  smul : ∀ (r : (OB Bsp).obj (op T)) (x : F.obj (op T)),
    e (r • x) = (show (GB.overO T.left).obj (op (overT (𝟙 T))) from r) • e x

variable (hH : AlgMag.S9.IsQCoh H) (hF : IsQCoh F) (e0 : TopIso (T := T) F H)

include hH hF in
theorem exA {A : SB Bsp} [IsAffine A.left] (k : A ⟶ T) :
    ∃ e : F.obj (op A) ≃+ H.obj (op (overT k)),
      (∀ (r : (OB Bsp).obj (op A)) (x : F.obj (op A)),
        e (r • x) = (show (GB.overO T.left).obj (op (overT k)) from r) • e x) ∧
      ∀ x, e (F.map k.op x) = H.map (mpT k (𝟙 T) k (Category.comp_id k)).op (e0.e x) := by
  let m := mpT k (𝟙 T) k (Category.comp_id k)
  haveI : IsAffine (overT (𝟙 T)).left := hT
  haveI : IsAffine (overT k).left := ‹IsAffine A.left›
  have hb := hH.base_change m
  exact @exists_bc_equiv ((OB Bsp).obj (op T)) ((OB Bsp).obj (op A)) (F.obj (op T)) (F.obj (op A))
    (H.obj (op (overT (𝟙 T)))) (H.obj (op (overT k))) _ _ _ (F.mod _) _ (F.mod _)
    (H.grp _) (H.mod (op (overT (𝟙 T)))) (H.grp _) (H.mod (op (overT k)))
    ((OB Bsp).map k.op).hom (F.map k.op) (F.map_smul k.op) (H.map m.op) (H.map_smul m.op)
    (hF.base_change k) hb e0.e e0.smul

/-- The identification over an affine `A → T`. -/
def ιA {A : SB Bsp} [IsAffine A.left] (k : A ⟶ T) : F.obj (op A) ≃+ H.obj (op (overT k)) :=
  (exA hH hF e0 k).choose

lemma ιA_smul {A : SB Bsp} [IsAffine A.left] (k : A ⟶ T) (r : (OB Bsp).obj (op A))
    (x : F.obj (op A)) : ιA hH hF e0 k (r • x) =
      (show (GB.overO T.left).obj (op (overT k)) from r) • ιA hH hF e0 k x :=
  (exA hH hF e0 k).choose_spec.1 r x

lemma ιA_base {A : SB Bsp} [IsAffine A.left] (k : A ⟶ T) (x : F.obj (op T)) :
    ιA hH hF e0 k (F.map k.op x) = H.map (mpT k (𝟙 T) k (Category.comp_id k)).op (e0.e x) :=
  (exA hH hF e0 k).choose_spec.2 x

lemma ιA_nat {A A' : SB Bsp} [IsAffine A.left] [IsAffine A'.left] (s : A' ⟶ A) (k : A ⟶ T)
    (k' : A' ⟶ T) (hs : s ≫ k = k') (y : F.obj (op A)) :
    ιA hH hF e0 k' (F.map s.op y) = H.map (mpT s k k' hs).op (ιA hH hF e0 k y) := by
  subst hs
  haveI : IsAffine (overT k).left := ‹IsAffine A.left›
  refine bc_induction _ _ _ (hF.base_change k) (P := fun y =>
    ιA hH hF e0 (s ≫ k) (F.map s.op y) = H.map (mpT s k (s ≫ k) rfl).op (ιA hH hF e0 k y))
    ?_ ?_ ?_ ?_ y
  · simp
  · intro x
    have e1 : F.map s.op (F.map k.op x) = F.map (s ≫ k).op x := by
      rw [op_comp, F.map_comp]
    rw [e1, ιA_base, ιA_base, mp_mp]
  · intro c y hy
    change ιA hH hF e0 (s ≫ k) (F.map s.op (c • y)) = H.map (mpT s k (s ≫ k) rfl).op (ιA hH hF e0 k (c • y))
    rw [F.map_smul, ιA_smul, ιA_smul, H.map_smul, hy]
    rfl
  · intro y z hy hz
    simp only [map_add, hy, hz]

/-- The value over `U → T` of the identification, by gluing over affine schemes. -/
theorem exFwd {U : SB Bsp} (u : U ⟶ T) (x : F.obj (op U)) :
    ∃ y : H.obj (op (overT u)), ∀ (A : SB Bsp) (a : A ⟶ U) (k : A ⟶ T) (hk : a ≫ u = k)
      [IsAffine A.left], H.map (mpT a u k hk).op y = ιA hH hF e0 k (F.map a.op x) :=
  glueH hH u (fun A a k _ _ => ιA hH hF e0 k (F.map a.op x)) (by
    intro A A' s a k hk a' k' hk' _ _ hs hs'
    subst hs
    rw [← ιA_nat hH hF e0 s k k' hs', op_comp, F.map_comp])

/-- Forward map. -/
def fwd {U : SB Bsp} (u : U ⟶ T) (x : F.obj (op U)) : H.obj (op (overT u)) :=
  (exFwd hH hF e0 u x).choose

lemma fwd_spec {U : SB Bsp} (u : U ⟶ T) (x : F.obj (op U)) (A : SB Bsp) (a : A ⟶ U) (k : A ⟶ T)
    (hk : a ≫ u = k) [IsAffine A.left] :
    H.map (mpT a u k hk).op (fwd hH hF e0 u x) = ιA hH hF e0 k (F.map a.op x) :=
  (exFwd hH hF e0 u x).choose_spec A a k hk

/-- Inverse map. -/
def bwd {U : SB Bsp} (u : U ⟶ T) (y : H.obj (op (overT u))) : F.obj (op U) :=
  glueV hF U (fun A a _ => (ιA hH hF e0 (a ≫ u)).symm (H.map (mpT a u _ rfl).op y)) (by
    intro A A' s a _ _
    refine (ιA hH hF e0 ((s ≫ a) ≫ u)).injective ?_
    rw [AddEquiv.apply_symm_apply, ιA_nat hH hF e0 s (a ≫ u) _ (by simp), AddEquiv.apply_symm_apply,
      mp_mp])

lemma bwd_spec {U : SB Bsp} (u : U ⟶ T) (y : H.obj (op (overT u))) (A : SB Bsp) (a : A ⟶ U)
    [IsAffine A.left] :
    F.map a.op (bwd hH hF e0 u y) = (ιA hH hF e0 (a ≫ u)).symm (H.map (mpT a u _ rfl).op y) :=
  glueV_spec hF U _ _ A a

/-- **`IsQCoh` gives the local datum over an affine `T`**, from an identification over `T`. -/
def localOfTop (G : T.left.Modules) (hG : G.IsQuasicoherent) (hH : AlgMag.S9.IsQCoh (assocPMod G))
    (e0 : TopIso (T := T) F (assocPMod G)) : LocalAssoc F T :=
  { G := G
    qc := hG
    ι := fun {U} u =>
      { toFun := fwd hH hF e0 u
        invFun := bwd hH hF e0 u
        left_inv := fun x => by
          refine sep_affine hF U fun A a _ => ?_
          rw [bwd_spec, AddEquiv.symm_apply_eq, fwd_spec]
        right_inv := fun y => by
          refine sep_aff hH u fun A a _ => ?_
          rw [fwd_spec, bwd_spec, AddEquiv.apply_symm_apply]
        map_add' := fun x y => by
          refine sep_aff hH u fun A a _ => ?_
          rw [map_add, fwd_spec, fwd_spec, fwd_spec, map_add, map_add] }
    smul := fun {U} u r x => by
      refine sep_aff hH u fun A a _ => ?_
      change (assocPMod G).map _ (fwd hH hF e0 u (r • x)) = (assocPMod G).map _ ((show (GB.overO T.left).obj (op (overT u)) from r) • fwd hH hF e0 u x)
      rw [(assocPMod G).map_smul, fwd_spec, fwd_spec, F.map_smul, ιA_smul]
      rfl
    nat := fun {U U'} s u x => by
      refine sep_aff hH (s ≫ u) fun A a _ => ?_
      change (assocPMod G).map _ (fwd hH hF e0 (s ≫ u) (F.map s.op x)) =
        (assocPMod G).map _ ((assocPMod G).map (mpT s u (s ≫ u) rfl).op (fwd hH hF e0 u x))
      rw [fwd_spec, mp_mp, fwd_spec, op_comp, F.map_comp] }

end Transport

/-- **`IsQCoh F` gives the local datum of Tag 03DX (1) over every affine `T`** (the converse of
`AlgMag.S9BF.isQCoh_of_local`, on affine objects). The module on `T` is `F(T)^~`. -/
theorem localAssoc_of_isQCoh {F : PMod (OB Bsp)} (hF : IsQCoh F) (T : SB Bsp) [IsAffine T.left] :
    Nonempty (LocalAssoc F T) := by
  letI : Module Γ(T.left, ⊤) (F.obj (op T)) := F.mod (op T)
  obtain ⟨G, hG, e, he⟩ := exists_qc_top T.left (F.obj (op T))
  obtain ⟨e', he'⟩ := exists_top_pullback G (SB.Hom.left (𝟙 T)) (SB.id_left T)
  haveI := hG
  have hH := isQCoh_assocPMod G
  let e0 : TopIso (T := T) F (assocPMod G) :=
    { e := e.trans e'
      smul := fun (r : Γ(T.left, ⊤)) x => by
        change e' (e (r • x)) = r • e' (e x)
        rw [he, he'] }
  exact ⟨localOfTop hF G hG hH e0⟩

/-- The base change property of `IsQCoh` over the affine `T`, from the local datum over `T`. -/
theorem baseChange_of_local {F : PMod (OB Bsp)} {T T' : SB Bsp} (D : LocalAssoc F T) (s : T' ⟶ T)
    [hT : IsAffine T.left] [hT' : IsAffine T'.left] :
    IsBC ((OB Bsp).map s.op).hom (F.map s.op) (F.map_smul s.op) := by
  haveI := D.qc
  let c : Over.mk (SB.Hom.left (s ≫ 𝟙 T)) ⟶ Over.mk (SB.Hom.left (𝟙 T)) :=
    Over.homMk (SB.Hom.left s) (SB.comp_left s (𝟙 T)).symm
  haveI : IsAffine (Over.mk (SB.Hom.left (𝟙 T))).left := hT
  haveI : IsAffine (Over.mk (SB.Hom.left (s ≫ 𝟙 T))).left := hT'
  have hb := (isQCoh_assocPMod D.G).base_change c
  exact @isBC_transport.{u} ((OB Bsp).obj (op T)) ((OB Bsp).obj (op T')) (F.obj (op T)) (F.obj (op T'))
    ((assocPMod D.G).obj (op (Over.mk (SB.Hom.left (𝟙 T)))))
    ((assocPMod D.G).obj (op (Over.mk (SB.Hom.left (s ≫ 𝟙 T))))) _ _ _ (F.mod _) _ (F.mod _)
    ((assocPMod D.G).grp _) ((assocPMod D.G).mod (op (Over.mk (SB.Hom.left (𝟙 T)))))
    ((assocPMod D.G).grp _) ((assocPMod D.G).mod (op (Over.mk (SB.Hom.left (s ≫ 𝟙 T)))))
    _ _ _ _ _ (D.ι (𝟙 T)) (D.smul (𝟙 T)) (D.ι (s ≫ 𝟙 T)) (D.smul (s ≫ 𝟙 T))
    (fun x => D.nat s (𝟙 T) x) hb

/-- **`IsQCoh` characterized by Stacks quasi-coherent modules**: `F` is `IsQCoh` if and only if it is
a Zariski sheaf and, over each affine `T`, it is the associated module of a Stacks quasi-coherent
module on `T` (compare `BigFppfOver.HasLocalAssociatedModule`, Tag 03DX (1)). -/
theorem isQCoh_iff_affine_local (F : PMod (OB Bsp)) :
    IsQCoh F ↔
      (∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left) (R : Sieve T),
        coverSieve T 𝒰 ≤ R → Presieve.IsSheafFor F.toPresheaf R.arrows) ∧
      ∀ (T : SB Bsp) [IsAffine T.left], Nonempty (LocalAssoc F T) := by
  refine ⟨fun h => ⟨h.sheaf, fun T _ => localAssoc_of_isQCoh h T⟩, fun h => ⟨h.1, ?_⟩⟩
  intro T T' s _ _
  obtain ⟨D⟩ := h.2 T
  exact baseChange_of_local D s

/-- **Nonzero witness.** A module pulled back from a scheme `Y` under `B` (for `Y = S`, every
quasi-coherent module on `S`) has the local datum over every affine `T`. -/
theorem localAssoc_restr {Y : Scheme.{u}} (P : ToScheme Bsp Y) (G : Y.Modules) [G.IsQuasicoherent]
    (T : SB Bsp) [IsAffine T.left] : Nonempty (LocalAssoc (restr P (assocPMod G)) T) :=
  localAssoc_of_isQCoh (isQCoh_of_scheme P G) T

/-! ### Proposition 9.1, with its canonical map -/

section Prop91
variable {X : (SB Bsp)ᵒᵖ ⥤ Type u} (r : AffOver X) {G : PMod (OB Bsp)}

variable (G X) in
/-- `(f_* f^* G)(T)`, for `f : X → B`: sections of `G` over the points of `T ×_B X`. -/
@[ext]
structure PushSec (T : SB Bsp) where
  /-- the value at a point `(t, x)` of `T ×_B X` -/
  val : ∀ {T' : SB Bsp} (_ : T' ⟶ T), X.obj (op T') → G.obj (op T')
  naturality : ∀ {T' T'' : SB Bsp} (s : T'' ⟶ T') (t : T' ⟶ T) (x : X.obj (op T')),
    val (s ≫ t) (X.map s.op x) = G.map s.op (val t x)

/-- For `T` affine, `T ×_B X` is the affine scheme `r.P T`: `(f_* f^* G)(T) = G(T ×_B X)`. -/
def pushSecEquiv (T : SB Bsp) [IsAffine T.left] : PushSec X G T ≃ G.obj (op (r.P T)) where
  toFun σ := σ.val (r.pr T) (r.univ T)
  invFun g :=
    { val := fun t x => G.map (r.lift t x).op g
      naturality := fun s t x => by
        rw [← G.map_comp, ← op_comp, AffOver.comp_lift] }
  left_inv σ := by
    ext T' t x
    change G.map _ (σ.val (r.pr T) (r.univ T)) = σ.val t x
    rw [← σ.naturality, r.lift_pr, r.lift_univ]
  right_inv g := by
    change G.map (r.lift (r.pr T) (r.univ T)).op g = g
    rw [AffOver.lift_pr_univ, op_id, G.map_id]

/-- **Proposition 9.1**, with the printed canonical map `G ⊗_𝒪 𝒜 → f_* f^* G`. For `T` affine,
`𝒜(T) = (f_* 𝒪_X)(T) = Γ(T ×_B X)`, and the map `a ⊗ g ↦ ((t, x) ↦ (t, x)^*(a) • t^*(g))` is bijective.
The bijectivity is the base change property of `G`; the sheaf tensor product is not formed, since a
map of quasi-coherent modules is determined on affine objects. -/
theorem prop91_canonical (hG : IsQCoh G) (T : SB Bsp) [IsAffine T.left] :
    letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
    ∃ Φ : ((OB Bsp).obj (op (r.P T)) ⊗[(OB Bsp).obj (op T)] G.obj (op T)) ≃ PushSec X G T,
      (∀ p q {T' : SB Bsp} (t : T' ⟶ T) (x : X.obj (op T')),
        (Φ (p + q)).val t x = (Φ p).val t x + (Φ q).val t x) ∧
      ∀ (a : (OB Bsp).obj (op (r.P T))) (g : G.obj (op T)) {T' : SB Bsp} (t : T' ⟶ T)
        (x : X.obj (op T')),
        (Φ (a ⊗ₜ g)).val t x = ((OB Bsp).map (r.lift t x).op).hom a • G.map t.op g := by
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  letI : Module ((OB Bsp).obj (op T)) (G.obj (op (r.P T))) :=
    Module.compHom _ ((OB Bsp).map (r.pr T).op).hom
  haveI : IsScalarTower ((OB Bsp).obj (op T)) ((OB Bsp).obj (op (r.P T))) (G.obj (op (r.P T))) :=
    ⟨fun c s x => by
      change (((OB Bsp).map (r.pr T).op).hom c * s) • x = ((OB Bsp).map (r.pr T).op).hom c • s • x
      rw [mul_smul]⟩
  have hb : IsBaseChange ((OB Bsp).obj (op (r.P T)))
      ({ toFun := G.map (r.pr T).op, map_add' := (G.map (r.pr T).op).map_add,
         map_smul' := G.map_smul (r.pr T).op } :
        G.obj (op T) →ₗ[(OB Bsp).obj (op T)] G.obj (op (r.P T))) := hG.base_change (r.pr T)
  refine ⟨hb.equiv.toEquiv.trans (pushSecEquiv r T).symm, ?_, ?_⟩
  · intro p q T' t x
    change G.map _ (hb.equiv (p + q)) = G.map _ (hb.equiv p) + G.map _ (hb.equiv q)
    rw [map_add, map_add]
  · intro a g T' t x
    change G.map _ (hb.equiv (a ⊗ₜ g)) = _
    rw [IsBaseChange.equiv_tmul]
    change G.map (r.lift t x).op (a • G.map (r.pr T).op g) = _
    rw [G.map_smul, ← G.map_comp, ← op_comp, r.lift_pr]

/-- **Proposition 9.1**, the base change, from the local datum of Tag 03DX over `T` alone: here the
content is Tag 03DX (through `baseChange_of_local`), not the definition of `IsQCoh`. -/
theorem prop91_of_local {T : SB Bsp} [IsAffine T.left] (D : LocalAssoc G T) :
    IsBC ((OB Bsp).map (r.pr T).op).hom (G.map (r.pr T).op) (G.map_smul (r.pr T).op) :=
  baseChange_of_local D (r.pr T)

end Prop91

/-! ### Genuine affine morphisms and monoid spaces -/

section Spaces
variable {X X' : (SB Bsp)ᵒᵖ ⥤ Type u}

/-- `AffOver` transports along an isomorphism of presheaves. -/
def affOverOfIso (r : AffOver X) (e : X ≅ X') : AffOver X' where
  P T _ := r.P T
  aff T _ := r.aff T
  pr T _ := r.pr T
  univ T _ := e.hom.app _ (r.univ T)
  lift t x := r.lift t (e.inv.app _ x)
  lift_pr t x := r.lift_pr t _
  lift_univ {T W} _ t x := by
    rw [nat_apply, r.lift_univ]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app (op W)) x
  uniq {T W} _ g g' h1 h2 := by
    refine r.uniq g g' h1 ?_
    rw [nat_apply, nat_apply] at h2
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app (op W))).1 h2

/-- **Proposition 9.9** for an affine morphism of algebraic spaces `p : X → B`. -/
def prop99_space {F G : PMod (OB Bsp)} {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp)
    (hp : Space.IsAffineHom Bs S hS p) (hG : IsQCoh G) :
    HomAt F G (Vp p) ≃ HomPush F G (affOverOfIsAffineHom p hp) :=
  homAtEquivHomPush _ hG

/-- **Proposition 9.10** for an affine monoid algebraic space `p : Y → B`: `H` is the monoid functor
on the site of `B` whose underlying presheaf is `Y` over `B`. -/
def prop910_space {F : PMod (OB Bsp)} {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} (p : Y ⟶ Bsp)
    (hp : Space.IsAffineHom Bs S hS p) {H : (SB Bsp)ᵒᵖ ⥤ MonCat.{u}} (e : Vp p ≅ H ⋙ forget MonCat)
    (hF : IsQCoh F) :
    HModule H F ≃ CoactionAff F (affOverOfIso (affOverOfIsAffineHom p hp) e) :=
  hModuleEquivCoaction _ hF

end Spaces

/-! ### `𝔸(M)_B`: Propositions 9.10 and 9.11 linked -/

section AM
variable {F : PMod (OB Bsp)} {M : Type u} [AddCommMonoid M] [Countable M]

/-- **Propositions 9.10 and 9.11 linked**, for `H = 𝔸(M)_B`: comodule structures `F → F ⊗ 𝒜` are the
families `(ρ_m)` of Proposition 9.11 (corrected wording). -/
def coactionEquivDecomp (hF : IsQCoh F) : CoactionAff F (affOverHm (M := M) (Bsp := Bsp)) ≃ Decomp F M :=
  (hModuleEquivCoaction _ hF).symm.trans (hModuleEquivDecomp hF)

/-- The comodule map of Proposition 9.10 is `ρ(v) = ∑ ρ_m(v) X^m`: on `T` affine, it is the element
`rhoV` of Proposition 9.11 evaluated on the universal point of `T ×_B 𝔸(M)`. -/
theorem coaction_eq_rhoV (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) (T : SB Bsp) [IsAffine T.left]
    (v : F.obj (op T)) :
    ((hModuleEquivCoaction (affOverHm (M := M) (Bsp := Bsp)) hF A).ρ.app T v) =
      evalE (Ypr M T) (univ M T) (rhoV A hF v) :=
  smul_eq_evalE hF v (Ypr M T) (univ M T)

/-- The components of the family of Proposition 9.11 are the coefficients of `ρ(v)`. -/
theorem decomp_comp_eq_coeff (hF : IsQCoh F) (A : HModule (Hm M Bsp) F) (m : M) (T : SB Bsp)
    [IsAffine T.left] (v : F.obj (op T)) :
    (hModuleEquivDecomp hF A).comp m T v = rhoV A hF v m :=
  compOf_affine hF A m v

variable {n : ℕ} {Y : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u}

/-- **Proposition 9.12** over a quasi-compact algebraic space `Y → B`: the literal direct sum. -/
theorem prop912_space (hF : IsQCoh F) (p : Y ⟶ Bsp) (hY : IsAlgebraicSpace Bs S hS Y)
    (hq : Space.IsQuasiCompactSpace Bs S hS Y) :
    Nonempty (CochainV F M (Vp p) n ≃ ((Fin n → M) →₀ SecF F (Vp p))) :=
  (qcCoverOfQuasiCompact p hY hq).map (cochainVEquivFinsupp hF)

/-- **Proposition 9.13 and Remark 9.14**, for the action given by a comodule structure (Proposition
9.10) over any `V`. -/
theorem prop913_of_coaction (hF : IsQCoh F) (R : CoactionAff F (affOverHm (M := M) (Bsp := Bsp)))
    {V : (SB Bsp)ᵒᵖ ⥤ Type u} (c : CochainV F M V (n + 1))
    (hc : ∀ {T : SB Bsp} (t : V.obj (op T)) g,
      (deltaV ((hModuleEquivCoaction _ hF).symm R) c).app t g = 0) :
    ∃ e : CochainV F M V n, deltaV ((hModuleEquivCoaction _ hF).symm R) e = c :=
  exists_deltaV_eq hF _ c hc

end AM

end AlgMag.S9BR

#print axioms AlgMag.S9BR.localAssoc_of_isQCoh
#print axioms AlgMag.S9BR.isQCoh_iff_affine_local
#print axioms AlgMag.S9BR.localAssoc_restr
#print axioms AlgMag.S9BR.pushSecEquiv
#print axioms AlgMag.S9BR.prop91_canonical
#print axioms AlgMag.S9BR.prop99_space
#print axioms AlgMag.S9BR.prop910_space
#print axioms AlgMag.S9BR.coactionEquivDecomp
#print axioms AlgMag.S9BR.coaction_eq_rhoV
#print axioms AlgMag.S9BR.decomp_comp_eq_coeff
#print axioms AlgMag.S9BR.prop912_space
#print axioms AlgMag.S9BR.prop913_of_coaction
#print axioms AlgMag.S9BR.exists_qc_top
#print axioms AlgMag.S9BR.glueH
#print axioms AlgMag.S9BR.localOfTop
#print axioms AlgMag.S9BR.baseChange_of_local
#print axioms AlgMag.S9BR.prop91_of_local
