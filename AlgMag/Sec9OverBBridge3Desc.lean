/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9OverBBridge3Geom

/-!
# Faithfully flat descent of the values `Γ(A) ⊗_{Γ(V)} 𝓜(V)`; `ZDesc` holds

`FDesc`: descent along a finite flat surjective family of affines (Stacks 023M, through
`isSheafFor_of_cartesian`), from which `zDesc`, and `eval_bijective` holds with no hypothesis.
-/

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.B3

open AlgMag.S9B AlgMag.S9 AlgebraicGeometry.Space

/-! ### `S' ⊗_R M` is the base change of `S ⊗_R M` -/

section Alg
variable {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M] [Module R M]

lemma pure_cancel [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] (x : S ⊗[R] M) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M ((1 : S') ⊗ₜ[S] x) =
      TensorProduct.map (AlgHom.toLinearMap (IsScalarTower.toAlgHom R S S')) LinearMap.id x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]
  | tmul s m => simp [Algebra.smul_def]

set_option maxHeartbeats 1000000 in
theorem bc_isBC (f : R →+* S) (g : S →+* S') (f' : R →+* S') (c : g.comp f = f'.comp (RingHom.id R))
    (φ : M →+ M) (hφ₀ : φ = AddMonoidHom.id M) (hφ : ∀ r m, φ (r • m) = RingHom.id R r • φ m) :
    IsBC g (bcMap (RingHom.id R) g c φ hφ) (bcMap_smul (RingHom.id R) g c φ hφ) := by
  subst hφ₀
  have hf' : f' = g.comp f := by rw [c]; rfl
  subst hf'
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI mS : Module S (BCv (g.comp f) M) := Module.compHom _ g
  haveI : IsScalarTower S S' (BCv (g.comp f) M) := ⟨fun r s x => by
    change (g r * s) • x = g r • s • x
    rw [mul_smul]⟩
  let L : BCv f M →ₗ[S] BCv (g.comp f) M :=
    ⟨⟨bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ,
      (bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ).map_add⟩,
      bcMap_smul (RingHom.id R) g c (AddMonoidHom.id M) hφ⟩
  change IsBaseChange S' L
  refine IsBaseChange.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' M) fun x => ?_
  have hk : ∀ s m, bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ (BCv.tm f s m) = BCv.tm (g.comp f) (g s) m :=
    fun s m => bcMap_tm (RingHom.id R) g c _ hφ s m
  exact (pure_cancel x).trans (BCv.induction f
    (P := fun x : BCv f M => TensorProduct.map (AlgHom.toLinearMap (IsScalarTower.toAlgHom R S S')) LinearMap.id x
      = bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ x)
    ((map_zero _).trans (map_zero (bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ)).symm)
    (fun s m => (TensorProduct.map_tmul _ _ _ _).trans (hk s m).symm)
    (fun a b ha hb => (map_add _ _ _).trans ((congrArg₂ _ ha hb).trans
      (map_add (bcMap (RingHom.id R) g c (AddMonoidHom.id M) hφ) a b).symm)) x)

end Alg

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace Bs S hS Bsp}
  (𝓜 : Space.Modules.{u, u} Bs S hS Bsp hB)

lemma Mres_id (V : AffineEtale Bs S hS Bsp) : Mres 𝓜 (𝟙 V) = AddMonoidHom.id _ := by
  ext m
  have key : ∀ (k : op V.obj ⟶ op V.obj), k = 𝟙 _ → ((Pm 𝓜).map k).hom m = m := by
    rintro k rfl
    exact congrArg (fun φ => (ConcreteCategory.hom φ) m) ((Pm 𝓜).presheaf.map_id (op V.obj))
  exact key _ (by simp)

lemma ρ_id {A : SB Bsp} {V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V}
    (hc : v ≫ cBm (𝟙 V) = 𝟙 A ≫ v) (z : Dv 𝓜 v) : ρ 𝓜 (𝟙 A) (𝟙 V) hc z = z := by
  refine BCv.induction _ (P := fun z => ρ 𝓜 (𝟙 A) (𝟙 V) hc z = z) (map_zero _) (fun a m => ?_)
    (fun x y hx hy => by rw [map_add, hx, hy]) z
  simp only [ρ, bcMap_tm]
  have e1 : ((OB Bsp).map (𝟙 A).op).hom a = a := by rw [op_id, (OB Bsp).map_id]; rfl
  have e2 : Mres 𝓜 (𝟙 V) m = m := by rw [Mres_id]; rfl
  rw [e1, e2]

/-- `ρ` along a morphism of the base with fixed chart is a base change. -/
theorem ρ_isBC {A' A : SB Bsp} {V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v' : A' ⟶ cB V}
    (s : A' ⟶ A) (hc : v' ≫ cBm (𝟙 V) = s ≫ v) :
    IsBC ((OB Bsp).map s.op).hom (ρ 𝓜 s (𝟙 V) hc) (fun r z => bcMap_smul _ _ _ _ _ r z) := by
  have key : ∀ (h : (rc V) →+* (rc V)) (hh : h = RingHom.id _)
      (c : ((OB Bsp).map s.op).hom.comp ((OB Bsp).map v.op).hom = ((OB Bsp).map v'.op).hom.comp h)
      (hφ : ∀ r m, Mres 𝓜 (𝟙 V) (r • m) = h r • Mres 𝓜 (𝟙 V) m),
      IsBC ((OB Bsp).map s.op).hom (bcMap h ((OB Bsp).map s.op).hom c (Mres 𝓜 (𝟙 V)) hφ)
        (bcMap_smul h _ c _ hφ) := by
    rintro h rfl c hφ
    exact bc_isBC _ _ _ c _ (Mres_id 𝓜 V) hφ
  exact key _ (by rw [cBm_id]; change ((OB Bsp).map (𝟙 (op (cB V)))).hom = _; rw [(OB Bsp).map_id]; rfl) _ _

/-! ### Pullbacks over `B` -/

/-- The underlying scheme, as a functor. -/
def sbL : SB Bsp ⥤ Scheme.{u} where
  obj T := T.left
  map f := SB.Hom.left f
  map_id := SB.id_left
  map_comp := SB.comp_left

section Pb
variable {X Y Z : SB Bsp} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The fibre product over `B`. -/
def sbPb : SB Bsp := ⟨pullback f.hom g.hom, Bsp.map (pullback.fst f.hom g.hom).op X.pt⟩

/-- The first projection. -/
def sbFst : sbPb f g ⟶ X := ⟨pullback.fst f.hom g.hom, rfl⟩

/-- The second projection. -/
def sbSnd : sbPb f g ⟶ Y := ⟨pullback.snd f.hom g.hom, by
  change Bsp.map (pullback.snd f.hom g.hom).op Y.pt = Bsp.map (pullback.fst f.hom g.hom).op X.pt
  rw [← g.w, ← f.w, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    pullback.condition]⟩

theorem sb_isPullback : IsPullback (sbFst f g) (sbSnd f g) f g := by
  refine ⟨⟨SB.Hom.ext pullback.condition⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => ⟨pullback.lift s.fst.hom s.snd.hom (congrArg SB.Hom.hom s.condition), ?_⟩)
    (fun s => SB.Hom.ext (pullback.lift_fst _ _ _)) (fun s => SB.Hom.ext (pullback.lift_snd _ _ _))
    (fun s m h1 h2 => SB.Hom.ext ?_)⟩⟩
  · have e : ∀ (k : s.pt.obj ⟶ pullback f.hom g.hom), k ≫ pullback.fst f.hom g.hom = s.fst.hom →
        Bsp.map k.op (Bsp.map (pullback.fst f.hom g.hom).op X.pt) = s.pt.pt := by
      intro k hk
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, hk]
      exact s.fst.w
    exact e _ (pullback.lift_fst _ _ _)
  · exact pullback.hom_ext ((congrArg SB.Hom.hom h1).trans (pullback.lift_fst _ _ _).symm)
      ((congrArg SB.Hom.hom h2).trans (pullback.lift_snd _ _ _).symm)

theorem sb_left : IsPullback (SB.Hom.left (sbFst f g)) (SB.Hom.left (sbSnd f g)) (SB.Hom.left f)
    (SB.Hom.left g) :=
  (IsPullback.of_hasPullback f.hom g.hom).map (BigFppfOver.toScheme Bs S hS)

end Pb

instance : HasPullbacks (SB Bsp) := by
  haveI : ∀ {X Y Z : SB Bsp} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g) :=
    fun {_ _ _ f g} => (sb_isPullback f g).hasPullback
  exact hasPullbacks_of_hasLimit_cospan _

/-- A pullback square over `B` is a pullback of schemes. -/
theorem isPullback_left {P X Y Z : SB Bsp} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) :
    IsPullback (SB.Hom.left a) (SB.Hom.left b) (SB.Hom.left f) (SB.Hom.left g) := by
  let e := h.isoIsPullback _ _ (sb_isPullback f g)
  refine IsPullback.of_iso (sb_left f g) (sbL.mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · change _ ≫ 𝟙 _ = SB.Hom.left e.inv ≫ _
    rw [Category.comp_id, ← SB.comp_left, h.isoIsPullback_inv_fst]
  · change _ ≫ 𝟙 _ = SB.Hom.left e.inv ≫ _
    rw [Category.comp_id, ← SB.comp_left, h.isoIsPullback_inv_snd]

theorem isAffine_of_isPullback {P X Y Z : SB Bsp} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hX : IsAffine X.left) (hY : IsAffine Y.left) (hZ : IsAffine Z.left) :
    IsAffine P.left := by
  have e := isPullback_left h
  exact IsAffine.of_isIso e.isoPullback.hom

theorem isPushout_OB {P X Y Z : SB Bsp} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hX : IsAffine X.left) (hY : IsAffine Y.left) (hZ : IsAffine Z.left) :
    IsPushout ((OB Bsp).map f.op) ((OB Bsp).map g.op) ((OB Bsp).map a.op) ((OB Bsp).map b.op) := by
  haveI := isAffine_of_isPullback h hX hY hZ
  exact isPushout_appTop_of_isPullback (isPullback_left h)

/-! ### Descent -/

lemma ρ_smul {A' A : SB Bsp} {V' V : AffineEtale Bs S hS Bsp} {v : A ⟶ cB V} {v' : A' ⟶ cB V'}
    (s : A' ⟶ A) (φ : V' ⟶ V) (hc : v' ≫ cBm φ = s ≫ v) (r : (OB Bsp).obj (op A)) (z : Dv 𝓜 v) :
    ρ 𝓜 s φ hc (r • z) = ((OB Bsp).map s.op).hom r • ρ 𝓜 s φ hc z :=
  bcMap_smul _ _ (square_ring s φ hc) _ (Mres_smul 𝓜 φ) r z

section Descent

variable {A : SB Bsp} {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V)

lemma sqO {X Y : Over A} (f : Y ⟶ X) : (Y.hom ≫ v) ≫ cBm (𝟙 V) = f.left ≫ X.hom ≫ v := by
  rw [cBm_id, Category.comp_id, ← Category.assoc, Over.w f]

/-- The values over the objects of `Over A`. -/
def MpA : (Over A)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (Dv 𝓜 (X.unop.hom ≫ v))
  map {X Y} f := AddCommGrpCat.ofHom (ρ 𝓜 f.unop.left (𝟙 V) (sqO v f.unop))
  map_id X := by
    ext z
    change ρ 𝓜 (𝟙 X).unop.left (𝟙 V) (sqO v (𝟙 X).unop) z = z
    exact (ρ_congr 𝓜 (by simp) rfl _ (sq1' _) z).trans (ρ_id 𝓜 _ z)
  map_comp {X Y Z} f g := by
    ext z
    change ρ 𝓜 (f ≫ g).unop.left (𝟙 V) (sqO v (f ≫ g).unop) z = _
    refine Eq.trans ?_ (ρ_comp 𝓜 f.unop.left (𝟙 V) (sqO v f.unop) g.unop.left (𝟙 V) (sqO v g.unop) z).symm
    exact ρ_congr 𝓜 (by simp) (by simp) _ _ z

/-- The rings over `Over A`. -/
abbrev RA (A : SB Bsp) : (Over A)ᵒᵖ ⥤ CommRingCat.{u} := (Over.forget A).op ⋙ OB Bsp

instance (X : (Over A)ᵒᵖ) : Module ((RA A ⋙ forget₂ CommRingCat RingCat).obj X) ((MpA 𝓜 v).obj X) :=
  inferInstanceAs (Module ((OB Bsp).obj (op X.unop.left)) (Dv 𝓜 (X.unop.hom ≫ v)))

/-- The values as a presheaf of modules. -/
def MA : PresheafOfModules.{u} (RA A ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.ofPresheaf (MpA 𝓜 v) (fun {X Y} f r z => ρ_smul 𝓜 f.unop.left (𝟙 V) (sqO v f.unop) r z)

theorem MA_cart {X Y : (Over A)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange (R := RA A) (MA 𝓜 v) f) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact AlgMag.B2.cart_of_isBC (R := RA A) (MA 𝓜 v) f (ρ_isBC 𝓜 f.unop.left (sqO v f.unop))

end Descent

/-- **Descent along a finite flat surjective family of affines.** -/
theorem FDesc {A : SB Bsp} (hA : IsAffine A.left) {V : AffineEtale Bs S hS Bsp} (v : A ⟶ cB V)
    {I : Type*} [Finite I] (Ai : I → SB Bsp) (s : ∀ i, Ai i ⟶ A) (hAi : ∀ i, IsAffine (Ai i).left)
    (hfl : ∀ i, Flat (SB.Hom.left (s i))) (hsu : ∀ x : A.left, ∃ i, x ∈ Set.range (SB.Hom.left (s i)))
    (y : ∀ i, Dv 𝓜 (s i ≫ v))
    (hy : ∀ (i j : I) {A'' : SB Bsp} (_ : IsAffine A''.left) (p : A'' ⟶ Ai i) (q : A'' ⟶ Ai j)
      (e : p ≫ s i = q ≫ s j) (v'' : A'' ⟶ cB V) (h1 : v'' ≫ cBm (𝟙 V) = p ≫ s i ≫ v)
      (h2 : v'' ≫ cBm (𝟙 V) = q ≫ s j ≫ v),
      ρ 𝓜 p (𝟙 V) h1 (y i) = ρ 𝓜 q (𝟙 V) h2 (y j)) :
    ∃! z : Dv 𝓜 v, ∀ i, ρ 𝓜 (s i) (𝟙 V) (sq1 (s i) v) z = y i := by
  let U : Over A := Over.mk (𝟙 A)
  let Vi : I → Over A := fun i => Over.mk (s i)
  let f : ∀ i, Vi i ⟶ U := fun i => Over.homMk (s i) (Category.comp_id _)
  let W : I → I → Over A := fun i j => Over.mk (sbFst (s i) (s j) ≫ s i)
  let pr : ∀ i j, W i j ⟶ Vi i := fun i j => Over.homMk (sbFst (s i) (s j))
  let qr : ∀ i j, W i j ⟶ Vi j := fun i j => Over.homMk (sbSnd (s i) (s j))
    (sb_isPullback (s i) (s j)).w.symm
  have hpq : ∀ i j, pr i j ≫ f i = qr i j ≫ f j := fun i j =>
    Over.OverMorphism.ext (sb_isPullback (s i) (s j)).w
  have hff : (RingHom.pi (fun i => ((RA A).map (f i).op).hom)).FaithfullyFlat := by
    haveI := hA; haveI := hAi; haveI := hfl
    exact Scheme.faithfullyFlat_pi_appTop (fun i => (Ai i).left) (fun i => SB.Hom.left (s i))
      (fun x => by obtain ⟨i, y, hy⟩ := hsu x; exact ⟨i, y, hy⟩)
  have hsh := Stacks.PresheafOfModules.isSheafFor_of_cartesian (RA A) (MA 𝓜 v) Vi f W pr qr hpq hff
    (fun i j => isPushout_OB (sb_isPullback (s i) (s j)) (hAi i) (hAi j) hA)
    (fun g => MA_cart 𝓜 v g)
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨t, ht, htu⟩ := hsh (fun i => (y i : Dv 𝓜 (s i ≫ v))) (by
    intro i j Z gi gj hg
    have hg' : gi.left ≫ s i = gj.left ≫ s j := congrArg CommaMorphism.left hg
    have hw := sb_isPullback (s i) (s j)
    let k := hw.lift gi.left gj.left hg'
    have k1 : k ≫ sbFst (s i) (s j) = gi.left := hw.lift_fst _ _ _
    have k2 : k ≫ sbSnd (s i) (s j) = gj.left := hw.lift_snd _ _ _
    have hAW := isAffine_of_isPullback hw (hAi i) (hAi j) hA
    have h0 := hy i j hAW (sbFst (s i) (s j)) (sbSnd (s i) (s j)) hw.w
      (sbFst (s i) (s j) ≫ s i ≫ v) (sq1 _ _) (by
        rw [cBm_id, Category.comp_id, ← Category.assoc, ← Category.assoc, hw.w])
    have hk0 : (Z.hom ≫ v) ≫ cBm (𝟙 V) = k ≫ sbFst (s i) (s j) ≫ s i ≫ v := by
      rw [cBm_id, Category.comp_id, ← Category.assoc, k1]
      exact (congrArg (· ≫ v) (Over.w gi)).symm.trans (Category.assoc _ _ _)
    have hk := congrArg (ρ 𝓜 k (𝟙 V) hk0) h0
    rw [ρ_comp, ρ_comp] at hk
    change ρ 𝓜 gi.left (𝟙 V) (sqO v gi) (y i) = ρ 𝓜 gj.left (𝟙 V) (sqO v gj) (y j)
    exact (ρ_congr 𝓜 k1.symm (by simp) _ _ (y i)).trans
      (hk.trans (ρ_congr 𝓜 k2 (by simp) _ _ (y j))))
  have hb0 : v ≫ cBm (𝟙 V) = 𝟙 A ≫ U.hom ≫ v := by simp [U, cBm_id]
  have hf0 : (U.hom ≫ v) ≫ cBm (𝟙 V) = 𝟙 A ≫ v := by simp [U, cBm_id]
  let back : Dv 𝓜 (U.hom ≫ v) → Dv 𝓜 v := ρ 𝓜 (𝟙 A) (𝟙 V) hb0
  let fwd : Dv 𝓜 v → Dv 𝓜 (U.hom ≫ v) := ρ 𝓜 (𝟙 A) (𝟙 V) hf0
  have hbf : ∀ z, back (fwd z) = z := fun z =>
    (ρ_comp 𝓜 (𝟙 A) (𝟙 V) hf0 (𝟙 A) (𝟙 V) hb0 z).trans
      ((ρ_congr 𝓜 (by simp) (by simp) _ (sq1' v) z).trans (ρ_id 𝓜 _ z))
  refine ⟨back t, fun i => ?_, fun z hz => ?_⟩
  · refine Eq.trans ?_ (ht i)
    exact (ρ_comp 𝓜 (𝟙 A) (𝟙 V) hb0 (s i) (𝟙 V) (sq1 (s i) v) t).trans
      (ρ_congr 𝓜 (Category.comp_id _) (by simp) _ (sqO v (f i)) t)
  · rw [← hbf z]
    refine congrArg back (htu (fwd z) fun i => ?_)
    refine Eq.trans ?_ (hz i)
    exact (ρ_comp 𝓜 (𝟙 A) (𝟙 V) hf0 (f i).left (𝟙 V) (sqO v (f i)) z).trans
      (ρ_congr 𝓜 (Category.comp_id _) (by simp) _ _ z)

/-- A point of a fibre product over `B`. -/
theorem exists_pt_of_isPullback {P X Y Z : SB Bsp} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X.left) (y : Y.left) (e : SB.Hom.left f x = SB.Hom.left g y) :
    ∃ w : P.left, SB.Hom.left a w = x ∧ SB.Hom.left b w = y := by
  have hl := isPullback_left h
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback x y e
  refine ⟨hl.isoPullback.inv z, ?_, ?_⟩
  · rw [← h1, ← hl.isoPullback_inv_fst]; rfl
  · rw [← h2, ← hl.isoPullback_inv_snd]; rfl

theorem flat_of_isPullback {P X Y Z : SB Bsp} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (hg : Flat (SB.Hom.left g)) : Flat (SB.Hom.left a) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_left h).flip hg

/-- **`ZDesc` holds.** -/
theorem zDesc : ZDesc 𝓜 := by
  intro A hA V v ι Ai s hAi hop hsu y hy
  classical
  haveI := hA
  have hfl : ∀ i, Flat (SB.Hom.left (s i)) := fun i => by haveI := hop i; infer_instance
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => Set.range (SB.Hom.left (s i))) (fun i => (hop i).base_open.isOpen_range)
    (fun x _ => Set.mem_iUnion.2 (hsu x))
  have hsu' : ∀ x : A.left, ∃ i : t, x ∈ Set.range (SB.Hom.left (s i)) := fun x => by
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, h⟩ := this
    exact ⟨⟨i, hi⟩, h⟩
  obtain ⟨z, hz, hzu⟩ := FDesc 𝓜 hA v (fun i : t => Ai i) (fun i => s i) (fun i => hAi i) (fun i => hfl i)
    hsu' (fun i => y i) (fun i j _ hA'' p q e v'' h1 h2 => hy i j hA'' p q e v'' h1 h2)
  refine ⟨z, fun i => ?_, fun z' hz' => hzu z' fun j => hz' j⟩
  have hw := fun j : t => sb_isPullback (s i) (s j)
  have uq := FDesc 𝓜 (hAi i) (s i ≫ v) (fun j : t => sbPb (s i) (s j)) (fun j => sbFst (s i) (s j))
    (fun j => isAffine_of_isPullback (hw j) (hAi _) (hAi _) hA)
    (fun j => flat_of_isPullback (hw j) (hfl j))
    (fun x => by
      obtain ⟨j, y, hy⟩ := hsu' (SB.Hom.left (s i) x)
      obtain ⟨w, h1, -⟩ := exists_pt_of_isPullback (hw j) x y hy.symm
      exact ⟨j, w, h1⟩)
    (fun j => ρ 𝓜 (sbFst (s i) (s j)) (𝟙 V) (sq1 _ _) (y i))
    (fun j k _ hA'' p q e v'' h1 h2 => by
      rw [ρ_comp, ρ_comp]
      exact ρ_congr 𝓜 e (rfl) _ _ (y i))
  refine uq.unique (fun j => ?_) (fun j => rfl)
  rw [ρ_comp]
  have e0 : (sbSnd (s i) (s j) : sbPb (s i) (s j) ⟶ Ai j) ≫ s j = sbFst (s i) (s j) ≫ s i := (hw j).w.symm
  have h2 := hz j
  have h3 := congrArg (ρ 𝓜 (sbSnd (s i) (s j)) (𝟙 V) (show (sbFst (s i) (s j) ≫ s i ≫ v) ≫ cBm (𝟙 V) = _ by
    rw [sq1, ← Category.assoc, ← Category.assoc, e0])) h2
  rw [ρ_comp] at h3
  exact (ρ_congr 𝓜 e0.symm rfl _ _ z).trans (h3.trans (hy i j
    (isAffine_of_isPullback (hw j) (hAi _) (hAi _) hA) (sbFst (s i) (s j)) (sbSnd (s i) (s j)) (hw j).w
    (sbFst (s i) (s j) ≫ s i ≫ v) (sq1 _ _) (by
      rw [cBm_id, Category.comp_id, ← Category.assoc, ← Category.assoc, (hw j).w])).symm)

/-- **Over an affine `T` mapping to a chart, a compatible family is its value at that chart.** -/
theorem eval_bijective' (h𝓜 : 𝓜.IsQuasicoherentOnSite) {T : SB Bsp} (hT : IsAffine T.left)
    {V₀ : AffineEtale Bs S hS Bsp} (τ : T ⟶ cB V₀) :
    Function.Bijective (fun x : Fam 𝓜 T => x.val hT (𝟙 T) τ) :=
  eval_bijective (cartesian_of_qc 𝓜 h𝓜) (zDesc 𝓜) geo hT τ

end AlgMag.B3
