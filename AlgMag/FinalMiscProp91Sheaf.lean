/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.FinalMiscProp91

/-!
# Proposition 9.1 of *Algebraic Magnetism* as an isomorphism of sheaves

`𝒜 = f_* 𝒪_X` is `PushSec X oMod`, an `𝒪_B`-module on the whole site. `preTen G X` is the presheaf tensor product
`T ↦ 𝒜(T) ⊗_{𝒪(T)} G(T)`, on the whole site. `canon` is the printed canonical morphism to `f_* f^* G`. It is bijective on
affine objects, and locally bijective for every topology containing the Zariski coverings, and `f_* f^* G` is a sheaf
whenever `G` is. So `f_* f^* G` is the sheafification of `preTen`, that is, the sheaf `G ⊗_𝒪 𝒜`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

namespace AlgMag.FinalMisc

open AlgMag.S9B AlgMag.S9BF AlgMag.S9BS AlgMag.S9BR AlgMag.S9BP AlgMag.B2 AlgMag.Final
open AlgMag.S9 (PMod)

variable {Bs : BigFppfSite.{u}} {S : Scheme.{u}} {hS : Bs.Contains S}
  {Bsp : (BigFppfOver Bs S hS)ᵒᵖ ⥤ Type u} {G : PMod (OB Bsp)} {X : (SB Bsp)ᵒᵖ ⥤ Type u}

variable (Bsp) in
/-- `𝒪_B` as a module over itself. -/
def oMod : PMod (OB Bsp) where
  obj U := (OB Bsp).obj U
  map f := ((OB Bsp).map f).hom.toAddMonoidHom
  map_smul f a x := by simp [smul_eq_mul]
  map_id U x := by simp
  map_comp f g x := by simp

section Mod
variable (F : PMod (OB Bsp)) (T : SB Bsp)

instance : Zero (PushSec X F T) := ⟨⟨fun _ _ => 0, fun _ _ _ => (map_zero _).symm⟩⟩
instance : Add (PushSec X F T) :=
  ⟨fun a b => ⟨fun t x => a.val t x + b.val t x, fun s t x => by
    rw [a.naturality, b.naturality, map_add]⟩⟩
instance : Neg (PushSec X F T) :=
  ⟨fun a => ⟨fun t x => - a.val t x, fun s t x => by rw [a.naturality, map_neg]⟩⟩
instance : SMul ℕ (PushSec X F T) :=
  ⟨fun n a => ⟨fun t x => n • a.val t x, fun s t x => by rw [a.naturality, map_nsmul]⟩⟩
instance : SMul ℤ (PushSec X F T) :=
  ⟨fun n a => ⟨fun t x => n • a.val t x, fun s t x => by rw [a.naturality, map_zsmul]⟩⟩
instance : Sub (PushSec X F T) :=
  ⟨fun a b => ⟨fun t x => a.val t x - b.val t x, fun s t x => by
    rw [a.naturality, b.naturality, map_sub]⟩⟩

lemma pushSec_val_injective {a b : PushSec X F T}
    (h : ∀ {W : SB Bsp} (t : W ⟶ T) (x : X.obj (op W)), a.val t x = b.val t x) : a = b := by
  ext W t x; exact h t x

instance : AddCommGroup (PushSec X F T) where
  add_assoc a b c := pushSec_val_injective F T fun t x => add_assoc _ _ _
  zero_add a := pushSec_val_injective F T fun t x => zero_add _
  add_zero a := pushSec_val_injective F T fun t x => add_zero _
  add_comm a b := pushSec_val_injective F T fun t x => add_comm _ _
  neg_add_cancel a := pushSec_val_injective F T fun t x => neg_add_cancel _
  nsmul := (· • ·)
  zsmul := (· • ·)
  nsmul_zero a := pushSec_val_injective F T fun t x => zero_nsmul _
  nsmul_succ n a := pushSec_val_injective F T fun t x => succ_nsmul _ _
  zsmul_zero' a := pushSec_val_injective F T fun t x => zero_zsmul _
  zsmul_succ' n a := pushSec_val_injective F T fun t x => by
    change ((n.succ : ℕ) : ℤ) • a.val t x = (n : ℤ) • a.val t x + a.val t x
    rw [Int.natCast_succ, add_zsmul, one_zsmul]
  zsmul_neg' n a := pushSec_val_injective F T fun t x => by
    change (Int.negSucc n) • a.val t x = -(((n.succ : ℕ) : ℤ) • a.val t x)
    rw [negSucc_zsmul, natCast_zsmul]
  sub_eq_add_neg a b := pushSec_val_injective F T fun t x => sub_eq_add_neg _ _

instance : Module ((OB Bsp).obj (op T)) (PushSec X F T) where
  smul c a := ⟨fun t x => ((OB Bsp).map t.op).hom c • a.val t x, fun s t x => by
    rw [a.naturality, F.map_smul]
    congr 1⟩
  one_smul a := pushSec_val_injective F T fun t x => by
    change ((OB Bsp).map t.op).hom 1 • a.val t x = _
    rw [map_one, one_smul]
  mul_smul c d a := pushSec_val_injective F T fun t x => by
    change ((OB Bsp).map t.op).hom (c * d) • a.val t x = _ • _ • _
    rw [map_mul, mul_smul]
  smul_zero c := pushSec_val_injective F T fun t x => smul_zero _
  smul_add c a b := pushSec_val_injective F T fun t x => smul_add _ _ _
  add_smul c d a := pushSec_val_injective F T fun t x => by
    change ((OB Bsp).map t.op).hom (c + d) • a.val t x = _ + _
    rw [map_add, add_smul]; rfl
  zero_smul a := pushSec_val_injective F T fun t x => by
    change ((OB Bsp).map t.op).hom 0 • a.val t x = _
    rw [map_zero, zero_smul]; rfl

end Mod

variable (X G) in
/-- `𝒜(T) ⊗_{𝒪(T)} G(T)`, `𝒜 = f_* 𝒪_X`, on any object `T`. -/
abbrev PreTenAt (T : SB Bsp) : Type (u + 1) :=
  PushSec X (oMod Bsp) T ⊗[(OB Bsp).obj (op T)] G.obj (op T)

lemma pushRes_smul {F : PMod (OB Bsp)} {T T' : SB Bsp} (s : T' ⟶ T) (c : (OB Bsp).obj (op T))
    (a : PushSec X F T) : pushRes s (c • a) = ((OB Bsp).map s.op).hom c • pushRes s a := by
  ext W t x
  change ((OB Bsp).map (t ≫ s).op).hom c • a.val (t ≫ s) x =
    ((OB Bsp).map t.op).hom (((OB Bsp).map s.op).hom c) • a.val (t ≫ s) x
  rw [op_comp, Functor.map_comp]; rfl

/-- The restriction of `𝒜 ⊗ G` along `s`. -/
def preRes {T T' : SB Bsp} (s : T' ⟶ T) : PreTenAt G X T →+ PreTenAt G X T' :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun g => pushRes s a ⊗ₜ G.map s.op g
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun g g' => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext g
        have : pushRes s (0 : PushSec X (oMod Bsp) T) = 0 := rfl
        simp [this]
      map_add' := fun a a' => by
        ext g
        have : pushRes s (a + a') = pushRes s a + pushRes s a' := rfl
        simp [this, TensorProduct.add_tmul] }
    (fun c a g => by
      change pushRes s (c • a) ⊗ₜ G.map s.op g = pushRes s a ⊗ₜ G.map s.op (c • g)
      rw [pushRes_smul, G.map_smul, TensorProduct.smul_tmul])

lemma preRes_id {T : SB Bsp} (p : PreTenAt G X T) : preRes (𝟙 T) p = p := by
  induction p using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul a g =>
    change pushRes (𝟙 _) a ⊗ₜ G.map (𝟙 _).op g = a ⊗ₜ g
    have e : pushRes (𝟙 _) a = a := by
      ext W t x; change a.val (t ≫ 𝟙 _) x = _; rw [Category.comp_id]
    rw [e, op_id, G.map_id]
  | add x y hx hy => rw [map_add, hx, hy]

lemma preRes_comp {T₁ T₂ T₃ : SB Bsp} (s' : T₃ ⟶ T₂) (s : T₂ ⟶ T₁) (p : PreTenAt G X T₁) :
    preRes (s' ≫ s) p = preRes s' (preRes s p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a g =>
    change pushRes (s' ≫ s) a ⊗ₜ G.map (s' ≫ s).op g =
      pushRes s' (pushRes s a) ⊗ₜ G.map s'.op (G.map s.op g)
    have e : pushRes (s' ≫ s) a = pushRes s' (pushRes s a) := by
      ext W t x
      change a.val (t ≫ s' ≫ s) x = a.val ((t ≫ s') ≫ s) x
      rw [Category.assoc]
    rw [e, op_comp, G.map_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (X G) in
/-- The presheaf tensor product `𝒜 ⊗_𝒪 G` on the site of `B`. -/
def preTen : (SB Bsp)ᵒᵖ ⥤ Type (u + 1) where
  obj T := PreTenAt G X T.unop
  map s := ↾ fun p => preRes s.unop p
  map_id T := by
    ext p
    exact preRes_id p
  map_comp s s' := by
    ext p
    exact preRes_comp s'.unop s.unop p

/-- The printed canonical map, `a ⊗ g ↦ ((t, x) ↦ a(t, x) • t^* g)`, at `T`. -/
def canonAt (T : SB Bsp) : PreTenAt G X T →+ PushSec X G T :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun g => ⟨fun t x => (show (OB Bsp).obj _ from a.val t x) • G.map t.op g, fun s t x => by
            rw [a.naturality, G.map_smul, op_comp, G.map_comp]; rfl⟩
          map_zero' := by
            ext W t x
            change _ • G.map t.op 0 = 0
            rw [map_zero, smul_zero]
          map_add' := fun g g' => by
            ext W t x
            change _ • G.map t.op (g + g') = _ • G.map t.op g + _ • G.map t.op g'
            rw [map_add, smul_add] }
      map_zero' := by
        ext g W t x
        exact zero_smul _ _
      map_add' := fun a a' => by
        ext g W t x
        exact add_smul _ _ _ }
    (fun c a g => by
      ext W t x
      change (((OB Bsp).map t.op).hom c * (show (OB Bsp).obj _ from a.val t x)) • G.map t.op g =
        (show (OB Bsp).obj _ from a.val t x) • G.map t.op (c • g)
      rw [G.map_smul, mul_smul, smul_comm])

lemma canonAt_res {T T' : SB Bsp} (s : T' ⟶ T) (p : PreTenAt G X T) :
    canonAt T' (preRes s p) = pushRes s (canonAt T p) := by
  induction p using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul a g =>
    ext W t x
    change (show (OB Bsp).obj _ from a.val (t ≫ s) x) • G.map t.op (G.map s.op g) =
      (show (OB Bsp).obj _ from a.val (t ≫ s) x) • G.map (t ≫ s).op g
    rw [op_comp, G.map_comp]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]; rfl

variable (X G) in
/-- **The canonical morphism of Proposition 9.1**, `𝒜 ⊗_𝒪 G → f_* f^* G`, a morphism of presheaves. -/
def canon : preTen G X ⟶ pushF G X where
  app T := ↾ fun p => canonAt T.unop p
  naturality T T' s := by
    ext p
    exact canonAt_res s.unop p

/-- The comparison `𝒜(T) = 𝒪(T ×_B X)` as a map on tensor products. -/
def tensToPre (r : AffOver X) (T : SB Bsp) [IsAffine T.left] : TensAt r G T →+ PreTenAt G X T :=
  letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun g => (pushSecEquiv r (G := oMod Bsp) T).symm a ⊗ₜ g
          map_zero' := by rw [TensorProduct.tmul_zero]
          map_add' := fun g g' => by rw [TensorProduct.tmul_add] }
      map_zero' := by
        ext g
        have : (pushSecEquiv r (G := oMod Bsp) T).symm 0 = 0 := by
          ext W t x; exact map_zero ((OB Bsp).map _).hom
        exact (congrArg (fun y => y ⊗ₜ[(OB Bsp).obj (op T)] g) this).trans (TensorProduct.zero_tmul _ _)
      map_add' := fun a a' => by
        ext g
        have : (pushSecEquiv r (G := oMod Bsp) T).symm (a + a') =
            (pushSecEquiv r (G := oMod Bsp) T).symm a + (pushSecEquiv r (G := oMod Bsp) T).symm a' := by
          ext W t x; exact map_add ((OB Bsp).map _).hom _ _
        simp [this, TensorProduct.add_tmul] }
    (fun c a g => by
      change (pushSecEquiv r (G := oMod Bsp) T).symm (((OB Bsp).map (r.pr T).op).hom c * a) ⊗ₜ g =
        (pushSecEquiv r (G := oMod Bsp) T).symm a ⊗ₜ (c • g)
      rw [← TensorProduct.smul_tmul]
      congr 1
      ext W t x
      change ((OB Bsp).map (r.lift t x).op).hom (((OB Bsp).map (r.pr T).op).hom c * a) =
        ((OB Bsp).map t.op).hom c * ((OB Bsp).map (r.lift t x).op).hom a
      rw [map_mul]
      congr 1
      have := r.lift_pr t x
      conv_rhs => rw [← this]
      rw [op_comp, Functor.map_comp]; rfl)

/-- `tensToPre` is surjective, since the first factor is an equivalence. -/
lemma tensToPre_surjective (r : AffOver X) (T : SB Bsp) [IsAffine T.left] :
    Function.Surjective (tensToPre (G := G) r T) := by
  intro p
  induction p using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a g =>
    letI := ((OB Bsp).map (r.pr T).op).hom.toAlgebra
    refine ⟨pushSecEquiv r (G := oMod Bsp) T a ⊗ₜ g, ?_⟩
    change (pushSecEquiv r (G := oMod Bsp) T).symm _ ⊗ₜ g = _
    rw [Equiv.symm_apply_apply]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- On an affine `T`, `canon` is bijective. -/
theorem canonAt_bijective (r : AffOver X) (hG : PrintedQCoh G) (T : SB Bsp) [IsAffine T.left] :
    Function.Bijective (canonAt (X := X) (G := G) T) := by
  obtain ⟨Φ, h1, h2, -⟩ := prop91_iso r hG
  have key : ∀ p : TensAt r G T, canonAt T (tensToPre r T p) = Φ T p := by
    intro p
    refine ten_induction r T (p := fun p => canonAt T (tensToPre r T p) = Φ T p) ?_ (fun a g => ?_)
      (fun x y hx hy => ?_) p
    · ext W t x
      have a0 := h1 T 0 0 t x
      rw [add_zero] at a0
      rw [map_zero, map_zero]
      exact (left_eq_add.mp a0).symm
    · ext W t x
      exact (h2 T a g t x).symm
    · ext W t z
      rw [map_add, map_add]
      refine Eq.trans ?_ (h1 T x y t z).symm
      rw [hx, hy]; rfl
  have hsurj := tensToPre_surjective (G := G) r T
  constructor
  · intro p q hpq
    obtain ⟨a, rfl⟩ := hsurj p
    obtain ⟨b, rfl⟩ := hsurj q
    rw [key, key] at hpq
    rw [(Φ T).injective hpq]
  · intro σ
    obtain ⟨p, rfl⟩ := (Φ T).surjective σ
    exact ⟨_, key p⟩

/-- An arrow in the cover sieve of the affine cover factors through an affine object over `T`. -/
lemma exists_affine_factor (T : SB Bsp) {W : SB Bsp} {f : W ⟶ T}
    (hf : coverSieve T T.left.affineCover f) :
    ∃ (U : SB Bsp) (_ : IsAffine U.left) (u : W ⟶ U) (ι : U ⟶ T), f = u ≫ ι := by
  obtain ⟨i, u, hu⟩ := hf
  have hX := coverContains T T.left.affineCover i
  refine ⟨T.ofMap hX (T.left.affineCover.f i), ?_, SB.ofMapLift hX f u hu.symm, T.ofMapι hX _, ?_⟩
  · exact inferInstanceAs (IsAffine (Spec _))
  · apply SB.hom_ext
    rw [SB.comp_left]
    exact hu

/-- **Proposition 9.1**, local injectivity of the canonical morphism. -/
theorem canon_isLocallyInjective (r : AffOver X) (hG : PrintedQCoh G) (J : GrothendieckTopology (SB Bsp))
    (hJ : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left), coverSieve T 𝒰 ∈ J T) :
    Presheaf.IsLocallyInjective J (canon G X) where
  equalizerSieve_mem {T} p q h := by
    refine J.superset_covering ?_ (hJ T.unop T.unop.left.affineCover)
    intro W f hf
    obtain ⟨U, hU, u, ι, rfl⟩ := exists_affine_factor _ hf
    have key : ∀ p q : PreTenAt G X T.unop, canonAt T.unop p = canonAt T.unop q →
        preRes (u ≫ ι) p = preRes (u ≫ ι) q := by
      intro p q h'
      have : preRes ι p = preRes ι q := (canonAt_bijective r hG U).1 (by
        rw [canonAt_res, canonAt_res, h'])
      rw [preRes_comp, preRes_comp, this]
    exact key p q h

/-- **Proposition 9.1**, local surjectivity of the canonical morphism. -/
theorem canon_isLocallySurjective (r : AffOver X) (hG : PrintedQCoh G) (J : GrothendieckTopology (SB Bsp))
    (hJ : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left), coverSieve T 𝒰 ∈ J T) :
    Presheaf.IsLocallySurjective J (canon G X) where
  imageSieve_mem {T} σ := by
    refine J.superset_covering ?_ (hJ T T.left.affineCover)
    intro W f hf
    obtain ⟨U, hU, u, ι, rfl⟩ := exists_affine_factor _ hf
    obtain ⟨p, hp⟩ := (canonAt_bijective r hG U).2 (pushRes ι σ)
    refine ⟨preRes u p, ?_⟩
    change canonAt W (preRes u p) = pushRes (u ≫ ι) σ
    rw [canonAt_res, hp]
    ext W' t x
    change σ.val (t ≫ u ≫ ι) x = σ.val ((t ≫ u) ≫ ι) x
    rw [Category.assoc]

/-- `f_* f^* G` is a sheaf for every topology for which `G` is one. -/
theorem pushF_isSheaf (J : GrothendieckTopology (SB Bsp)) (hG : Presieve.IsSheaf J G.toPresheaf) :
    Presieve.IsSheaf J (pushF G X) := by
  intro T R hR fam hfam
  have hfamc : ∀ {W : SB Bsp} (t : W ⟶ T) (x : X.obj (op W)),
      ∃! g : G.obj (op W), ∀ {V : SB Bsp} (v : V ⟶ W) (hv : R (v ≫ t)),
        G.map v.op g = (fam (v ≫ t) hv).val (𝟙 V) (X.map v.op x) := by
    intro W t x
    have hsf := hG _ (J.pullback_stable t hR)
    let fw : Presieve.FamilyOfElements G.toPresheaf (R.pullback t).arrows :=
      fun V v hv => (fam (v ≫ t) hv).val (𝟙 V) (X.map v.op x)
    have hc : fw.Compatible := by
      intro V₁ V₂ Z a₁ a₂ v₁ v₂ h₁ h₂ w
      have hh := hfam a₁ a₂ h₁ h₂ (by rw [← Category.assoc, w, Category.assoc])
      have e1 := congrArg (fun σ : PushSec X G Z => σ.val (𝟙 Z) (X.map (a₁ ≫ v₁).op x)) hh
      change G.map a₁.op ((fam (v₁ ≫ t) h₁).val (𝟙 V₁) (X.map v₁.op x)) =
        G.map a₂.op ((fam (v₂ ≫ t) h₂).val (𝟙 V₂) (X.map v₂.op x))
      rw [← (fam (v₁ ≫ t) h₁).naturality, ← (fam (v₂ ≫ t) h₂).naturality]
      have ex : X.map a₂.op (X.map v₂.op x) = X.map a₁.op (X.map v₁.op x) := by
        simp only [← types_comp_apply (X.map _) (X.map _), ← X.map_comp, ← op_comp, w]
      rw [ex, Category.comp_id, Category.comp_id]
      have e2 : (pushRes a₁ (fam (v₁ ≫ t) h₁)).val (𝟙 Z) (X.map a₁.op (X.map v₁.op x)) =
          (pushRes a₂ (fam (v₂ ≫ t) h₂)).val (𝟙 Z) (X.map a₁.op (X.map v₁.op x)) := by
        have : pushRes a₁ (fam (v₁ ≫ t) h₁) = pushRes a₂ (fam (v₂ ≫ t) h₂) := hh
        rw [this]
      change (fam (v₁ ≫ t) h₁).val (𝟙 Z ≫ a₁) _ = (fam (v₂ ≫ t) h₂).val (𝟙 Z ≫ a₂) _ at e2
      simpa only [Category.id_comp] using e2
    obtain ⟨g, hg, hu⟩ := hsf fw hc
    exact ⟨g, fun v hv => hg v hv, fun g' h' => hu g' fun V v hv => h' v hv⟩
  choose gl hgl huniq using fun (W : SB Bsp) (t : W ⟶ T) (x : X.obj (op W)) => hfamc t x
  have hfe : ∀ {W : SB Bsp} {a b : W ⟶ T} (ha : R a) (hb : R b), a = b → fam a ha = fam b hb := by
    rintro W a _ ha hb rfl; rfl
  have hval : ∀ {W : SB Bsp} (t : W ⟶ T) (x : X.obj (op W)) (ht : R t),
      gl W t x = (fam t ht).val (𝟙 W) x := by
    intro W t x ht
    have h := hgl W t x (𝟙 W) (by rw [Category.id_comp]; exact ht)
    rw [hfe _ ht (Category.id_comp t)] at h
    simp only [op_id, G.map_id, X.map_id] at h
    simpa using h
  refine ⟨⟨fun {W} t x => gl W t x, ?_⟩, ?_, ?_⟩
  · intro W W' s t x
    refine (huniq W' (s ≫ t) (X.map s.op x) _ fun {V} v hv => ?_).symm
    have h := hgl W t x (v ≫ s) (by rw [Category.assoc]; exact hv)
    rw [hfe _ hv (Category.assoc v s t), op_comp, G.map_comp, X.map_comp] at h
    exact h
  · intro W f hf
    apply pushSec_val_injective G
    intro V t x
    change gl V (t ≫ f) x = (fam f hf).val t x
    rw [hval (t ≫ f) x (R.downward_closed hf t)]
    have hh := hfam t (𝟙 V) hf (R.downward_closed hf t) (by rw [Category.id_comp])
    have e := congrArg (fun σ : PushSec X G V => σ.val (𝟙 V) x) hh
    change (fam f hf).val (𝟙 V ≫ t) x = (fam (t ≫ f) _).val (𝟙 V ≫ 𝟙 V) x at e
    simp only [Category.id_comp] at e
    exact e.symm
  · intro (σ : PushSec X G T) hσ
    apply pushSec_val_injective G
    intro W t x
    refine huniq W t x _ fun {V} v hv => ?_
    rw [← σ.naturality]
    have h : pushRes (v ≫ t) σ = fam (v ≫ t) hv := hσ (v ≫ t) hv
    rw [← h]
    change _ = σ.val (𝟙 V ≫ v ≫ t) _
    rw [Category.id_comp]

/-- **Proposition 9.1**, `f_* f^* F = F ⊗_{𝒪_B} 𝒜` as sheaves. `f : X → B` is affine, `G` is quasi-coherent in the printed
sense, `J` is any topology on the site of `B` containing the Zariski coverings for which `G` is a sheaf, for instance the
fppf topology of the print. The printed canonical morphism `canon` from the presheaf tensor product to `f_* f^* G`
is locally bijective, its target is a sheaf, and every morphism from the presheaf tensor product to a sheaf factors
uniquely through it. So `f_* f^* G` is the sheafification of the presheaf tensor product. -/
theorem prop91_sheaf (r : AffOver X) (hG : PrintedQCoh G) (J : GrothendieckTopology (SB Bsp))
    (hJ : ∀ (T : SB Bsp) (𝒰 : Scheme.OpenCover.{u} T.left), coverSieve T 𝒰 ∈ J T)
    (hGJ : Presieve.IsSheaf J G.toPresheaf) :
    Presheaf.IsLocallyInjective J (canon G X) ∧ Presheaf.IsLocallySurjective J (canon G X) ∧
      Presieve.IsSheaf J (pushF G X) ∧
      ∀ (Q : (SB Bsp)ᵒᵖ ⥤ Type (u + 1)), Presieve.IsSheaf J Q → ∀ h : preTen G X ⟶ Q,
        ∃! k : pushF G X ⟶ Q, canon G X ≫ k = h := by
  have h1 := canon_isLocallyInjective (G := G) r hG J hJ
  have h2 := canon_isLocallySurjective (G := G) r hG J hJ
  refine ⟨h1, h2, pushF_isSheaf J hGJ, fun Q hQ h => ?_⟩
  have hW : J.W (canon G X) := J.W_of_isLocallyBijective _
  have hQ' : Presheaf.IsSheaf J Q := (isSheaf_iff_isSheaf_of_type J Q).2 hQ
  exact (hW Q hQ').existsUnique h

end AlgMag.FinalMisc

#print axioms AlgMag.FinalMisc.prop91_sheaf
#print axioms AlgMag.FinalMisc.canon_isLocallyInjective
#print axioms AlgMag.FinalMisc.canon_isLocallySurjective
#print axioms AlgMag.FinalMisc.pushF_isSheaf
