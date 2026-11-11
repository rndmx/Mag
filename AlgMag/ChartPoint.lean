/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartConclude
import AlgMag.ChartPointAlg
import AlgMag.ChartSplit

/-!
# The point and the orbit (chart-lemma proof, §1)

* `AlgMag.ChartPoint.exists_stab_ideal`: the stabilizer of a point `x : P → X`, `P` affine, `X`
  separated, as a closed subscheme `V(J)` of `D(M)_P`.
* `AlgMag.ChartPoint.exists_stabilizer`: over a field, `H = D(M/Z₀)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TensorProduct

universe u

namespace AlgMag.ChartPoint

open ChartMain

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [AddMonoid.FG M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

variable {P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]

variable (M P) in
/-- `D(M)_P`. -/
noncomputable abbrev Gk : BigFppfOver B S hS := spObj P (ι1 P (M := M)) contains1

variable (M P) in
/-- `D(M)_P → P`. -/
noncomputable abbrev Gπ : Gk M P ⟶ P := spToT P (ι1 P (M := M)) contains1

/-- The orbit map `D(M)_P → X`, `g ↦ g · x`. -/
noncomputable def orbMap (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X) :
    yoneda.obj (Gk M P) ⟶ X :=
  yonedaEquiv.symm (actX.smul (U := op (Gk M P)) (univPt1 (U := P))
    (x.app (op (Gk M P)) (Gπ M P)))

lemma orbMap_app (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X)
    {T : BigFppfOver B S hS} (τ : T ⟶ Gk M P) :
    (orbMap actX x).app (op T) τ =
      actX.smul (U := op T) (secPt ((SCH).map τ).appTop.hom (univPt1 (U := P)))
        (x.app (op T) (τ ≫ Gπ M P)) := by
  refine (actX.map_smul (U := op (Gk M P)) (V := op T) τ.op (univPt1 (U := P)) _).trans ?_
  congr 1
  exact (NatTrans.naturality_apply x τ.op (Gπ M P)).symm

lemma eval_secPt {A R R' : Type*} [CommRing A] [CommRing R] [CommRing R'] {M' : Type*}
    [AddCommGroup M'] (s : R →+* R') (ρ : A →+* R) (z : Multiplicative M' →* R)
    (p : AddMonoidAlgebra A M') :
    evalAt (s.comp ρ) (s.toMonoidHom.comp z) p = s (evalAt ρ z p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single e b =>
    rw [evalAt_single, evalAt_single, map_mul]
    rfl

lemma exists_ringHom_lift {A A' C : Type*} [CommRing A] [CommRing A'] [CommRing C] (f : A →+* A')
    (hf : Function.Surjective f) (g : A →+* C) (hk : RingHom.ker f ≤ RingHom.ker g) :
    ∃ φ : A' →+* C, φ.comp f = g :=
  ⟨RingHom.liftOfSurjective f hf ⟨g, hk⟩, RingHom.ext fun y =>
    RingHom.liftOfRightInverse_comp_apply f _ (Function.rightInverse_surjInv hf) ⟨g, hk⟩ y⟩

/-- **§1**: the stabilizer of `x` is closed in `D(M)_P`, as `X` is separated. The ideal `J` of
`Γ(P)[M]` is such that `h ∈ D(M)(T)` over `t : T → P` fixes `x_T` iff it kills `J`. -/
theorem exists_stab_ideal (hsep : AlgMag.IsSeparatedOver X)
    (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X) :
    ∃ J : Ideal (R1 P M), ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ f ∈ J, evalAt ((SCH).map t).appTop.hom h f = 0 := by
  obtain ⟨E, ι, hc, heq, hfac⟩ := AlgMag.exists_equalizer hsep (W := Gk M P)
    (actX.smul (U := op (Gk M P)) (univPt1 (U := P)) (x.app (op (Gk M P)) (Gπ M P)))
    (x.app (op (Gk M P)) (Gπ M P))
  have hE : IsAffine ((SCH).obj E) := isAffine_of_isAffineHom ((SCH).map ι)
  have hsurj : Function.Surjective ((SCH).map ι).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map ι)).2
  let J : Ideal (R1 P M) := (RingHom.ker ((SCH).map ι).appTop.hom).comap
    (spSec P (ι1 P (M := M)) contains1)
  refine ⟨J, ?_⟩
  intro T t h
  have hψ : (evalAt ((SCH).map t).appTop.hom h).comp (ι1 P (M := M)) = ((SCH).map t).appTop.hom :=
    RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_spLift (R' := R1 P M) (ι1 P) contains1 t _ hψ
  have hres : secPt ((SCH).map τ).appTop.hom (univPt1 (U := P)) = h := MonoidHom.ext fun m => by
    refine (hτ₂ _).trans ?_
    refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
    rw [map_one, one_mul]
    rfl
  have ea : X.map τ.op
      (actX.smul (U := op (Gk M P)) (univPt1 (U := P)) (x.app (op (Gk M P)) (Gπ M P))) =
      actX.smul (U := op T) h (x.app (op T) t) := by
    have := orbMap_app actX x τ
    rw [hres, hτ₁] at this
    exact this
  have eb : X.map τ.op (x.app (op (Gk M P)) (Gπ M P)) = x.app (op T) t := by
    rw [← hτ₁]
    exact (NatTrans.naturality_apply x τ.op (Gπ M P)).symm
  constructor
  · intro hfix f hf
    obtain ⟨l, hl⟩ := hfac τ (ea.trans (hfix.trans eb.symm))
    rw [← hτ₂ f, ← hl, Functor.map_comp, Scheme.Hom.comp_appTop]
    change ((SCH).map l).appTop.hom (((SCH).map ι).appTop.hom _) = 0
    rw [show ((SCH).map ι).appTop.hom (spSec P (ι1 P (M := M)) contains1 f) = 0 from hf, map_zero]
  · intro hkill
    have hker : RingHom.ker ((SCH).map ι).appTop.hom ≤ RingHom.ker ((SCH).map τ).appTop.hom := by
      intro y hy
      obtain ⟨f, rfl⟩ := (spSec_bijective P (ι1 P (M := M)) contains1).2 y
      rw [RingHom.mem_ker, hτ₂]
      exact hkill f hy
    obtain ⟨φ, hφ⟩ := exists_ringHom_lift _ hsurj ((SCH).map τ).appTop.hom hker
    have hfacS : toAffine (T := (SCH).obj T) (U := (SCH).obj E) φ ≫ (SCH).map ι = (SCH).map τ := by
      refine toAffine_ext ?_
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, toAffine_appTop]
      exact hφ
    let l : T ⟶ E := siteHom (toAffine (T := (SCH).obj T) (U := (SCH).obj E) φ) (by
      rw [← site_w ι, ← Category.assoc, hfacS, site_w])
    have hl : l ≫ ι = τ := site_hom_ext (by rw [Functor.map_comp]; exact hfacS)
    have e2 := congrArg (X.map l.op) heq
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at e2
    have hop : ι.op ≫ l.op = τ.op := by rw [← op_comp, hl]
    rw [hop] at e2
    exact ea.symm.trans (e2.trans eb)

section Field

variable (hK : IsField (RT P))
include hK

/-- **§1**: `H = D(M/Z₀)`: the stabilizer of a point over a field, by the classification of Hopf
ideals of `k[M]`. A point of `D(M)` fixes `x` iff it is trivial on `Z₀`. -/
theorem exists_stabilizer (hsep : AlgMag.IsSeparatedOver X)
    (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X) :
    ∃ Z₀ : AddSubgroup M, ∀ {T : BigFppfOver B S hS} (t : T ⟶ P)
      (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1 := by
  classical
  obtain ⟨J, hJ⟩ := exists_stab_ideal hsep actX x
  letI : Field (RT P) := hK.toField
  refine ⟨stabSubgroup J, ?_⟩
  have hone : ∀ f ∈ J, evalAt (algebraMap (RT P) (RT P)) (1 : Multiplicative M →* RT P) f = 0 := by
    intro f hf
    have := (hJ (𝟙 P) (1 : Multiplicative M →* _)).1 (by
      exact actX.one_smul (U := op P) _) f hf
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop] at this
    exact this
  have hmul : ∀ f ∈ J, evalAt (algebraMap (RT P) _) (diagPt J) f = 0 := by
    let Bq := R1 P M ⧸ J
    let R := Bq ⊗[RT P] Bq
    haveI : Algebra.FiniteType (RT P) (R1 P M) := AddMonoidAlgebra.finiteType_of_fg _ _
    haveI : Algebra.FiniteType (RT P) Bq :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ _ J) Ideal.Quotient.mk_surjective
    haveI : Algebra.FiniteType Bq R := inferInstance
    haveI : Algebra.FiniteType (RT P) R := Algebra.FiniteType.trans ‹_› ‹_›
    have hC : B.Contains (Spec (.of R)) := contains_ft (RT P) R (contains_RT P)
    let T := spObj P (algebraMap (RT P) R) hC
    let t : T ⟶ P := spToT P _ hC
    let sec : R →+* Γ((SCH).obj T, ⊤) := spSec P _ hC
    have ht : ((SCH).map t).appTop.hom = sec.comp (algebraMap (RT P) R) :=
      RingHom.ext fun b => spToT_appTop P _ hC b
    let i₁ : Bq →ₐ[RT P] R := Algebra.TensorProduct.includeLeft
    let i₂ : Bq →ₐ[RT P] R := Algebra.TensorProduct.includeRight
    have hi : ∀ i : Bq →ₐ[RT P] R, ∀ f ∈ J, evalAt ((SCH).map t).appTop.hom
        (sec.toMonoidHom.comp ((i : Bq →+* R).toMonoidHom.comp (bq J))) f = 0 := by
      intro i f hf
      have e : ∀ p : R1 P M, evalAt (algebraMap (RT P) R)
          ((i : Bq →+* R).toMonoidHom.comp (bq J)) p = i (Ideal.Quotient.mk J p) := by
        intro p
        induction p using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | single m c =>
          rw [evalAt_single, mk_single, map_smul, Algebra.smul_def]
          rfl
      rw [ht, eval_secPt, e, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero, map_zero]
    have h₁ := (hJ t _).2 (hi i₁)
    have h₂ := (hJ t _).2 (hi i₂)
    have hm := actX.mul_smul (U := op T) (sec.toMonoidHom.comp ((i₁ : Bq →+* R).toMonoidHom.comp (bq J)))
      (sec.toMonoidHom.comp ((i₂ : Bq →+* R).toMonoidHom.comp (bq J))) (x.app (op T) t)
    rw [h₂, h₁] at hm
    intro f hf
    have ed : (sec.toMonoidHom.comp ((i₁ : Bq →+* R).toMonoidHom.comp (bq J)) *
        sec.toMonoidHom.comp ((i₂ : Bq →+* R).toMonoidHom.comp (bq J)) :
          APt (fppfO B S hS) M (op T)) =
        sec.toMonoidHom.comp (diagPt J) := by
      ext m
      change sec _ * sec _ = sec _
      rw [← map_mul]
      congr 1
      change (bq J m ⊗ₜ[RT P] 1) * (1 ⊗ₜ[RT P] bq J m) = bq J m ⊗ₜ[RT P] bq J m
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hm' : actX.smul (U := op T) (sec.toMonoidHom.comp (diagPt J)) (x.app (op T) t) =
        x.app (op T) t := by
      rw [← ed]; exact hm
    have := (hJ t _).1 hm' f hf
    rw [ht, eval_secPt] at this
    exact (spSec_bijective P _ hC).1 (this.trans (map_zero _).symm)
  intro T t h
  rw [hJ t h]
  constructor
  · intro hk z hz
    have := hk _ hz
    rw [map_sub, evalAt_single, map_one, map_one, one_mul, sub_eq_zero] at this
    exact this
  · intro hz f hf
    exact eval_eq_zero_of_trivial_on hone hmul _ h (fun z hzJ => hz z hzJ) hf

end Field

section OrbitObject

variable (N : AddSubgroup M) [AddMonoid.FG N]

variable (P) in
/-- `Γ(P)[N]`. -/
noncomputable abbrev RN : Type u := AddMonoidAlgebra (RT P) N

include N in
lemma containsN : B.Contains (Spec (.of (RN P N))) := contains_M (M := N) (contains_RT P)

variable (P) in
/-- `O = Spec Γ(P)[Z₀]`, as an object of the site. -/
noncomputable abbrev Ob : BigFppfOver B S hS :=
  spObj P (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N) (containsN N)

variable (P) in
/-- `O → P`. -/
noncomputable abbrev Oπ : Ob P N ⟶ P := spToT P _ (containsN N)

variable {N} in
/-- The character of `N` attached to a point of `O`. -/
noncomputable def oChar {T : BigFppfOver B S hS} (t : T ⟶ Ob P N) :
    Multiplicative N →* Γ((SCH).obj T, ⊤) :=
  (((SCH).map t).appTop.hom.toMonoidHom).comp
    ((spSec P _ (containsN N)).toMonoidHom.comp (AddMonoidAlgebra.of (RT P) N))

lemma oChar_ofAdd {T : BigFppfOver B S hS} (t : T ⟶ Ob P N) (z : N) :
    oChar t (Multiplicative.ofAdd z) = ((SCH).map t).appTop.hom
      (spSec P _ (containsN N) (AddMonoidAlgebra.single z 1)) := rfl

lemma oChar_comp {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (t : T ⟶ Ob P N) :
    oChar (τ ≫ t) = ((SCH).map τ).appTop.hom.toMonoidHom.comp (oChar t) := by
  refine MonoidHom.ext fun z => ?_
  simp only [oChar, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- A point of `O` is a point of `P` and a character of `N`. -/
lemma appTop_eq_eval {T : BigFppfOver B S hS} (t : T ⟶ Ob P N) (p : RN P N) :
    ((SCH).map t).appTop.hom (spSec P _ (containsN N) p) =
      evalAt ((SCH).map (t ≫ Oπ P N)).appTop.hom (oChar t) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single z b =>
    rw [evalAt_single]
    have e : AddMonoidAlgebra.single z b = (AddMonoidAlgebra.singleZeroRingHom b : RN P N) *
        AddMonoidAlgebra.single z (1 : RT P) := by
      rw [show (AddMonoidAlgebra.singleZeroRingHom b : RN P N) = AddMonoidAlgebra.single 0 b from rfl,
        AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
    rw [e, map_mul, map_mul, Functor.map_comp, Scheme.Hom.comp_appTop]
    congr 1
    change _ = ((SCH).map t).appTop.hom (((SCH).map (Oπ P N)).appTop.hom b)
    rw [spToT_appTop]

lemma o_ext {T : BigFppfOver B S hS} {t t' : T ⟶ Ob P N} (hb : t ≫ Oπ P N = t' ≫ Oπ P N)
    (hc : oChar t = oChar t') : t = t' := by
  refine site_hom_ext (toAffine_ext (RingHom.ext fun y => ?_))
  obtain ⟨p, rfl⟩ := (spSec_bijective P _ (containsN N)).2 y
  rw [appTop_eq_eval, appTop_eq_eval, hb, hc]

/-- The point of `O` with a given base and character. -/
noncomputable def oLift {T : BigFppfOver B S hS} (τ : T ⟶ P)
    (c : Multiplicative N →* Γ((SCH).obj T, ⊤)) : T ⟶ Ob P N :=
  spLift P _ (containsN N) τ (evalAt ((SCH).map τ).appTop.hom c)
    (RingHom.ext fun b => evalAt_ι _ _ b)

@[simp] lemma oLift_π {T : BigFppfOver B S hS} (τ : T ⟶ P)
    (c : Multiplicative N →* Γ((SCH).obj T, ⊤)) : oLift N τ c ≫ Oπ P N = τ :=
  spLift_toT P _ (containsN N) τ _ _

@[simp] lemma oChar_oLift {T : BigFppfOver B S hS} (τ : T ⟶ P)
    (c : Multiplicative N →* Γ((SCH).obj T, ⊤)) : oChar (oLift N τ c) = c := by
  refine MonoidHom.ext fun z => ?_
  refine (spLift_appTop P _ (containsN N) τ (evalAt ((SCH).map τ).appTop.hom c)
    (RingHom.ext fun b => evalAt_ι _ _ b) (AddMonoidAlgebra.single (Multiplicative.toAdd z) 1)).trans ?_
  refine (evalAt_single _ _ _ _).trans ?_
  rw [map_one, one_mul]
  rfl

/-- `D(M) → D(N)`, on points. -/
def resChar {R : Type*} [Monoid R] (g : Multiplicative M →* R) : Multiplicative N →* R :=
  g.comp (AddMonoidHom.toMultiplicative N.subtype)

lemma resChar_ofAdd {R : Type*} [Monoid R] (g : Multiplicative M →* R) (z : N) :
    resChar N g (Multiplicative.ofAdd z) = g (Multiplicative.ofAdd (z : M)) := rfl

/-- The value of the action of `D(M)` on `O`. -/
noncomputable def oSmul {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (t : T ⟶ Ob P N) : T ⟶ Ob P N :=
  oLift N (t ≫ Oπ P N) (oChar t * resChar N g)

lemma oSmul_π {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (t : T ⟶ Ob P N) : oSmul N g t ≫ Oπ P N = t ≫ Oπ P N := oLift_π N _ _

lemma oChar_oSmul {T : BigFppfOver B S hS} (g : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (t : T ⟶ Ob P N) : oChar (oSmul N g t) = oChar t * resChar N g := oChar_oLift N _ _

lemma oSmul_ext {T : BigFppfOver B S hS} {t t' : T ⟶ Ob P N} (hb : t ≫ Oπ P N = t' ≫ Oπ P N)
    (hc : ∀ z, oChar t z = oChar t' z) : t = t' :=
  o_ext N hb (MonoidHom.ext hc)

lemma oSmul_one {T : BigFppfOver B S hS} (t : T ⟶ Ob P N) : oSmul N 1 t = t := by
  refine oSmul_ext N (oSmul_π N 1 t) fun z => ?_
  rw [oChar_oSmul]
  exact mul_one (oChar t z)

lemma oSmul_mul {T : BigFppfOver B S hS} (g h : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (t : T ⟶ Ob P N) : oSmul N (g * h) t = oSmul N g (oSmul N h t) := by
  refine oSmul_ext N ((oSmul_π N (g * h) t).trans
    ((oSmul_π N h t).symm.trans (oSmul_π N g _).symm)) fun z => ?_
  rw [oChar_oSmul, oChar_oSmul, oChar_oSmul]
  change oChar t z * (g _ * h _) = oChar t z * h _ * g _
  ring

lemma comp_oSmul {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ Ob P N) :
    τ ≫ oSmul N g t = oSmul N (((SCH).map τ).appTop.hom.toMonoidHom.comp g) (τ ≫ t) := by
  refine oSmul_ext N ?_ fun z => ?_
  · rw [Category.assoc, oSmul_π, oSmul_π, Category.assoc]
  · rw [oChar_comp, oChar_oSmul, oChar_oSmul, oChar_comp]
    change ((SCH).map τ).appTop.hom (oChar t z * _) = ((SCH).map τ).appTop.hom (oChar t z) * _
    rw [map_mul]
    rfl

/-- The action of `D(M)` on `O = D(N)_P`. -/
noncomputable def oAct : AAction (fppfO B S hS) M (yoneda.obj (Ob P N)) where
  smul {T} g t := oSmul N (T := T.unop) g t
  one_smul {T} t := oSmul_one N (T := T.unop) t
  mul_smul {T} g h t := oSmul_mul N (T := T.unop) g h t
  map_smul {T V} e g t := comp_oSmul N (T := T.unop) (T' := V.unop) e.unop g t

/-- The unit section of `O`, over `P`. -/
noncomputable def oUnit : P ⟶ Ob P N := oLift N (𝟙 P) 1

/-- **§6, stabilizer clause**: if `g` is trivial on `N`, then `g` fixes every point of the identity
section of `O`. -/
lemma oAct_fix {T : BigFppfOver B S hS} (t : T ⟶ P) (g : Multiplicative M →* Γ((SCH).obj T, ⊤))
    (hg : ∀ z ∈ N, g (Multiplicative.ofAdd z) = 1) :
    (oAct N).smul (F := yoneda.obj (Ob P N)) (U := op T) g (t ≫ oUnit N) = t ≫ oUnit N := by
  refine oSmul_ext N (oSmul_π N g _) fun z => ?_
  refine (DFunLike.congr_fun (oChar_oSmul N g (t ≫ oUnit N)) z).trans ?_
  change oChar (t ≫ oUnit N) z * g (Multiplicative.ofAdd ((Multiplicative.toAdd z : N) : M)) = _
  rw [hg _ (Multiplicative.toAdd z : N).2, mul_one]

end OrbitObject

section Conclude

variable (N : AddSubgroup M) [AddMonoid.FG N]

/-- **§6, the stabilizer clause of `AlgMag.IsChartAt`** (`hstab` of
`AlgMag.ChartConclude.exists_chart_of_etaleAt`). `W` has an equivariant map `i : O → W`, `f : W → X`
is equivariant, `u₀ = e ≫ i`, and the stabilizer of `x = f(u₀)` is `D(M/N)`. -/
theorem hstab_of_orbit {W : BigFppfOver B S hS} (actW : AAction (fppfO B S hS) M (yoneda.obj W))
    (actX : AAction (fppfO B S hS) M X) (i : Ob P N ⟶ W)
    (hi : IsEquivariant (oAct N) actW (yoneda.map i)) (f : yoneda.obj W ⟶ X)
    (hN : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (f.app (op T) (t ≫ oUnit N ≫ i)) = f.app (op T) (t ≫ oUnit N ≫ i) →
        ∀ z ∈ N, h (Multiplicative.ofAdd z) = 1)
    {T : BigFppfOver B S hS} (t : T ⟶ P) (g : APt (fppfO B S hS) M (op T))
    (hg : actX.smul g (f.app (op T) (t ≫ oUnit N ≫ i)) = f.app (op T) (t ≫ oUnit N ≫ i)) :
    actW.smul (F := yoneda.obj W) g (t ≫ oUnit N ≫ i) = t ≫ oUnit N ≫ i := by
  have h1 := oAct_fix N t g (hN t g hg)
  have h2 := hi (T := op T) g (t ≫ oUnit N)
  have h3 : (yoneda.map i).app (op T) (t ≫ oUnit N) = t ≫ oUnit N ≫ i := by
    change (t ≫ oUnit N) ≫ i = _
    rw [Category.assoc]
  rw [h3] at h2
  rw [← h2, h1, h3]

/-- The inner character of `A[N][M]`. -/
noncomputable def c0 (A : Type u) [CommRing A] : Multiplicative N →*
    AddMonoidAlgebra (AddMonoidAlgebra A N) M :=
  ((AddMonoidAlgebra.singleZeroRingHom :
    AddMonoidAlgebra A N →+* AddMonoidAlgebra (AddMonoidAlgebra A N) M).toMonoidHom).comp
    (AddMonoidAlgebra.of A N)

/-- `A → A[N][M]`. -/
noncomputable def ρ0 (A : Type u) [CommRing A] : A →+* AddMonoidAlgebra (AddMonoidAlgebra A N) M :=
  (AddMonoidAlgebra.singleZeroRingHom).comp AddMonoidAlgebra.singleZeroRingHom

lemma coeff_twist {A : Type u} [CommRing A] (p : AddMonoidAlgebra A N) (z : N) :
    ((evalAt (ρ0 N A) (c0 N A * resChar N (AddMonoidAlgebra.of (AddMonoidAlgebra A N) M)) p).coeff
      (z : M)).coeff z = p.coeff z := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single w b =>
    rw [evalAt_single]
    have e : ρ0 N A b * (c0 N A * resChar N (AddMonoidAlgebra.of (AddMonoidAlgebra A N) M))
        (Multiplicative.ofAdd w) = AddMonoidAlgebra.single (w : M) (AddMonoidAlgebra.single w b) := by
      change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
        (AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single w 1) *
          AddMonoidAlgebra.single (w : M) 1) = _
      simp [AddMonoidAlgebra.single_mul_single]
    rw [e]
    by_cases h : w = z
    · subst h; simp
    · have h' : (w : M) ≠ z := fun e => h (Subtype.ext e)
      simp [h, h', AddMonoidAlgebra.coeff_single]

lemma eval_c0 {A : Type u} [CommRing A] (p : AddMonoidAlgebra A N) :
    evalAt (ρ0 N A) (c0 N A) p = (AddMonoidAlgebra.singleZeroRingHom p :
      AddMonoidAlgebra (AddMonoidAlgebra A N) M) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single w b =>
    rw [evalAt_single]
    change AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 b) *
      AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single w 1) = _
    simp [AddMonoidAlgebra.single_mul_single]

set_option maxHeartbeats 2000000 in
/-- The elements of `Γ(O)` homogeneous of degree `d` for `oAct` are supported in degree `d`. -/
lemma coeff_eq_zero_of_homog {d : M} {y : RN P N}
    (hy : spSec P _ (containsN N) y ∈ homog (oAct (P := P) N) d) {z : N}
    (hz : y.coeff z ≠ 0) : (z : M) = d := by
  classical
  by_contra hne
  apply hz
  let R := AddMonoidAlgebra (RN P N) M
  have hC : B.Contains (Spec (.of R)) := contains_M (containsN N)
  let ρ : RT P →+* R := ρ0 N (RT P)
  let sec : R →+* Γ((SCH).obj (spObj P ρ hC), ⊤) := spSec P ρ hC
  let τ : spObj P ρ hC ⟶ P := spToT P ρ hC
  let u : Multiplicative M →* R := AddMonoidAlgebra.of (RN P N) M
  have hτ : ((SCH).map τ).appTop.hom = sec.comp ρ := RingHom.ext fun b => spToT_appTop P ρ hC b
  let t : spObj P ρ hC ⟶ Ob P N := oLift N τ (sec.toMonoidHom.comp (c0 N (RT P)))
  have key := appTop_smul_of_mem (oAct (P := P) N) t (sec.toMonoidHom.comp u) hy
  have hsm : smulAt (oAct (P := P) N) (sec.toMonoidHom.comp u) t =
      oSmul N (sec.toMonoidHom.comp u) t := rfl
  rw [hsm, appTop_eq_eval, appTop_eq_eval, oSmul_π, oChar_oSmul] at key
  have hπ : t ≫ Oπ P N = τ := oLift_π N _ _
  have hχ : oChar t = sec.toMonoidHom.comp (c0 N (RT P)) := oChar_oLift N _ _
  rw [hπ, hχ, hτ] at key
  have hmulc : sec.toMonoidHom.comp (c0 N (RT P)) * resChar N (sec.toMonoidHom.comp u) =
      sec.toMonoidHom.comp (c0 N (RT P) * resChar N u) :=
    MonoidHom.ext fun w => (map_mul sec _ _).symm
  rw [hmulc, eval_secPt, eval_secPt] at key
  have e2 : sec (evalAt ρ (c0 N (RT P) * resChar N u) y) =
      sec (evalAt ρ (c0 N (RT P)) y * u (Multiplicative.ofAdd d)) := by
    rw [map_mul]; exact key
  have key' := (spSec_bijective P ρ hC).1 e2
  have e3 := coeff_twist N y z
  rw [show evalAt (ρ0 N (RT P)) (c0 N (RT P) * resChar N (AddMonoidAlgebra.of (RN P N) M)) y =
    evalAt ρ (c0 N (RT P)) y * u (Multiplicative.ofAdd d) from key'] at e3
  rw [← e3]
  change ((evalAt (ρ0 N (RT P)) (c0 N (RT P)) y * AddMonoidAlgebra.single d 1).coeff (z : M)).coeff z = 0
  rw [eval_c0]
  change ((AddMonoidAlgebra.single 0 y * AddMonoidAlgebra.single d 1 : R).coeff (z : M)).coeff z = 0
  rw [AddMonoidAlgebra.single_mul_single, zero_add, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, ite_eq_right_iff.2 (fun e => absurd e.symm hne)]
  rfl

/-- **§1, `hOf` of `AlgMag.ChartConclude.exists_chart_of_etaleAt`**: for an equivariant closed
immersion `i : O → W`, homogeneous elements outside `I_O` are units modulo `I_O`. -/
theorem hOf_of_orbit (hK : IsField (RT P)) {W : BigFppfOver B S hS}
    [IsAffine ((SCH).obj W)] (actW : AAction (fppfO B S hS) M (yoneda.obj W)) (i : Ob P N ⟶ W)
    (hi : IsEquivariant (oAct N) actW (yoneda.map i))
    (hc : IsClosedImmersion ((SCH).map i)) {d : M} {c : Γ((SCH).obj W, ⊤)}
    (hd : c ∈ homog actW d) (hcO : c ∉ RingHom.ker ((SCH).map i).appTop.hom) :
    ∃ c', c * c' - 1 ∈ RingHom.ker ((SCH).map i).appTop.hom := by
  letI : Field (RT P) := hK.toField
  let e := RingEquiv.ofBijective (spSec P (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N) (containsN N))
    (spSec_bijective P (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N) (containsN N))
  let ψ : Γ((SCH).obj W, ⊤) →+* RN P N := (e.symm : _ →+* _).comp ((SCH).map i).appTop.hom
  have hψs : Function.Surjective ψ :=
    e.symm.surjective.comp (IsClosedImmersion.isAffine_surjective_of_isAffine ((SCH).map i)).2
  have hker : RingHom.ker ((SCH).map i).appTop.hom = RingHom.ker ψ := by
    ext a
    simp [ψ, RingHom.mem_ker]
  rw [hker] at hcO ⊢
  refine exists_inv_of_homogeneous (homog actW) (fun z : N => (z : M)) Subtype.val_injective ψ hψs
    ?_ rfl hd hcO
  intro d' a ha z hz
  refine coeff_eq_zero_of_homog N (d := d') (y := ψ a) ?_ hz
  have := map_mem_homog (U := Ob P N) (V := W) (oAct (P := P) N) actW hi ha
  have e' : spSec P (AddMonoidAlgebra.singleZeroRingHom : RT P →+* RN P N) (containsN N) (ψ a) = ((SCH).map i).appTop.hom a :=
    e.apply_symm_apply _
  rw [e']
  exact this

end Conclude

section Free

variable (N : AddSubgroup M)

/-- `K[N] → K[M]`. -/
noncomputable def inclN (K : Type u) [CommRing K] :
    AddMonoidAlgebra K N →+* AddMonoidAlgebra K M :=
  evalAt AddMonoidAlgebra.singleZeroRingHom
    ((AddMonoidAlgebra.of K M).comp (AddMonoidHom.toMultiplicative N.subtype))

lemma inclN_single {K : Type u} [CommRing K] (z : N) (b : K) :
    inclN N K (AddMonoidAlgebra.single z b) = AddMonoidAlgebra.single (z : M) b := by
  rw [inclN, evalAt_single]
  change AddMonoidAlgebra.single 0 b * AddMonoidAlgebra.single (z : M) 1 = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- **§1**: `K[M]` is free over `K[N]`, on a transversal of `M/N`. So `D(M)_K → D(N)_K` is fpqc. -/
theorem free_inclN (K : Type u) [CommRing K] :
    letI := (inclN N K).toAlgebra
    Module.Free (AddMonoidAlgebra K N) (AddMonoidAlgebra K M) := by
  classical
  letI := (inclN N K).toAlgebra
  have hsmul : ∀ (a : AddMonoidAlgebra K N) (f : AddMonoidAlgebra K M), a • f = inclN N K a * f :=
    fun a f => Algebra.smul_def a f
  let out : M ⧸ N → M := Quotient.out
  have hout : ∀ m : M, -out (QuotientAddGroup.mk m) + m ∈ N := fun m =>
    QuotientAddGroup.eq.1 (Quotient.out_eq' (QuotientAddGroup.mk m : M ⧸ N))
  let v : M ⧸ N → AddMonoidAlgebra K M := fun c => AddMonoidAlgebra.single (out c) 1
  have hspan : ⊤ ≤ Submodule.span (AddMonoidAlgebra K N) (Set.range v) := by
    rintro f -
    induction f using AddMonoidAlgebra.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add p q hp hq => exact Submodule.add_mem _ hp hq
    | single m b =>
      have e : AddMonoidAlgebra.single m b =
          (AddMonoidAlgebra.single (⟨_, hout m⟩ : N) b : AddMonoidAlgebra K N) •
            v (QuotientAddGroup.mk m) := by
        rw [hsmul, inclN_single]
        change _ = AddMonoidAlgebra.single _ b * AddMonoidAlgebra.single _ 1
        rw [AddMonoidAlgebra.single_mul_single, mul_one]
        congr 1
        change m = -out _ + m + out _
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hli : LinearIndependent (AddMonoidAlgebra K N) v := by
    rw [linearIndependent_iff]
    intro l hl
    -- coefficient at `z + out c`
    have hco : ∀ (l : (M ⧸ N) →₀ AddMonoidAlgebra K N) (c : M ⧸ N) (z : N),
        (Finsupp.linearCombination (AddMonoidAlgebra K N) v l).coeff ((z : M) + out c) =
          (l c).coeff z := by
      intro l c z
      induction l using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp [map_add, hf, hg]
      | single d a =>
        rw [Finsupp.linearCombination_single, hsmul]
        induction a using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add p q hp hq => simp [map_add, add_mul, hp, hq, Finsupp.single_add]
        | single w b =>
          rw [inclN_single]
          change (AddMonoidAlgebra.single (w : M) b * AddMonoidAlgebra.single (out d) 1 : AddMonoidAlgebra K M).coeff _ = _
          rw [AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.coeff_single,
            Finsupp.single_apply]
          by_cases hdc : d = c
          · subst hdc
            by_cases hw : w = z
            · subst hw; simp
            · have : ¬ ((w : M) + out d = (z : M) + out d) := fun e =>
                hw (Subtype.ext (add_right_cancel e))
              simp [this, hw, AddMonoidAlgebra.coeff_single]
          · have : ¬ ((w : M) + out d = (z : M) + out c) := by
              intro e
              apply hdc
              have h1 : (QuotientAddGroup.mk (out d) : M ⧸ N) = d := Quotient.out_eq' d
              have h2 : (QuotientAddGroup.mk (out c) : M ⧸ N) = c := Quotient.out_eq' c
              rw [← h1, ← h2, QuotientAddGroup.eq]
              have : -out d + out c = (w : M) - z := by
                have e' : out c = (w : M) + out d - z := by rw [e]; abel
                rw [e']; abel
              rw [this]
              exact N.sub_mem w.2 z.2
            simp [this, hdc]
    ext c z
    have := hco l c z
    rw [hl] at this
    simpa using this.symm
  exact Module.Free.of_basis (Module.Basis.mk hli hspan)

end Free

/-- A subgroup of a finitely generated abelian group is finitely generated. -/
lemma fg_addSubgroup (N : AddSubgroup M) : AddMonoid.FG N := by
  have hf : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.2 (AddGroup.fg_iff_addMonoid_fg.2 ‹_›)
  have : IsNoetherian ℤ M := inferInstance
  have h2 : Module.Finite ℤ N.toIntSubmodule := inferInstance
  exact AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 h2)


section Orbit

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable (N : AddSubgroup M) [AddMonoid.FG N]

lemma inclN_comp : (inclN N (RT P)).comp (AddMonoidAlgebra.singleZeroRingHom) = ι1 P (M := M) :=
  RingHom.ext fun b => by
    change inclN N (RT P) (AddMonoidAlgebra.single 0 b) = AddMonoidAlgebra.single 0 b
    exact inclN_single N 0 b

/-- `D(M)_P → O`. -/
noncomputable def qN : Gk M P ⟶ Ob P N :=
  spMap P (inclN N (RT P)) (inclN_comp N)

lemma qN_π : qN N (P := P) ≫ Oπ P N = Gπ M P := spMap_toT P _ _

lemma oChar_qN {T : BigFppfOver B S hS} (g : T ⟶ Gk M P) :
    oChar (g ≫ qN N) = resChar N (secPt ((SCH).map g).appTop.hom (univPt1 (U := P))) := by
  rw [oChar_comp]
  refine MonoidHom.ext fun z => ?_
  have e := spMap_appTop P (hC := containsN N) (hC' := contains1) (inclN N (RT P))
    (inclN_comp N) (AddMonoidAlgebra.single (Multiplicative.toAdd z) 1)
  change ((SCH).map g).appTop.hom (((SCH).map (qN N)).appTop.hom
    (spSec P _ (containsN N) (AddMonoidAlgebra.single (Multiplicative.toAdd z) 1))) = _
  rw [qN, e, inclN_single]
  rfl

/-- The point of `D(M)_P` over `τ` with value `h`. -/
lemma exists_gkLift {T : BigFppfOver B S hS} (τ : T ⟶ P)
    (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) :
    ∃ w : T ⟶ Gk M P, w ≫ Gπ M P = τ ∧ secPt ((SCH).map w).appTop.hom (univPt1 (U := P)) = h := by
  have hψ : (evalAt ((SCH).map τ).appTop.hom h).comp (ι1 P (M := M)) = ((SCH).map τ).appTop.hom :=
    RingHom.ext fun b => evalAt_ι _ _ b
  obtain ⟨w, h₁, h₂⟩ := exists_spLift (R' := R1 P M) (ι1 P) contains1 τ _ hψ
  refine ⟨w, h₁, MonoidHom.ext fun m => ?_⟩
  refine (h₂ _).trans ?_
  refine (evalAt_single _ _ (Multiplicative.toAdd m) 1).trans ?_
  rw [map_one, one_mul]
  rfl

/-- A flat surjective quasi-compact morphism is an fpqc family with one member. -/
lemma ofArrows_unit_mem_fpqc' {Z T : Scheme.{u}} (q : Z ⟶ T) (hf : Flat q) (hs : Surjective q)
    (hq : QuasiCompact q) :
    Presieve.ofArrows (fun _ : Unit => Z) (fun _ => q) ∈ Scheme.fpqcPrecoverage T := by
  have hcov : ∀ x : T, ∃ i : Unit, x ∈ Set.range q := fun x => ⟨(), q.surjective x⟩
  let 𝒰 : T.Cover (Scheme.precoverage @Flat) :=
    Scheme.Cover.mkOfCovers Unit (fun _ => Z) (fun _ => q) hcov (fun _ => hf)
  have := Scheme.jointlySurjective_precoverage_flat
  have hfin : Finite 𝒰.I₀ := inferInstanceAs (Finite Unit)
  have hc : ∀ i, QuasiCompact (𝒰.f i) := fun _ => hq
  have hqc : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hqc,
    (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, fun _ => hf⟩⟩

lemma flat_qN (_hK : IsField (RT P)) : Flat ((SCH).map (qN N (P := P))) := by
  letI := (inclN N (RT P)).toAlgebra
  haveI := free_inclN N (RT P)
  change Flat (Spec.map (CommRingCat.ofHom (inclN N (RT P))))
  exact Flat.SpecMap_iff.2 (inferInstanceAs (Module.Flat (AddMonoidAlgebra (RT P) N) _))

lemma surjective_qN (hK : IsField (RT P)) : Surjective ((SCH).map (qN N (P := P))) := by
  letI := (inclN N (RT P)).toAlgebra
  haveI := free_inclN N (RT P)
  haveI : Nontrivial (RT P) := ⟨hK.exists_pair_ne⟩
  haveI : Module.FaithfullyFlat (AddMonoidAlgebra (RT P) N) (AddMonoidAlgebra (RT P) M) :=
    inferInstance
  change Surjective (Spec.map (CommRingCat.ofHom (inclN N (RT P))))
  exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩

/-- Base change of a flat surjective quasi-compact map to an arbitrary `T`: `X(T)` is separated. -/
theorem eq_of_cover (hK : IsField (RT P)) {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) {T : BigFppfOver B S hS} (t : T ⟶ Ob P N) (a b : W.obj (op T))
    (h : W.map (pullback.fst t (qN N)).op a = W.map (pullback.fst t (qN N)).op b) : a = b := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hW
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have sq := (IsPullback.of_hasPullback t (qN N (P := P))).map (SCH)
  have hfl := flat_qN (P := P) N hK
  have hsu := surjective_qN (P := P) N hK
  have hF : Flat ((SCH).map (pullback.fst t (qN N (P := P)))) :=
    MorphismProperty.of_isPullback sq.flip hfl
  have hSu : Surjective ((SCH).map (pullback.fst t (qN N (P := P)))) :=
    MorphismProperty.of_isPullback sq.flip hsu
  have hQ : QuasiCompact ((SCH).map (pullback.fst t (qN N (P := P)))) :=
    MorphismProperty.of_isPullback sq.flip inferInstance
  have hR : Presieve.ofArrows (fun _ : Unit => pullback t (qN N (P := P)))
      (fun _ => pullback.fst t (qN N (P := P))) ∈ Scheme.fpqcPrecoverage.comap (SCH) T := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact ofArrows_unit_mem_fpqc' _ hF hSu hQ
  have hS' := (Presieve.isSheafFor_arrows_iff W
    (fun _ : Unit => pullback.fst t (qN N (P := P)))).1 (hsh _ hR)
  obtain ⟨s, -, hu⟩ := hS' (fun _ => W.map (pullback.fst t (qN N (P := P))).op a) (by
    intro i j Z g₁ g₂ e
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e])
  have ha := hu a fun _ => rfl
  have hb := hu b fun _ => h.symm
  exact ha.trans hb.symm

variable {N}
variable {actX : AAction (fppfO B S hS) M X} {x : yoneda.obj P ⟶ X}

lemma orbMap_congr
    (hN : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ N, h (Multiplicative.ofAdd z) = 1)
    {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ Gk M P) (e : g₁ ≫ qN N = g₂ ≫ qN N) :
    (orbMap actX x).app (op Z) g₁ = (orbMap actX x).app (op Z) g₂ := by
  have hb : g₁ ≫ Gπ M P = g₂ ≫ Gπ M P := by
    rw [← qN_π N, ← Category.assoc, ← Category.assoc, e]
  rw [orbMap_app, orbMap_app, hb]
  set h₁ := secPt ((SCH).map g₁).appTop.hom (univPt1 (U := P))
  set h₂ := secPt ((SCH).map g₂).appTop.hom (univPt1 (U := P))
  have hc : resChar N h₁ = resChar N h₂ := by
    rw [← oChar_qN, ← oChar_qN, e]
  let c : Multiplicative M →* Γ((SCH).obj Z, ⊤) :=
    h₂.comp (invMonoidHom (α := Multiplicative M)) * h₁
  have hc1 : ∀ z ∈ N, c (Multiplicative.ofAdd z) = 1 := by
    intro z hz
    have e1 := DFunLike.congr_fun hc (Multiplicative.ofAdd (⟨z, hz⟩ : N))
    have e2 : h₁ (Multiplicative.ofAdd z) = h₂ (Multiplicative.ofAdd z) := e1
    change h₂ (Multiplicative.ofAdd z)⁻¹ * h₁ (Multiplicative.ofAdd z) = 1
    rw [e2, ← map_mul, inv_mul_cancel, map_one]
  have hfix := (hN (g₂ ≫ Gπ M P) c).2 hc1
  have hm : h₁ = (h₂ * c : Multiplicative M →* Γ((SCH).obj Z, ⊤)) := by
    refine MonoidHom.ext fun m => ?_
    change h₁ m = h₂ m * (h₂ m⁻¹ * h₁ m)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have := actX.mul_smul (U := op Z) h₂ c (x.app (op Z) (g₂ ≫ Gπ M P))
  rw [hfix] at this
  rw [hm]
  exact this

/-- **§1**: the orbit map `O = D(M)_P/H → X`, by fpqc descent along `D(M)_P → O`. -/
theorem exists_orbit (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (hN : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ N, h (Multiplicative.ofAdd z) = 1) :
    ∃ o : yoneda.obj (Ob P N) ⟶ X, yoneda.map (qN N) ≫ o = orbMap actX x := by
  have hsh := IsAlgebraicSpace.isSheaf_fpqc hX
  rw [isSheaf_iff_isSheaf_of_type,
    Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange] at hsh
  have hfl := flat_qN (P := P) N hK
  have hsu := surjective_qN (P := P) N hK
  have hR : Presieve.ofArrows (fun _ : Unit => Gk M P) (fun _ => qN N (P := P)) ∈
      Scheme.fpqcPrecoverage.comap (SCH) (Ob P N) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact ofArrows_unit_mem_fpqc' _ hfl hsu inferInstance
  have hF := (Presieve.isSheafFor_arrows_iff X (fun _ : Unit => qN N (P := P))).1 (hsh _ hR)
  obtain ⟨t, ht, -⟩ := hF (fun _ => yonedaEquiv (orbMap actX x)) (by
    intro i j Z g₁ g₂ h
    have e := orbMap_congr hN g₁ g₂ h
    exact (yonedaEquiv_naturality (orbMap actX x) g₁).trans
      (e.trans (yonedaEquiv_naturality (orbMap actX x) g₂).symm))
  refine ⟨yonedaEquiv.symm t, ?_⟩
  apply yonedaEquiv.injective
  have e := yonedaEquiv_naturality (yonedaEquiv.symm t) (qN N (P := P))
  rw [Equiv.apply_symm_apply] at e
  exact e.symm.trans (ht ())

variable {o : yoneda.obj (Ob P N) ⟶ X}

lemma o_comp_qN (ho : yoneda.map (qN N) ≫ o = orbMap actX x) {T : BigFppfOver B S hS}
    (w : T ⟶ Gk M P) : o.app (op T) (w ≫ qN N) =
      actX.smul (U := op T) (secPt ((SCH).map w).appTop.hom (univPt1 (U := P)))
        (x.app (op T) (w ≫ Gπ M P)) :=
  (congrArg (fun z => z.app (op T) w) ho).trans (orbMap_app actX x w)

lemma orbit_equivariant_aux (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (ho : yoneda.map (qN N) ≫ o = orbMap actX x) {T : BigFppfOver B S hS}
    (g : Multiplicative M →* Γ((SCH).obj T, ⊤)) (t : T ⟶ Ob P N) :
    o.app (op T) (oSmul N g t) = actX.smul (U := op T) g (o.app (op T) t) := by
  refine eq_of_cover N hK hX t _ _ ?_
  let f := pullback.fst t (qN N (P := P))
  let w := pullback.snd t (qN N (P := P))
  have hfw : f ≫ t = w ≫ qN N := pullback.condition
  let G : Multiplicative M →* Γ((SCH).obj (pullback t (qN N (P := P))), ⊤) :=
    ((SCH).map f).appTop.hom.toMonoidHom.comp g
  let hw := secPt ((SCH).map w).appTop.hom (univPt1 (U := P))
  obtain ⟨w', hw'π, hw'h⟩ := exists_gkLift (w ≫ Gπ M P) (G * hw)
  have e1 : f ≫ oSmul N g t = w' ≫ qN N := by
    rw [comp_oSmul, hfw]
    refine oSmul_ext N ?_ fun z => ?_
    · rw [oSmul_π, Category.assoc, Category.assoc, qN_π, hw'π]
    · refine (DFunLike.congr_fun (oChar_oSmul N _ _) z).trans ?_
      rw [oChar_qN, oChar_qN, hw'h]
      change hw _ * G _ = G _ * hw _
      exact mul_comm _ _
  have nat : ∀ (y : T ⟶ Ob P N), X.map f.op (o.app (op T) y) = o.app (op _) (f ≫ y) := fun y =>
    (NatTrans.naturality_apply o f.op y).symm
  have lhs : X.map f.op (o.app (op T) (oSmul N g t)) = _ := nat _
  rw [lhs, e1, o_comp_qN ho, hw'π, hw'h]
  refine Eq.trans ?_ (actX.map_smul (U := op T) f.op g (o.app (op T) t)).symm
  rw [nat, hfw, o_comp_qN ho]
  exact actX.mul_smul (U := op _) G hw _

/-- **§1**: the orbit map is equivariant. -/
theorem orbit_equivariant (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (ho : yoneda.map (qN N) ≫ o = orbMap actX x) : IsEquivariant (oAct N) actX o :=
  fun {T} g t => orbit_equivariant_aux hK hX ho (T := T.unop) g t

/-- **§1**: the orbit map is a monomorphism when `X` has a structure map to some `Z'`, invariant
under the action, for which `P → Z'` is a monomorphism (over `ℤ` a monomorphism fails if
`k ≠ 𝔽_p`). -/
theorem orbit_injective (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (hN : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
      actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
        ∀ z ∈ N, h (Multiplicative.ofAdd z) = 1)
    (ho : yoneda.map (qN N) ≫ o = orbMap actX x) {Zp : BigFppfOver B S hS}
    (zS : X ⟶ yoneda.obj Zp)
    (hz : ∀ {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (y : X.obj (op T)),
      zS.app (op T) (actX.smul (U := op T) h y) = zS.app (op T) y)
    (ιz : P ⟶ Zp) [Mono ιz] (hx : x ≫ zS = yoneda.map ιz)
    {T : BigFppfOver B S hS} (a b : T ⟶ Ob P N) (hab : o.app (op T) a = o.app (op T) b) : a = b := by
  have hOb := isAlgebraicSpace_yoneda B S hS (Ob P N)
  refine eq_of_cover N hK hOb a a b ?_
  let f₁ := pullback.fst a (qN N (P := P))
  let w₁ := pullback.snd a (qN N (P := P))
  have h₁ : f₁ ≫ a = w₁ ≫ qN N := pullback.condition
  change f₁ ≫ a = f₁ ≫ b
  refine eq_of_cover N hK hOb (f₁ ≫ b) _ _ ?_
  let f₂ := pullback.fst (f₁ ≫ b) (qN N (P := P))
  let w₂ := pullback.snd (f₁ ≫ b) (qN N (P := P))
  have h₂ : f₂ ≫ f₁ ≫ b = w₂ ≫ qN N := pullback.condition
  change f₂ ≫ f₁ ≫ a = f₂ ≫ f₁ ≫ b
  let v := f₂ ≫ w₁
  have ha : f₂ ≫ f₁ ≫ a = v ≫ qN N := by rw [h₁, Category.assoc]
  rw [ha, h₂]
  have nat : ∀ {T₁ T₂ : BigFppfOver B S hS} (s : T₁ ⟶ T₂) (y : T₂ ⟶ Ob P N),
      o.app (op T₁) (s ≫ y) = X.map s.op (o.app (op T₂) y) := fun s y =>
    NatTrans.naturality_apply o s.op y
  have heq : o.app (op _) (v ≫ qN N) = o.app (op _) (w₂ ≫ qN N) := by
    rw [← ha, ← h₂, nat, nat f₁, nat, nat f₁, hab]
  rw [o_comp_qN ho, o_comp_qN ho] at heq
  have hz' := congrArg (zS.app (op _)) heq
  rw [hz, hz] at hz'
  have ex : ∀ {T₁ : BigFppfOver B S hS} (τ : T₁ ⟶ P), zS.app (op T₁) (x.app (op T₁) τ) = τ ≫ ιz :=
    fun τ => congrArg (fun k => k.app (op _) τ) hx
  rw [ex, ex] at hz'
  have hb := (cancel_mono ιz).1 hz'
  rw [hb] at heq
  set h₁' := secPt ((SCH).map v).appTop.hom (univPt1 (U := P))
  set h₂' := secPt ((SCH).map w₂).appTop.hom (univPt1 (U := P))
  let c : Multiplicative M →* Γ((SCH).obj _, ⊤) :=
    h₂'.comp (invMonoidHom (α := Multiplicative M)) * h₁'
  have hfix : actX.smul (U := op _) c (x.app (op _) (w₂ ≫ Gπ M P)) = x.app (op _) (w₂ ≫ Gπ M P) := by
    let i₂ : Multiplicative M →* Γ((SCH).obj _, ⊤) := h₂'.comp (invMonoidHom (α := Multiplicative M))
    have m := actX.mul_smul (U := op _) i₂ h₁' (x.app (op _) (w₂ ≫ Gπ M P))
    refine m.trans ?_
    rw [heq]
    refine (actX.mul_smul (U := op _) i₂ h₂' _).symm.trans ?_
    have hi : (i₂ * h₂' : Multiplicative M →* Γ((SCH).obj _, ⊤)) = 1 := by
      refine MonoidHom.ext fun m => ?_
      change h₂' m⁻¹ * h₂' m = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    refine (congrArg (fun k : APt (fppfO B S hS) M (op _) => actX.smul k _) hi).trans ?_
    exact actX.one_smul (U := op _) _
  have htr := (hN _ c).1 hfix
  refine oSmul_ext N ?_ fun z => ?_
  · have hq : ∀ {Y : BigFppfOver B S hS} (g : Y ⟶ Gk M P), (g ≫ qN N) ≫ Oπ P N = g ≫ Gπ M P := fun g => by
      rw [Category.assoc, qN_π]
    rw [hq, hq]
    exact hb
  · rw [oChar_qN, oChar_qN]
    have key : ∀ m : Multiplicative M, h₂' m⁻¹ * h₁' m = 1 → h₁' m = h₂' m := by
      intro m e
      have hu : h₂' m * h₂' m⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      calc h₁' m = h₂' m * h₂' m⁻¹ * h₁' m := by rw [hu, one_mul]
        _ = h₂' m := by rw [mul_assoc, e, mul_one]
    exact key _ (htr _ (Multiplicative.toAdd z : N).2)

/-- **§1, summary**: for `x : P → X`, `P` the spectrum of a field, `X` a separated algebraic space
with `D(M)`-action and an invariant map to `Z'` with `P → Z'` a monomorphism: there is `Z₀ ⊆ M` such
that the stabilizer of `x` is `D(M/Z₀)`, and an equivariant injective `O = Spec k[Z₀] → X` restricting
to `x` on the unit section of `O`. -/
theorem exists_orbit_mono (hK : IsField (RT P)) (hX : IsAlgebraicSpace B S hS X)
    (hsep : AlgMag.IsSeparatedOver X) (actX : AAction (fppfO B S hS) M X) (x : yoneda.obj P ⟶ X)
    {Zp : BigFppfOver B S hS} (zS : X ⟶ yoneda.obj Zp)
    (hz : ∀ {T : BigFppfOver B S hS} (h : Multiplicative M →* Γ((SCH).obj T, ⊤)) (y : X.obj (op T)),
      zS.app (op T) (actX.smul (U := op T) h y) = zS.app (op T) y)
    (ιz : P ⟶ Zp) [Mono ιz] (hx : x ≫ zS = yoneda.map ιz) :
    ∃ (Z₀ : AddSubgroup M) (_ : AddMonoid.FG Z₀) (o : yoneda.obj (Ob P Z₀) ⟶ X),
      (∀ {T : BigFppfOver B S hS} (t : T ⟶ P) (h : Multiplicative M →* Γ((SCH).obj T, ⊤)),
        actX.smul (U := op T) h (x.app (op T) t) = x.app (op T) t ↔
          ∀ z ∈ Z₀, h (Multiplicative.ofAdd z) = 1) ∧
      IsEquivariant (oAct Z₀) actX o ∧
      (∀ {T : BigFppfOver B S hS} (a b : T ⟶ Ob P Z₀), o.app (op T) a = o.app (op T) b → a = b) := by
  obtain ⟨Z₀, hZ⟩ := exists_stabilizer hK hsep actX x
  haveI hfg := fg_addSubgroup Z₀
  obtain ⟨o, ho⟩ := exists_orbit (N := Z₀) hK hX hZ
  exact ⟨Z₀, hfg, o, hZ, orbit_equivariant hK hX ho,
    fun a b hab => orbit_injective hK hX hZ ho zS hz ιz hx a b hab⟩

end Orbit

end AlgMag.ChartPoint

#print axioms AlgMag.ChartPoint.exists_stab_ideal
#print axioms AlgMag.ChartPoint.exists_stabilizer
#print axioms AlgMag.ChartPoint.hstab_of_orbit
#print axioms AlgMag.ChartPoint.hOf_of_orbit
#print axioms AlgMag.ChartPoint.free_inclN
#print axioms AlgMag.ChartPoint.exists_orbit
#print axioms AlgMag.ChartPoint.orbit_equivariant
#print axioms AlgMag.ChartPoint.orbit_injective
#print axioms AlgMag.ChartPoint.exists_orbit_mono
