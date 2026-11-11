/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBaseLocal

/-!
# Theorem 3.20 over an affine open of the base

For `U ⊆ S` affine, `X → S` affine with an action of `𝔸(M)_S`, and `T` over `U`, affine or not:
`X^N(T) = Hom_R(A / J_N, Γ(T, ⊤))` (`AlgMag.GB.localEquiv`).
-/

suppress_compilation

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

open scoped Classical

universe u

namespace AlgMag.GB

attribute [local instance] gradedAlgebraOf

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U) {M : Type u} [AddCommMonoid M]
variable {X : Over S} [IsAffineHom X.hom] (act : AAction (overO S) M (yoneda.obj X))
variable (N : AddSubmonoid M)

/-- The value of an attractor point over a morphism `T' → T`, for a graded map `A → Γ(T, ⊤)[N]`. -/
def grVal {T T' : Over S} (hT : LiesOver T U) (s : T' ⟶ T) (a : APt (overO S) N (op T'))
    (f : Attractor (gradingOf hU act) N (Ga hU T hT)) : T' ⟶ X :=
  (ptX X hU T' (hT.of_hom s)).symm
    ((evalAlg (gpull hU hT (hT.of_hom s) s) (toGa hU (hT.of_hom s) a)).comp f.toAlgHom)

/-- A graded map `A → Γ(T, ⊤)[N]` defines a point of the attractor of Definition 3.1. -/
def ptGr {T : Over S} (hT : LiesOver T U) (f : Attractor (gradingOf hU act) N (Ga hU T hT)) :
    AttractorPt act N T where
  app s a := grVal hU act N hT s a f
  naturality {T' T''} s t a := by
    have ht' := hT.of_hom t
    have ht'' := ht'.of_hom s
    change grVal hU act N hT (s ≫ t) _ f = s ≫ grVal hU act N hT t a f
    rw [grVal, grVal, ← ptX_symm_comp X hU ht' ht'', ← AlgHom.comp_assoc]
    congr 2
    rw [comp_evalAlg, gpull_comp hU hT ht' ht'']
    rfl
  equivariant {T'} t h a := by
    have ht := hT.of_hom t
    apply (ptX X hU T' ht).injective
    refine algHom_ext_of_homogeneous (D := Ga hU T' ht) (gradingOf hU act) fun m x hx => ?_
    change ptX X hU T' ht (grVal hU act N hT t _ f) x =
      ptX X hU T' ht (act.smul h (grVal hU act N hT t a f)) x
    rw [ptX_smul_of_mem hU act ht h _ hx, grVal, grVal, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact evalAlg_mul_graded (D := Ga hU T' ht) _ (toGa hU ht h) (toGa hU ht a) f hx

lemma evalAlg_id_one {C : Type u} [CommRing C] [Algebra Γ(S, U) C] (x : AddMonoidAlgebra C N) :
    evalAlg (N := N) (R := Γ(S, U)) (AlgHom.id _ C) 1 x = magnetAug N C x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n c => simp

lemma toPoint_ptGr {T : Over S} (hT : LiesOver T U)
    (f : Attractor (gradingOf hU act) N (Ga hU T hT)) :
    ptX X hU T hT (ptGr hU act N hT f).toPoint = attractorPoint (gradingOf hU act) f := by
  change ptX X hU T hT (grVal hU act N hT (𝟙 T) 1 f) = _
  rw [grVal, Equiv.apply_symm_apply]
  refine AlgHom.ext fun a => ?_
  have e : gpull hU hT (hT.of_hom (𝟙 T)) (𝟙 T) = AlgHom.id _ _ := gpull_id hU hT
  change evalAlg (gpull hU hT (hT.of_hom (𝟙 T)) (𝟙 T)) (toGa hU _ 1) (f a) = _
  rw [e]
  exact evalAlg_id_one (U := U) N (f a)

/-- Base change does not change the construction of the point. -/
lemma toPoint_baseChange {T T' : Over S} (s : T' ⟶ T) (φ : AttractorPt act N T) :
    (φ.baseChange s).toPoint = s ≫ φ.toPoint := by
  have h := φ.naturality s (𝟙 T) 1
  have hone : APt.res (𝒪 := overO S) (P := N) s.op 1 = 1 := by
    ext p
    simp
  rw [hone, Category.comp_id] at h
  change φ.app (𝟙 T' ≫ s) 1 = _
  rw [Category.id_comp]
  exact h

lemma PhiMap_id (D : CommAlgCat.{u} Γ(S, U)) : PhiMap hU (AlgHom.id _ D) = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change Spec.map (𝟙 _) = 𝟙 _
  simp

lemma PhiMap_comp {D D' D'' : CommAlgCat.{u} Γ(S, U)} (t : D →ₐ[Γ(S, U)] D')
    (t' : D' →ₐ[Γ(S, U)] D'') : PhiMap hU (t'.comp t) = PhiMap hU t' ≫ PhiMap hU t := by
  refine Over.OverMorphism.ext ?_
  change Spec.map (CommRingCat.ofHom t.toRingHom ≫ CommRingCat.ofHom t'.toRingHom) = _
  rw [Spec.map_comp]
  rfl

/-- A point of `𝔸(P)` over `D`, as a point over `Spec D`. -/
def etaPt {P : Type u} [AddCommMonoid P] (D : CommAlgCat.{u} Γ(S, U)) (a : Multiplicative P →* D) :
    APt (overO S) P (op (Phi hU D)) :=
  ofGa hU (liesOver_Phi hU D) (((eta hU D) : D →* _).comp a)

lemma etaPt_res {P : Type u} [AddCommMonoid P] {D D' : CommAlgCat.{u} Γ(S, U)}
    (σ : D →ₐ[Γ(S, U)] D') (a : Multiplicative P →* D) :
    etaPt hU D' (((σ : D →* D')).comp a) = APt.res (PhiMap hU σ).op (etaPt hU D a) := by
  refine MonoidHom.ext fun n => ?_
  exact (DFunLike.congr_fun (gpull_PhiMap_eta hU σ) (a n)).symm

variable (X) in
/-- A point of `X` over `Spec D`, as an algebra map `A → D`. -/
def backX (D : CommAlgCat.{u} Γ(S, U)) (x : Phi hU D ⟶ X) : Aalg X U →ₐ[Γ(S, U)] D :=
  ((etaEquiv hU D).symm.toAlgHom).comp (ptX X hU _ (liesOver_Phi hU D) x)

omit [IsAffineHom X.hom] in
lemma eta_backX_aux [IsAffineHom X.hom] (D : CommAlgCat.{u} Γ(S, U)) (x : Phi hU D ⟶ X) (a : Aalg X U) :
    eta hU D (backX hU X D x a) = ptX X hU _ (liesOver_Phi hU D) x a :=
  (etaEquiv hU D).apply_symm_apply _

lemma backX_comp {D D' : CommAlgCat.{u} Γ(S, U)} (σ : D →ₐ[Γ(S, U)] D') (x : Phi hU D ⟶ X) :
    backX hU X D' (PhiMap hU σ ≫ x) = (σ : D →ₐ[Γ(S, U)] D').comp (backX hU X D x) := by
  refine AlgHom.ext fun a => (eta_bijective hU D').1 ?_
  rw [eta_backX_aux, ptX_PhiMap_comp, AlgHom.comp_apply, AlgHom.comp_apply]
  have h1 := DFunLike.congr_fun (gpull_PhiMap_eta hU σ) (backX hU X D x a)
  rw [AlgHom.comp_apply, eta_backX_aux] at h1
  exact h1

lemma toAff_nat {C D D' : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C))
    (σ : D →ₐ[Γ(S, U)] D') (τ : C →ₐ[Γ(S, U)] D) (a : Multiplicative N →* D) :
    backX hU X D' (φ.app (PhiMap hU (σ.comp τ)) (etaPt hU D' ((σ : D →* D').comp a))) =
      σ.comp (backX hU X D (φ.app (PhiMap hU τ) (etaPt hU D a))) := by
  have a1 := φ.naturality (PhiMap hU σ) (PhiMap hU τ) (etaPt hU D a)
  have a2 := PhiMap_comp hU τ σ
  have a3 := etaPt_res hU σ a
  have e : φ.app (PhiMap hU (σ.comp τ)) (etaPt hU D' ((σ : D →* D').comp a)) =
      PhiMap hU σ ≫ φ.app (PhiMap hU τ) (etaPt hU D a) :=
    (congrArg₂ (fun (f : Phi hU D' ⟶ Phi hU C) b => φ.app f b) a2 a3).trans a1
  exact (congrArg (backX hU X D') e).trans (backX_comp hU σ _)

lemma toAff_equiv {C D : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C))
    (τ : C →ₐ[Γ(S, U)] D) (h : Multiplicative M →* D) (a : Multiplicative N →* D) :
    backX hU X D (φ.app (PhiMap hU τ)
        (etaPt hU D ((h.comp (AddMonoidHom.toMultiplicative N.subtype)) * a))) =
      gradedSmul (gradingOf hU act) h (backX hU X D (φ.app (PhiMap hU τ) (etaPt hU D a))) := by
  have hD := liesOver_Phi hU D
  have he := φ.equivariant (PhiMap hU τ) (etaPt hU D h) (etaPt hU D a)
  have h3 : APt.toMagnet N (etaPt hU D h) * etaPt hU D a =
      etaPt hU D ((h.comp (AddMonoidHom.toMultiplicative N.subtype)) * a) := by
    refine MonoidHom.ext fun n => ?_
    exact (map_mul (eta hU D) _ _).symm
  rw [h3] at he
  refine (congrArg (backX hU X D) he).trans ?_
  refine algHom_ext_of_homogeneous (D := D) (gradingOf hU act) fun m x hx => ?_
  refine Eq.trans ?_ (gradedSmul_apply_of_mem (D := D) (gradingOf hU act) _ _ hx).symm
  refine (eta_bijective hU D).1 ?_
  rw [eta_backX_aux, ptX_smul_of_mem hU act hD _ _ hx, map_mul]
  exact congrArg₂ (· * ·) rfl (eta_backX_aux hU D _ x).symm

/-- Restriction of a point of the attractor over `Spec C` to the category of affine `U`-schemes,
where the action is the one of the grading. -/
def toAff {C : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C)) :
    AttractorPt (gradedAction (gradingOf hU act)) N (op C) where
  app {T'} t a := backX hU X (unop T') (φ.app (PhiMap hU t.unop.hom) (etaPt hU (unop T') a))
  naturality {_ _} s t a := toAff_nat hU act N φ s.unop.hom t.unop.hom a
  equivariant {_} t h a := toAff_equiv hU act N φ t.unop.hom h a

variable {N} in
/-- The graded map `A → C[N]` attached to an attractor point over `Spec C`. -/
def grOf {C : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C)) :
    Attractor (gradingOf hU act) N C :=
  attractorPtEquiv (gradingOf hU act) N C (toAff hU act N φ)

variable {N} in
lemma toAff_app {C D : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C))
    (t : C →ₐ[Γ(S, U)] D) (a : Multiplicative N →* D) :
    backX hU X D (φ.app (PhiMap hU t) (etaPt hU D a)) =
      (evalAlg t a).comp (grOf hU act φ).toAlgHom := by
  have h := (attractorPtEquiv (gradingOf hU act) N C).symm_apply_apply (toAff hU act N φ)
  have h2 := congrArg (fun ψ : AttractorPt (gradedAction (gradingOf hU act)) N (op C) =>
    ψ.app (T' := op D) (CommAlgCat.ofHom t).op a) h
  exact h2.symm

variable {N} in
lemma backX_toPoint {C : CommAlgCat.{u} Γ(S, U)} (φ : AttractorPt act N (Phi hU C)) :
    backX hU X C φ.toPoint = attractorPoint (gradingOf hU act) (grOf hU act φ) := by
  have h := toAff_app hU act φ (AlgHom.id _ C) 1
  have e1 : PhiMap hU (AlgHom.id _ C) = 𝟙 _ := PhiMap_id hU C
  have e2 : etaPt hU C (1 : Multiplicative N →* C) = 1 := by
    refine MonoidHom.ext fun n => ?_
    exact map_one (eta hU C)
  rw [e1, e2] at h
  refine h.trans (AlgHom.ext fun a => ?_)
  exact evalAlg_id_one (U := U) N _

variable {N} in
/-- Over `Spec C`, a point of the attractor is determined by its underlying point of `X`. -/
lemma app_eq_of_toPoint_eq {C D : CommAlgCat.{u} Γ(S, U)} (φ φ' : AttractorPt act N (Phi hU C))
    (h : φ.toPoint = φ'.toPoint) (t : C →ₐ[Γ(S, U)] D) (b : APt (overO S) N (op (Phi hU D))) :
    φ.app (PhiMap hU t) b = φ'.app (PhiMap hU t) b := by
  have hg : grOf hU act φ = grOf hU act φ' := by
    apply attractorPoint_injective
    rw [← backX_toPoint, ← backX_toPoint, h]
  obtain ⟨a, rfl⟩ : ∃ a : Multiplicative N →* D, etaPt hU D a = b := by
    refine ⟨(((etaEquiv hU D).symm : _ ≃* _).toMonoidHom).comp (toGa hU (liesOver_Phi hU D) b), ?_⟩
    refine MonoidHom.ext fun n => ?_
    exact (etaEquiv hU D).apply_symm_apply _
  have k1 := toAff_app hU act φ t a
  have k2 := toAff_app hU act φ' t a
  rw [hg] at k1
  have k := k1.trans k2.symm
  apply (ptX X hU _ (liesOver_Phi hU D)).injective
  refine AlgHom.ext fun x => ?_
  exact (eta_backX_aux hU D _ x).symm.trans
    ((congrArg (eta hU D) (DFunLike.congr_fun k x)).trans (eta_backX_aux hU D _ x))

/-- `Spec Γ(T, ⊤) = T` for `T` affine over `U`. -/
def toSpecHom (T : Over S) (hT : LiesOver T U) : T ⟶ Phi hU (Ga hU T hT) :=
  (homPhi hU T hT _).symm (AlgHom.id _ _)

instance isIso_toSpecHom (T : Over S) (hT : LiesOver T U) [IsAffine T.left] :
    IsIso (toSpecHom hU T hT) := by
  have : IsIso (toSpecHom hU T hT).left := by
    have h0 : IsIso T.left.toSpecΓ := IsAffine.affine
    have e : CommRingCat.ofHom (AlgHom.id Γ(S, U) (Ga hU T hT)).toRingHom = 𝟙 _ := rfl
    have h1 : IsIso (Spec.map (CommRingCat.ofHom (AlgHom.id Γ(S, U) (Ga hU T hT)).toRingHom)) := by
      rw [e]
      infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ T.left.toSpecΓ _ h0 h1
  have : IsIso ((Over.forget S).map (toSpecHom hU T hT)) := this
  exact isIso_of_reflects_iso _ (Over.forget S)

include hU in
variable {N} in
/-- For `T` affine over `U`, a point of `X^N(T)` is determined by the underlying point of `X`, at
least on identity. -/
lemma app_eq_of_affine {T W : Over S} (hT : LiesOver T U) (φ φ' : AttractorPt act N T)
    (h : φ.toPoint = φ'.toPoint) (s : W ⟶ T) [IsAffine W.left] (a : APt (overO S) N (op W)) :
    φ.app s a = φ'.app s a := by
  have hW := hT.of_hom s
  let e := toSpecHom hU W hW
  let i := inv e
  let β := φ.baseChange (i ≫ s)
  let β' := φ'.baseChange (i ≫ s)
  have hb : β.toPoint = β'.toPoint := by
    rw [toPoint_baseChange, toPoint_baseChange, h]
  have := app_eq_of_toPoint_eq hU act β β' hb (AlgHom.id _ _) (APt.res i.op a)
  have e1 : PhiMap hU (AlgHom.id _ (Ga hU W hW)) = 𝟙 _ := PhiMap_id hU _
  rw [e1] at this
  have this' : φ.app (𝟙 _ ≫ i ≫ s) (APt.res i.op a) = φ'.app (𝟙 _ ≫ i ≫ s) (APt.res i.op a) := this
  rw [Category.id_comp, φ.naturality, φ'.naturality] at this'
  have h3 := congrArg (fun y => e ≫ y) this'
  simpa [i] using h3

/-- The affine chart `Spec Γ(W_i, ⊤)`-pieces of a scheme over `S`. -/
def coverOver (T : Over S) (i : T.left.affineCover.I₀) : Over S :=
  Over.mk (T.left.affineCover.f i ≫ T.hom)

/-- The inclusion of an affine piece. -/
def coverHom (T : Over S) (i : T.left.affineCover.I₀) : coverOver T i ⟶ T :=
  Over.homMk (T.left.affineCover.f i) rfl

instance (T : Over S) (i : T.left.affineCover.I₀) : IsAffine (coverOver T i).left :=
  inferInstanceAs (IsAffine (T.left.affineCover.X i))

lemma over_hom_ext_cover {T Y : Over S} (f g : T ⟶ Y)
    (h : ∀ i, coverHom T i ≫ f = coverHom T i ≫ g) : f = g := by
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_)
  exact congrArg (fun k => k.left) (h i)

include hU in
variable {N} in
/-- **Theorem 3.20, monomorphism part, over `U`**: for `T` over `U`, affine or not, the map
`X^N(T) → X(T)` is injective. -/
theorem toPoint_injective {T : Over S} (hT : LiesOver T U) :
    Function.Injective (AttractorPt.toPoint (act := act) (N := N) (T := T)) := by
  intro φ φ' h
  refine AttractorPt.ext ?_
  funext T' s a
  refine over_hom_ext_cover _ _ fun i => ?_
  have h1 := φ.naturality (coverHom T' i) s a
  have h2 := φ'.naturality (coverHom T' i) s a
  change _ = coverHom T' i ≫ _ at h1
  change _ = coverHom T' i ≫ _ at h2
  rw [← h1, ← h2]
  exact app_eq_of_affine hU act hT φ φ' h _ _

/-- A section of a scheme vanishes as soon as it vanishes on an open cover. -/
lemma section_eq_zero_of_cover {T : Scheme.{u}} (s : Γ(T, ⊤))
    (h : ∀ i, (T.affineCover.f i).appTop.hom s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext T.sheaf ⊤ s 0 fun x hx => ?_
  obtain ⟨i, y, rfl⟩ := T.affineCover.exists_eq x
  have hinj : Function.Injective ((T.affineCover.f i).stalkMap y) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  refine hinj ?_
  have h1 := Scheme.Hom.germ_stalkMap_apply (T.affineCover.f i) ⊤ y hx s
  have h2 := Scheme.Hom.germ_stalkMap_apply (T.affineCover.f i) ⊤ y hx 0
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  rw [map_zero]
  exact h i

/-- **Theorem 3.20, closed part, over `U`**: the underlying point of a point of `X^N(T)` kills
`J_N`. -/
theorem toPoint_kills {T : Over S} (hT : LiesOver T U) (φ : AttractorPt act N T) {a : Aalg X U}
    (ha : a ∈ magnetIdeal (gradingOf hU act) N) :
    ptX X hU T hT φ.toPoint a = 0 := by
  refine section_eq_zero_of_cover _ fun i => ?_
  let W := coverOver T i
  let w := coverHom T i
  have hW := hT.of_hom w
  let e := toSpecHom hU W hW
  let β := φ.baseChange (inv e ≫ w)
  have hb : ptX X hU _ (liesOver_Phi hU _) β.toPoint a = 0 := by
    rw [← eta_backX_aux, backX_toPoint]
    rw [show attractorPoint (gradingOf hU act) (grOf hU act β) a = 0 from
      psiAux_eq_zero_of_mem_magnetIdeal _ ha, map_zero]
  rw [toPoint_baseChange] at hb
  have h3 : ptX X hU W hW (w ≫ φ.toPoint) a = 0 := by
    have h4 : e ≫ inv e ≫ w ≫ φ.toPoint = w ≫ φ.toPoint := by simp
    rw [← h4, ptX_comp X hU (liesOver_Phi hU _) hW]
    rw [AlgHom.comp_apply, Category.assoc] at *
    rw [hb, map_zero]
  rw [ptX_comp X hU hT hW] at h3
  exact h3

/-- **Theorem 3.20 over `U`**: for `T` over the affine open `U` of `S`, affine or not,
`X^N(T) = Hom_R(A / J_N, Γ(T, ⊤))`. -/
def localEquiv {T : Over S} (hT : LiesOver T U) :
    AttractorPt act N T ≃
      ((Aalg X U ⧸ magnetIdeal (gradingOf hU act) N) →ₐ[Γ(S, U)] Ga hU T hT) where
  toFun φ := Ideal.Quotient.liftₐ _ (ptX X hU T hT φ.toPoint) fun _ ha =>
    toPoint_kills hU act N hT φ ha
  invFun F := ptGr hU act N hT (attractorEquiv (gradingOf hU act) N _ F)
  left_inv φ := by
    apply toPoint_injective hU act hT
    apply (ptX X hU T hT).injective
    rw [toPoint_ptGr]
    refine AlgHom.ext fun a => ?_
    exact attractorPoint_attractorEquiv _ a
  right_inv F := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change ptX X hU T hT (ptGr hU act N hT _).toPoint a = _
    rw [toPoint_ptGr]
    exact attractorPoint_attractorEquiv F a

/-- The underlying point of the point of `X^N(T)` attached to `F : A / J_N → Γ(T, ⊤)` is
`A → A / J_N → Γ(T, ⊤)`. -/
theorem ptX_toPoint_localEquiv_symm {T : Over S} (hT : LiesOver T U)
    (F : (Aalg X U ⧸ magnetIdeal (gradingOf hU act) N) →ₐ[Γ(S, U)] Ga hU T hT) :
    ptX X hU T hT ((localEquiv hU act N hT).symm F).toPoint =
      F.comp (Ideal.Quotient.mkₐ _ _) := by
  change ptX X hU T hT (ptGr hU act N hT _).toPoint = _
  rw [toPoint_ptGr]
  exact AlgHom.ext fun a => attractorPoint_attractorEquiv F a

end AlgMag.GB
