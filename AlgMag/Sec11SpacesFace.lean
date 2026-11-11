/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec11SpacesLift
import AlgMag.Sec11SchemesFace

/-!
# Proposition 11.7 for algebraic spaces

Mayeux, *Algebraic Magnetism*, Proposition 11.7, with Fact 11.8 in the form of Stacks 07SY on
sections of `X`. `#M` is below the cutoff of the site.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.SpacesLift

open AlgMag.GB AlgMag.Lifts AlgMag.SmoothSchemes

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
  [SM B M] (N : AddSubmonoid M) {F : AddSubmonoid M} (hF : IsFace F N)

variable (B S hS) in
/-- `S` as the terminal object of the site over `S`. -/
noncomputable abbrev Ter : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

lemma ter_eq {U : (BigFppfOver B S hS)ᵒᵖ} (a b : (yoneda.obj (Ter B S hS)).obj U) : a = b :=
  (Over.mkIdTerminal (X := B.obj hS)).hom_ext (show unop U ⟶ _ from a) (show unop U ⟶ _ from b)

lemma top_eq {U : (BigFppfOver B S hS)ᵒᵖ} (a b : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj U) :
    a = b :=
  yonedaEquiv.symm.injective (terminal.hom_ext _ _)

/-- The trivial action on `S`. -/
noncomputable def termAct : AAction (fppfO B S hS) M (yoneda.obj (Ter B S hS)) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  map_smul _ _ _ := ter_eq _ _

section Face

variable [DecidableEq M]

lemma lift_faceS (T : BigFppfOver B S hS) [IsAffine (τS T)] [SR B Γ(τS T, ⊤)]
    (s : Spec (CommRingCat.of (RS N (τS T))) ⟶ S)
    (hs : magnetπ N (τS T) ≫ T.hom.hom = s) (s₁ : Spec (CommRingCat.of (RS F (τS T))) ⟶ S)
    (hs₁ : magnetπ F (τS T) ≫ T.hom.hom = s₁) (h : sp (faceRingHom hF Γ(τS T, ⊤)) ≫ s = s₁) :
    (specU N T s hs).lift (specU F T s₁ hs₁).π (APt.faceExt hF (specU F T s₁ hs₁).u) =
      (svHom B hS (faceRingHom hF Γ(τS T, ⊤)) h : Sv B hS s₁ ⟶ Sv B hS s) := by
  symm
  have h1 : (svHom B hS (faceRingHom hF Γ(τS T, ⊤)) h : Sv B hS s₁ ⟶ Sv B hS s) ≫ (specU N T s hs).π =
      (specU F T s₁ hs₁).π := site_ext (face_π N hF (τS T))
  refine (specU N T s hs).uniq _ _ _ h1 ?_
  refine MonoidHom.ext fun n => ?_
  refine (sp_inv _ _).trans ?_
  by_cases hn : ((Multiplicative.toAdd n : N) : M) ∈ F
  · rw [faceRingHom_single_pos hF _ hn]
    exact (APt.faceExt_pos (𝒪 := fppfO B S hS) (U := op (Sv B hS s₁)) hF (specU F T s₁ hs₁).u hn).symm
  · rw [faceRingHom_single_neg hF _ hn, map_zero]
    exact (APt.faceExt_neg (𝒪 := fppfO B S hS) (U := op (Sv B hS s₁)) hF (specU F T s₁ hs₁).u hn).symm

instance srPushout {D D₁ : Type u} [CommRing D] [CommRing D₁] [SR B D] [SR B D₁] (ι : D →+* D₁) :
    SR B (pushoutRing hF ι) := sr_subring _

omit [DecidableEq M] in
set_option maxHeartbeats 3000000 in
/-- **Proposition 11.7** for algebraic spaces: if `X → S` is smooth and `F` is a face of `N`, then
`X^N → X^F` is formally smooth as a transformation of functors. Here `#M` is below the cutoff. -/
theorem isFormallySmooth_faceMap_spaces {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (aX : AAction (fppfO B S hS) M X)
    (hsm : Space.FormallySmooth (terminal.from X)) : IsFormallySmooth (faceMap aX hF) := by
  classical
  intro T₀ T i hi x₀ y hc
  have := hi.affine₀
  have := hi.affine
  haveI : IsAffine (τS T₀) := hi.affine₀
  haveI : IsAffine (τS T) := hi.affine
  haveI := sr_sections T₀
  haveI := sr_sections T
  let e := (BigFppfOver.toScheme B S hS).map i
  let ι := e.appTop.hom
  have hι : Function.Surjective ι := hi.surjective
  let t := magnetπ N (τS T) ≫ T.hom.hom
  let π₁ := pushoutMap hF ι
  have hπs : Function.Surjective π₁ := pushoutMap_surjective hF ι hι
  have hπq : ∀ x y, π₁ x = 0 → π₁ y = 0 → x * y = 0 := pushoutMap_mul_eq_zero hF ι hi.sq_zero
  let sF := sp (faceRingHom hF Γ(τS T, ⊤)) ≫ t
  have hsF : magnetπ F (τS T) ≫ T.hom.hom = sF :=
    ((congrArg (· ≫ T.hom.hom) (face_π N hF (τS T))).symm.trans (Category.assoc _ _ _))
  have hw : e ≫ T.hom.hom = T₀.hom.hom := congrArg (fun k => k.hom) (Over.w i)
  have thick : ∀ (P : AddSubmonoid M), magnetπ P (τS T₀) ≫ T₀.hom.hom =
      sp (AddMonoidAlgebra.mapRingHom P ι) ≫ magnetπ P (τS T) ≫ T.hom.hom := fun P => by
    rw [← hw, ← Category.assoc, piSq P e, Category.assoc]
  let s₀ := sp (AddMonoidAlgebra.mapRingHom N ι) ≫ t
  have hs₀ : magnetπ N (τS T₀) ≫ T₀.hom.hom = s₀ := thick N
  let sF₀ := sp (AddMonoidAlgebra.mapRingHom F ι) ≫ sF
  have hsF₀ : magnetπ F (τS T₀) ≫ T₀.hom.hom = sF₀ :=
    (thick F).trans (congrArg (fun z => sp (AddMonoidAlgebra.mapRingHom F ι) ≫ z) hsF)
  let U := specU N T t rfl
  let UF := specU F T sF hsF
  let U₀ := specU N T₀ s₀ hs₀
  let UF₀ := specU F T₀ sF₀ hsF₀
  let yF : X.obj (op UF.P) := y.app UF.π UF.u
  let x₀U : X.obj (op U₀.P) := x₀.app U₀.π U₀.u
  have hface₀ : sp (faceRingHom hF Γ(τS T₀, ⊤)) ≫ s₀ = sF₀ :=
    tri (sp_sq (RingHom.ext fun w => face_comm hF ι w)) t
  have hmF : (svHom B hS (AddMonoidAlgebra.mapRingHom F ι) rfl : Sv B hS sF₀ ⟶ Sv B hS sF) =
      UF.lift (UF₀.π ≫ i) UF₀.u := by
    refine UF.uniq _ _ _ (site_ext (piSq F e).symm) (MonoidHom.ext fun n => ?_)
    refine (sp_inv _ _).trans (congrArg _ ?_)
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [map_one]
  have hjF := hmF
  have hcomp : pb X (svHom B hS (AddMonoidAlgebra.mapRingHom F ι) rfl : Sv B hS sF₀ ⟶ Sv B hS sF) yF =
      pb X (svHom B hS (faceRingHom hF Γ(τS T₀, ⊤)) hface₀ : Sv B hS sF₀ ⟶ Sv B hS s₀) x₀U := by
    have e' := congrArg (fun z : AttractorPt aX F T₀ => z.app UF₀.π UF₀.u) hc
    have e₁ : x₀.app UF₀.π (APt.faceExt hF UF₀.u) =
        pb X (svHom B hS (faceRingHom hF Γ(τS T₀, ⊤)) hface₀ : Sv B hS sF₀ ⟶ Sv B hS s₀) x₀U := by
      refine (x₀.app_eq_of_universal U₀ _ _).trans ?_
      exact congrArg (fun z : Sv B hS sF₀ ⟶ Sv B hS s₀ => pb X z x₀U)
        (lift_faceS N hF T₀ s₀ hs₀ sF₀ hsF₀ hface₀)
    have e₂ : y.app (UF₀.π ≫ i) UF₀.u =
        pb X (svHom B hS (AddMonoidAlgebra.mapRingHom F ι) rfl : Sv B hS sF₀ ⟶ Sv B hS sF) yF := by
      refine (y.app_eq_of_universal UF _ _).trans ?_
      exact congrArg (fun z : Sv B hS sF₀ ⟶ Sv B hS sF => pb X z yF) hmF.symm
    exact e₂.symm.trans (e'.symm.trans e₁)
  let Pu := pushoutRing hF ι
  let H := milnor_pushout N hF ι hι
  have hspf : sp (pFst N hF ι) ≫ sp π₁ = sp (faceRingHom hF Γ(τS T, ⊤)) := by
    rw [← sp_comp]; rfl
  have hsps : sp (pSnd N hF ι) ≫ sp π₁ = sp (AddMonoidAlgebra.mapRingHom N ι) := by
    rw [← sp_comp]; rfl
  have hpFs : sp (pFst N hF ι) ≫ sp π₁ ≫ t = sF :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hspf)
  have hpSs : sp (pSnd N hF ι) ≫ sp π₁ ≫ t = s₀ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) hsps)
  have hιq : ∀ a b, AddMonoidAlgebra.mapRingHom F ι a = 0 → AddMonoidAlgebra.mapRingHom F ι b = 0 →
      a * b = 0 := magnetAlgebra_mul_eq_zero ι hi.sq_zero
  obtain ⟨a, ⟨hpFa, hpSa⟩, -⟩ := glue H (pSnd_surjective N hF ι hι)
    (fun y hy => pFst_ker N hF ι y hy) hιq hpFs hpSs rfl hface₀ X hX yF x₀U hcomp
  let pF : Sv B hS sF ⟶ Sv B hS (sp π₁ ≫ t) := svHom B hS (pFst N hF ι) hpFs
  let pS : Sv B hS s₀ ⟶ Sv B hS (sp π₁ ≫ t) := svHom B hS (pSnd N hF ι) hpSs
  let ρ := coactN (M := M) N Γ(τS T, ⊤)
  let ρ₀ := coactP (M := M) N hF ι hι
  have hρt : sp ρ ≫ t = sp (cst _ M) ≫ t := rhoS N t rfl
  have hρφ : ∀ w, AddMonoidAlgebra.mapRingHom M π₁ (ρ w) = ρ₀ (π₁ w) := fun w =>
    (coactP_π N hF ι hι w).symm
  have h₀c : sp (cst Pu M) ≫ sp π₁ ≫ t = sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst _ M) ≫ t :=
    tri (sp_sq (RingHom.ext fun w => (map_cst π₁ w).symm)) t
  have h₀ρ : sp ρ₀ ≫ sp π₁ ≫ t = sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst _ M) ≫ t := by
    rw [← hρt]
    exact tri (sp_sq (RingHom.ext fun w => (hρφ w).symm)) t
  let HM := milnor_map (M := M) H
  let s₁ := sp (AddMonoidAlgebra.mapRingHom M π₁) ≫ sp (cst (RS N (τS T)) M) ≫ t
  let sF₁ := sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ s₁
  let s₀₁ := sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ s₁
  have e1F : sp (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) ≫ sp (AddMonoidAlgebra.mapRingHom M π₁) ≫
      sp (cst (RS N (τS T)) M) = sp (cst _ M) ≫ sp (faceRingHom hF Γ(τS T, ⊤)) := by
    rw [← Category.assoc, sp_sq (g₃ := AddMonoidAlgebra.mapRingHom M (faceRingHom hF Γ(τS T, ⊤)))
      (g₄ := RingHom.id _) (RingHom.ext fun w => map_map_apply _ _ _ (fun _ => rfl) w), sp_id',
      Category.id_comp]
    exact sp_sq (RingHom.ext fun w => map_cst _ w)
  have e1S : sp (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) ≫ sp (AddMonoidAlgebra.mapRingHom M π₁) ≫
      sp (cst (RS N (τS T)) M) = sp (cst _ M) ≫ sp (AddMonoidAlgebra.mapRingHom N ι) := by
    rw [← Category.assoc, sp_sq (g₃ := AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom N ι))
      (g₄ := RingHom.id _) (RingHom.ext fun w => map_map_apply _ _ _ (fun _ => rfl) w), sp_id',
      Category.id_comp]
    exact sp_sq (RingHom.ext fun w => map_cst _ w)
  have hF₁c : sp (cst _ M) ≫ sF = sF₁ := (tri3 e1F t).symm
  have hS₁c : sp (cst _ M) ≫ s₀ = s₀₁ := (tri3 e1S t).symm
  have hF₁ρ : sp (coactN (M := M) F Γ(τS T, ⊤)) ≫ sF = sF₁ := (rhoS F sF hsF).trans hF₁c
  have hS₁ρ : sp (coactN (M := M) N Γ(τS T₀, ⊤)) ≫ s₀ = s₀₁ := (rhoS N s₀ hs₀).trans hS₁c
  let PM : Sv B hS sF₁ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) rfl
  let QM : Sv B hS s₀₁ ⟶ Sv B hS s₁ := svHom B hS (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) rfl
  have ha : pb X (svHom B hS ρ₀ h₀ρ) a =
      ss aX (eS B hS s₁ (eU Pu M)) (pb X (svHom B hS (cst Pu M) h₀c) a) := by
    have hsqM : (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom F ι)).comp
        (AddMonoidAlgebra.mapRingHom M (pFst N hF ι)) =
        (AddMonoidAlgebra.mapRingHom M (faceRingHom hF Γ(τS T₀, ⊤))).comp
          (AddMonoidAlgebra.mapRingHom M (pSnd N hF ι)) := RingHom.ext fun w => HM.comm w
    have hd₀ : sp (AddMonoidAlgebra.mapRingHom M (faceRingHom hF Γ(τS T₀, ⊤))) ≫ s₀₁ =
        sp (AddMonoidAlgebra.mapRingHom M (AddMonoidAlgebra.mapRingHom F ι)) ≫ sF₁ :=
      (tri (sp_sq hsqM) s₁).symm
    refine (glue HM (mapRingHom_surjective _ (pSnd_surjective N hF ι hι)) (fun y hy => by
        obtain ⟨z, h₁, h₂⟩ := HM.ex y 0 (by rw [hy, map_zero])
        exact ⟨z, h₁, h₂⟩)
      (map_sq_zero _ hιq) rfl rfl rfl hd₀ X hX _ _ ?_).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · refine pb_sq X ?_ _
      exact site_ext (sp_sq hsqM)
    · have l₁ := pb_sq X (u := PM) (v := svHom B hS (cst Pu M) h₀c)
        (w := svHom B hS (cst _ M) hF₁c) (x := pF) (site_ext (sp_sq (RingHom.ext fun p => map_cst _ p))) a
      have l₃ : APt.res PM.op (eS B hS s₁ (eU Pu M)) = eS B hS sF₁ (eU _ M) :=
        (res_eS _ _ _).trans (eS_congr _ (hof _))
      have l₀ := pb_sq X (u := PM) (v := svHom B hS ρ₀ h₀ρ)
        (w := svHom B hS (coactN (M := M) F Γ(τS T, ⊤)) hF₁ρ) (x := pF)
        (site_ext (sp_sq (RingHom.ext fun p => coactP_fst N hF ι hι p))) a
      refine Eq.symm ?_
      rw [pb_ss, l₃, l₁]
      refine l₀.trans ?_
      have hpFa' : pb X pF a = yF := hpFa
      rw [hpFa']
      exact equiv_of_attPtS F sF hsF y sF₁ hF₁c hF₁ρ
    · have l₁ := pb_sq X (u := QM) (v := svHom B hS (cst Pu M) h₀c)
        (w := svHom B hS (cst _ M) hS₁c) (x := pS) (site_ext (sp_sq (RingHom.ext fun p => map_cst _ p))) a
      have l₃ : APt.res QM.op (eS B hS s₁ (eU Pu M)) = eS B hS s₀₁ (eU _ M) :=
        (res_eS _ _ _).trans (eS_congr _ (hof _))
      have l₀ := pb_sq X (u := QM) (v := svHom B hS ρ₀ h₀ρ)
        (w := svHom B hS (coactN (M := M) N Γ(τS T₀, ⊤)) hS₁ρ) (x := pS)
        (site_ext (sp_sq (RingHom.ext fun p => coactP_snd N hF ι hι p))) a
      refine Eq.symm ?_
      rw [pb_ss, l₃, l₁]
      refine l₀.trans ?_
      have hpSa' : pb X pS a = x₀U := hpSa
      rw [hpSa']
      exact equiv_of_attPtS N s₀ hs₀ x₀ s₀₁ hS₁c hS₁ρ
  have hthick : Space.IsSquareZeroClosedImmersion B S hS (svHom B hS π₁ (s := t) rfl) :=
    sqZero_svHom π₁ hπs hπq
  let w₀ : (yoneda.obj (Ter B S hS)).obj (op (Sv B hS t)) :=
    (Over.mkIdTerminal (X := B.obj hS)).from _
  obtain ⟨α, hα₁, -⟩ := hsm _ _ (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsAffine (Spec _))) (svHom B hS π₁ (s := t) rfl) hthick a
    ((terminal.from (yoneda.obj (Ter B S hS))).app _ w₀) (top_eq _ _)
  let eqT : EquivariantHom aX (termAct (M := M) (B := B) (S := S) (hS := hS)) :=
    { hom := { app := fun U => TypeCat.ofHom fun _ => (Over.mkIdTerminal (X := B.obj hS)).from _
               naturality := fun _ _ _ => by ext x; exact ter_eq _ _ }
      map_smul := fun _ _ => ter_eq _ _ }
  obtain ⟨l, hl₁, -, hl₃⟩ := exists_equivariant_of_lift π₁ hπs hπq t ρ ρ₀ hρt hρφ
    (coactN_coassoc N _) hX (isAlgebraicSpace_yoneda B S hS _) eqT a w₀ α hα₁
    (ter_eq _ _) h₀ρ h₀c ha (ter_eq _ _)
  have a1 : (attPtOfS N t rfl l hρt hl₃).app U.π U.u = l := attPtOfS_app N t rfl l hρt hl₃
  have hπ₁l : pb X (svHom B hS (faceRingHom hF Γ(τS T, ⊤)) rfl : Sv B hS sF ⟶ Sv B hS t) l = yF := by
    have sq : (svHom B hS (faceRingHom hF Γ(τS T, ⊤)) rfl : Sv B hS sF ⟶ Sv B hS t) =
        pF ≫ svHom B hS π₁ rfl := site_ext hspf.symm
    rw [sq, pb_comp, hl₁]
    exact hpFa
  have hπ₂l : pb X (svHom B hS (AddMonoidAlgebra.mapRingHom N ι) rfl : Sv B hS s₀ ⟶ Sv B hS t) l = x₀U := by
    have sq : (svHom B hS (AddMonoidAlgebra.mapRingHom N ι) rfl : Sv B hS s₀ ⟶ Sv B hS t) =
        pS ≫ svHom B hS π₁ rfl := site_ext hsps.symm
    rw [sq, pb_comp, hl₁]
    exact hpSa
  refine ⟨attPtOfS N t rfl l hρt hl₃, ?_, ?_⟩
  · refine (attractorPtEquivOfUniversal (act := aX) U₀).injective (Subtype.ext ?_)
    change (attPtOfS N t rfl l hρt hl₃).app (U₀.π ≫ i) U₀.u = x₀U
    refine ((attPtOfS N t rfl l hρt hl₃).app_eq_of_universal U _ _).trans ?_
    refine (congrArg (fun z : X.obj (op U.P) => pb X (U.lift (U₀.π ≫ i) U₀.u) z) a1).trans ?_
    have hj : (svHom B hS (AddMonoidAlgebra.mapRingHom N ι) rfl : Sv B hS s₀ ⟶ Sv B hS t) =
        U.lift (U₀.π ≫ i) U₀.u := by
      refine U.uniq _ _ _ (site_ext (piSq N e).symm) (MonoidHom.ext fun n => ?_)
      refine (sp_inv _ _).trans (congrArg _ ?_)
      refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
      rw [map_one]
    exact (congrArg (fun z => pb X z l) hj.symm).trans hπ₂l
  · refine (attractorPtEquivOfUniversal (act := aX) UF).injective (Subtype.ext ?_)
    change (attPtOfS N t rfl l hρt hl₃).app UF.π (APt.faceExt hF UF.u) = yF
    refine ((attPtOfS N t rfl l hρt hl₃).app_eq_of_universal U _ _).trans ?_
    refine (congrArg (fun z : X.obj (op U.P) => pb X (U.lift UF.π (APt.faceExt hF UF.u)) z) a1).trans ?_
    exact (congrArg (fun z => pb X z l) (lift_faceS N hF T t rfl sF hsF rfl)).trans hπ₁l

end Face

end AlgMag.SpacesLift
