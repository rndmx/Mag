/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3LeftoverAttr

/-!
# Algebraic Magnetism, Proposition 3.28 over an arbitrary scheme: the functor form

`AlgMag.VB.vAttractorIso`: `V(E)^N ≅ V(E_N)` as functors on `Sch/S`, where `V(-)` is
`T ↦ Hom_{𝒪_S}(-, p_* 𝒪_T)`, the functor of points of `Spec_S Sym(-)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

open scoped Classical

variable {S : Scheme.{u}} {M : Type u} [AddCommMonoid M] (G : GrMod S M) (N : AddSubmonoid M)

/-- `E_N = ⨁_{n ∈ N} E_n`, the `N`-graded component of `E`. -/
def GrMod.EN : S.Modules := ∐ fun n : N => G.P n

/-- The inclusion `E_n → E_N`. -/
def GrMod.ιN (n : N) : G.P n ⟶ G.EN N := Sigma.ι (fun n : N => G.P n) n

lemma GrMod.EN_ext {Q : S.Modules} {f g : G.EN N ⟶ Q} (h : ∀ n, G.ιN N n ≫ f = G.ιN N n ≫ g) :
    f = g :=
  Sigma.hom_ext _ _ h

variable {T : Over S}

/-- The component `E_m → p'_* 𝒪_{T'}` of the point attached to `l : E_N → p_* 𝒪_T`, at `a` over `t`. -/
def ptComp (l : G.EN N ⟶ pO T) {T' : Over S} (t : T' ⟶ T) (a : APt (overO S) N (op T')) (m : M) :
    G.P m ⟶ pO T' :=
  if hm : m ∈ N then
    G.ιN N ⟨m, hm⟩ ≫ l ≫ resO t ≫ mulO T' (a (Multiplicative.ofAdd ⟨m, hm⟩))
  else 0

lemma resO_comp_mulO {T T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T) (r : Γ(T'.left, ⊤)) :
    resO (s ≫ t) ≫ mulO T'' (s.left.appTop.hom r) = resO t ≫ mulO T' r ≫ resO s := by
  rw [mulO_resO, resO_comp, Category.assoc]

lemma val_zero {V : S.Opens} (hV : IsAffineOpen V) {P : S.Modules} {T : Over S} (hT : LiesOver T V)
    (x : Γ(P, V)) : val hV hT (0 : P ⟶ pO T) x = 0 :=
  map_zero (T.left.presheaf.map (homOfLE (le_of_eq hT.symm)).op).hom

lemma ptComp_res (l : G.EN N ⟶ pO T) {T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) (m : M) :
    ptComp G N l (s ≫ t) (APt.res s.op a) m = ptComp G N l t a m ≫ resO s := by
  unfold ptComp
  by_cases hm : m ∈ N
  · simp only [dif_pos hm, Category.assoc]
    exact congrArg (fun k => G.ιN N ⟨m, hm⟩ ≫ l ≫ k)
      (resO_comp_mulO s t (a (Multiplicative.ofAdd ⟨m, hm⟩)))
  · simp only [dif_neg hm, zero_comp]

/-- The point of `V(E)^N` attached to `l : E_N → p_* 𝒪_T`. -/
def ptOf (l : G.EN N ⟶ pO T) : AttractorPt (vAction G) N T where
  app {T'} t a := G.desc (ptComp G N l t a)
  naturality {T' T''} s t a := by
    change G.desc (ptComp G N l (s ≫ t) (APt.res s.op a)) = G.desc (ptComp G N l t a) ≫ resO s
    refine G.hom_ext fun m => ?_
    rw [G.ι_desc, G.ι_desc_assoc, ptComp_res]
  equivariant {T'} t h a := by
    change G.desc (ptComp G N l t (APt.toMagnet N h * a)) =
      vSmul G h (G.desc (ptComp G N l t a))
    refine G.hom_ext fun m => ?_
    rw [G.ι_desc, ι_vSmul, G.ι_desc_assoc]
    unfold ptComp
    by_cases hm : m ∈ N
    · simp only [dif_pos hm, Category.assoc]
      refine congrArg (fun k => G.ιN N ⟨m, hm⟩ ≫ l ≫ resO t ≫ k) ?_
      exact mulO_mul T' (h (Multiplicative.ofAdd m)) (a (Multiplicative.ofAdd ⟨m, hm⟩))
    · simp only [dif_neg hm, zero_comp]

variable {G N}

/-- A value of a point of `V(E)^N`, as a morphism of modules. -/
def ah (φ : AttractorPt (vAction G) N T) {T' : Over S} (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) : G.E ⟶ pO T' := φ.app t a

lemma ah_nat (φ : AttractorPt (vAction G) N T) {T' T'' : Over S} (s : T'' ⟶ T') (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) :
    ah φ (s ≫ t) (APt.res s.op a) = ah φ t a ≫ resO s := φ.naturality s t a

/-- `E_N`-component of a point of `V(E)^N`. -/
def ptTo (φ : AttractorPt (vAction G) N T) : G.EN N ⟶ pO T :=
  Sigma.desc fun n : N => G.ι n ≫ ah φ (𝟙 T) 1

lemma ιN_ptTo (φ : AttractorPt (vAction G) N T) (n : N) :
    G.ιN N n ≫ ptTo φ = G.ι n ≫ ah φ (𝟙 T) 1 := Sigma.ι_desc _ _

lemma res_one {T T' : Over S} (τ : T' ⟶ T) :
    APt.res τ.op (1 : APt (overO S) N (op T)) = 1 := by
  refine MonoidHom.ext fun n => ?_
  exact map_one ((overO S).map τ.op).hom

/-- The computation on `Spec D`. -/
lemma app_eq_on_Phi {V : S.Opens} (hV : IsAffineOpen V) (D : CommAlgCat.{u} Γ(S, V))
    (φ : AttractorPt (vAction G) N T) (τ : Phi hV D ⟶ T) (a : APt (overO S) N (op (Phi hV D)))
    (m : M) (x : Γ(G.P m, V)) :
    val hV (liesOver_Phi hV D) (G.ι m ≫ ah φ τ a) x =
      val hV (liesOver_Phi hV D) (ptComp G N (ptTo φ) τ a m) x := by
  let β := φ.baseChange τ
  let a' : Multiplicative N →* D :=
    (((etaEquiv hV D).symm : _ ≃* _).toMonoidHom).comp (toGa hV (liesOver_Phi hV D) a)
  have ha' : etaPt hV D a' = a := by
    refine MonoidHom.ext fun n => ?_
    exact (etaEquiv hV D).apply_symm_apply _
  have e1 : PhiMap hV (AlgHom.id _ D) = 𝟙 _ := PhiMap_id hV D
  have hval : ∀ (b : Multiplicative N →* D), eta hV D (cv hV G N m x β (AlgHom.id _ D) b) =
      val hV (liesOver_Phi hV D) (G.ι m ≫ ah φ τ (etaPt hV D b)) x := by
    intro b
    refine (eta_cv hV G N m x β (AlgHom.id _ D) b).trans ?_
    have h : ah β (PhiMap hV (AlgHom.id _ D)) (etaPt hV D b) = ah φ τ (etaPt hV D b) := by
      change ah φ (PhiMap hV (AlgHom.id _ D) ≫ τ) _ = _
      rw [e1, Category.id_comp]
    exact congrArg (fun z => val hV (liesOver_Phi hV D) (G.ι m ≫ z) x) h
  have hA : val hV (liesOver_Phi hV D) (G.ι m ≫ ah φ τ a) x =
      eta hV D (cv hV G N m x β (AlgHom.id _ D) a') := by
    rw [hval, ha']
  rw [hA]
  unfold ptComp
  by_cases hm : m ∈ N
  · rw [dif_pos hm, cv_eq_mul hV G N m x β _ _ hm, map_mul]
    have e2 : etaPt hV D (1 : Multiplicative N →* D) = 1 := by
      refine MonoidHom.ext fun n => ?_
      exact map_one (eta hV D)
    have e3 : ah φ τ 1 = ah φ (𝟙 T) 1 ≫ resO τ := by
      have := ah_nat φ τ (𝟙 T) 1
      rwa [Category.comp_id, res_one] at this
    have e4 : eta hV D (cv hV G N m x β (AlgHom.id _ D) 1) =
        val hV (liesOver_Phi hV D) (G.ιN N ⟨m, hm⟩ ≫ ptTo φ ≫ resO τ) x := by
      rw [hval, e2, e3, ← Category.assoc (G.ιN N ⟨m, hm⟩), ιN_ptTo, Category.assoc]
    have e6 : eta hV D (a' (Multiplicative.ofAdd ⟨m, hm⟩)) = a (Multiplicative.ofAdd ⟨m, hm⟩) :=
      (etaEquiv hV D).apply_symm_apply _
    have h7 := val_mul hV (liesOver_Phi hV D)
      (G.ιN N ⟨m, hm⟩ ≫ ptTo φ ≫ resO τ) (a (Multiplicative.ofAdd ⟨m, hm⟩)) x
    simp only [Category.assoc] at h7
    refine Eq.trans ?_ h7.symm
    exact congrArg₂ (· * ·) e6 e4
  · rw [dif_neg hm, cv_eq_zero hV G N m x β _ _ hm, map_zero]
    exact (val_zero hV _ x).symm

lemma app_eq (φ : AttractorPt (vAction G) N T) {T' : Over S} (t : T' ⟶ T)
    (a : APt (overO S) N (op T')) (m : M) :
    G.ι m ≫ ah φ t a = ptComp G N (ptTo φ) t a m := by
  refine local_ext fun V hV D s x => ?_
  have h1 := app_eq_on_Phi hV D φ (s ≫ t) (APt.res s.op a) m x
  rw [ah_nat, ptComp_res, ← Category.assoc] at h1
  exact h1

variable (G N)

/-- **Proposition 3.28.** `V(E)^N(T) = V(E_N)(T)`, by `φ ↦ φ.toPoint|_{E_N}`, for `S` any scheme,
`E` any `M`-graded `𝒪_S`-module, `T` any `S`-scheme. -/
def vAttractorEquiv (T : Over S) : AttractorPt (vAction G) N T ≃ (G.EN N ⟶ pO T) where
  toFun := ptTo
  invFun := ptOf G N
  left_inv φ := by
    refine AttractorPt.ext ?_
    funext T' t a
    refine G.hom_ext fun m => ?_
    refine (G.ι_desc _ m).trans ?_
    exact (app_eq φ t a m).symm
  right_inv l := by
    refine G.EN_ext N fun n => ?_
    rw [ιN_ptTo]
    change G.ι n ≫ G.desc (ptComp G N l (𝟙 T) 1) = _
    rw [G.ι_desc]
    unfold ptComp
    rw [dif_pos n.2]
    have : (1 : APt (overO S) N (op T)) (Multiplicative.ofAdd ⟨(n : M), n.2⟩) = 1 := rfl
    rw [resO_id, Category.id_comp]
    exact (congrArg (fun k => G.ιN N n ≫ l ≫ k) (mulO_one T)).trans
      (by rw [Category.comp_id])

lemma ptTo_baseChange {T T' : Over S} (s : T' ⟶ T) (φ : AttractorPt (vAction G) N T) :
    ptTo (φ.baseChange s) = ptTo φ ≫ resO s := by
  refine G.EN_ext N fun n => ?_
  rw [ιN_ptTo, ← Category.assoc, ιN_ptTo, Category.assoc, ← ah_nat, Category.comp_id, res_one]
  rfl

/-- **Proposition 3.28**, naturality in `T`. -/
lemma vAttractorEquiv_baseChange {T T' : Over S} (s : T' ⟶ T) (φ : AttractorPt (vAction G) N T) :
    vAttractorEquiv G N T' (φ.baseChange s) = vAttractorEquiv G N T φ ≫ resO s :=
  ptTo_baseChange G N s φ

end AlgMag.VB
