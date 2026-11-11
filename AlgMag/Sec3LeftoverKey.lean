/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec3LeftoverAct

/-!
# Algebraic Magnetism, Proposition 3.28: the attractor of `V(E)`, over `Spec D`

The identifications of the printed proof, on affine `T = Spec D`:
`Hom^{𝔸(M)}_T(𝔸(N)_T, V(p^*E)) = Hom^{M-gr}(p^*E, 𝒪_T[N])`: a graded map sends `E_m` into `𝒪_T X^m`,
and to `0` for `m ∉ N`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Magnetism

noncomputable section

namespace AlgMag.VB

open AlgMag.GB

/-! ### Algebra -/

section Algebra

open AddMonoidAlgebra

variable {C : Type u} [CommRing C] {M : Type u} [AddCommMonoid M] {N : AddSubmonoid M}

/-- The coefficient comparison: if `Σ c_n X^(n,n) = X^(m,0) Σ c_n X^(0,n)` in `C[M × N]`,
then `c_k = 0` for `k ≠ m`. -/
lemma coeff_eq_zero_of_coact (m : M) (J₁ J₂ : AddMonoidAlgebra C N →+ AddMonoidAlgebra C (M × N))
    (h₁ : ∀ n a, J₁ (single n a) = single ((n : M), n) a)
    (h₂ : ∀ n a, J₂ (single n a) = single ((0 : M), n) a)
    (c : AddMonoidAlgebra C N) (h : J₁ c = single (m, 0) 1 * J₂ c)
    (k : N) (hk : (k : M) ≠ m) : c.coeff k = 0 := by
  classical
  have A : ∀ c : AddMonoidAlgebra C N, (J₁ c).coeff ((k : M), k) = c.coeff k := by
    intro c
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [map_add, hx, hy]
    | single n a =>
      rw [h₁, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases e : n = k
      · simp [e]
      · have : ¬ ((n : M), n) = ((k : M), k) := fun h' => e (Prod.ext_iff.mp h').2
        simp [e, this]
  have B : ∀ c : AddMonoidAlgebra C N,
      (single (m, 0) 1 * J₂ c : AddMonoidAlgebra C (M × N)).coeff ((k : M), k) = 0 := by
    intro c
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [map_add, mul_add, hx, hy]
    | single n a =>
      rw [h₂, single_mul_single, coeff_single, Finsupp.single_apply]
      have : ¬ ((m, 0) + ((0 : M), n) = ((k : M), k)) := fun h' => hk (by
        have := (Prod.ext_iff.mp h').1
        simpa using this.symm)
      rw [if_neg this]
  rw [← A c, h, B c]

end Algebra

/-! ### Values of sections on schemes over an affine open -/

section Val

variable {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V)

/-- The value in `Γ(T, ⊤)` of a morphism to `p_* 𝒪_T` on a section over `V`, when `T` lies over `V`. -/
def val {P : S.Modules} {T : Over S} (hT : LiesOver T V) (ξ : P ⟶ pO T) (x : Γ(P, V)) :
    Ga hV T hT :=
  (T.left.presheaf.map (homOfLE (le_of_eq hT.symm)).op).hom (sec ξ V x)

lemma val_res {P : S.Modules} {T T' : Over S} (hT : LiesOver T V) (hT' : LiesOver T' V)
    (ξ : P ⟶ pO T) (s : T' ⟶ T) (x : Γ(P, V)) :
    val hV hT' (ξ ≫ resO s) x = gpull hV hT hT' s (val hV hT ξ x) := by
  have h1 : s.left.appLE (T.hom ⁻¹ᵁ V) (T'.hom ⁻¹ᵁ V) (preimage_le s V) ≫
      T'.left.presheaf.map (homOfLE (le_of_eq hT'.symm)).op =
      T.left.presheaf.map (homOfLE (le_of_eq hT.symm)).op ≫ s.left.appTop := by
    rw [Scheme.Hom.appLE_map]
    exact (Scheme.Hom.naturality s.left (homOfLE (le_of_eq hT.symm)).op).symm
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) (sec ξ V x)

lemma val_mul {P : S.Modules} {T : Over S} (hT : LiesOver T V) (ξ : P ⟶ pO T) (r : Γ(T.left, ⊤))
    (x : Γ(P, V)) :
    val hV hT (ξ ≫ mulO T r) x = (show Ga hV T hT from r) * val hV hT ξ x := by
  change (T.left.presheaf.map (homOfLE (le_of_eq hT.symm)).op).hom
    ((T.left.presheaf.map (homOfLE le_top).op).hom r * sec ξ V x) = _
  rw [map_mul]
  refine congrArg (· * _) ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (T.left.presheaf.map_id _)) r

end Val

/-! ### The computation over `Spec D` -/

section Compute

open scoped Classical

variable {S : Scheme.{u}} {V : S.Opens} (hV : IsAffineOpen V) {M : Type u} [AddCommMonoid M]
  (G : GrMod S M) (N : AddSubmonoid M) (m : M) (x : Γ(G.P m, V))

/-- The value on `x ∈ E_m(V)` of a point of the attractor, at a point `a` of `𝔸(N)` over `τ : C → D`. -/
def cv {C : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    {D : CommAlgCat.{u} Γ(S, V)} (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) : D :=
  (etaEquiv hV D).symm (val hV (liesOver_Phi hV D)
    (G.ι m ≫ (show G.E ⟶ pO (Phi hV D) from β.app (PhiMap hV τ) (etaPt hV D a))) x)

lemma eta_cv {C : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    {D : CommAlgCat.{u} Γ(S, V)} (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) :
    eta hV D (cv hV G N m x β τ a) = val hV (liesOver_Phi hV D)
      (G.ι m ≫ (show G.E ⟶ pO (Phi hV D) from β.app (PhiMap hV τ) (etaPt hV D a))) x :=
  (etaEquiv hV D).apply_symm_apply _

lemma cv_nat {C D D' : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (σ : D →ₐ[Γ(S, V)] D') (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) :
    cv hV G N m x β (σ.comp τ) ((σ : D →* D').comp a) = σ (cv hV G N m x β τ a) := by
  refine (eta_bijective hV D').1 ?_
  rw [eta_cv]
  have a1 := β.naturality (PhiMap hV σ) (PhiMap hV τ) (etaPt hV D a)
  have a2 := PhiMap_comp hV τ σ
  have a3 := etaPt_res hV σ a
  have e : (show G.E ⟶ pO (Phi hV D') from
      β.app (PhiMap hV (σ.comp τ)) (etaPt hV D' ((σ : D →* D').comp a))) =
      (show G.E ⟶ pO (Phi hV D) from β.app (PhiMap hV τ) (etaPt hV D a)) ≫ resO (PhiMap hV σ) :=
    (congrArg₂ (fun (f : Phi hV D' ⟶ Phi hV C) b => β.app f b) a2 a3).trans a1
  rw [e, ← Category.assoc, val_res hV (liesOver_Phi hV D) (liesOver_Phi hV D') _ _ x, ← eta_cv]
  exact DFunLike.congr_fun (gpull_PhiMap_eta hV σ) _

lemma cv_eqv {C D : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (τ : C →ₐ[Γ(S, V)] D) (h : Multiplicative M →* D) (a : Multiplicative N →* D) :
    cv hV G N m x β τ ((h.comp (AddMonoidHom.toMultiplicative N.subtype)) * a) =
      h (Multiplicative.ofAdd m) * cv hV G N m x β τ a := by
  refine (eta_bijective hV D).1 ?_
  rw [eta_cv, map_mul, eta_cv]
  have he := β.equivariant (PhiMap hV τ) (etaPt hV D h) (etaPt hV D a)
  have h3 : APt.toMagnet N (etaPt hV D h) * etaPt hV D a =
      etaPt hV D ((h.comp (AddMonoidHom.toMultiplicative N.subtype)) * a) := by
    refine MonoidHom.ext fun n => ?_
    exact (map_mul (eta hV D) _ _).symm
  rw [h3] at he
  have key : ∀ ξ₀ : G.E ⟶ pO (Phi hV D), val hV (liesOver_Phi hV D)
      (G.ι m ≫ vSmul G (etaPt hV D h) ξ₀) x =
      eta hV D (h (Multiplicative.ofAdd m)) * val hV (liesOver_Phi hV D) (G.ι m ≫ ξ₀) x := by
    intro ξ₀
    rw [ι_vSmul, ← Category.assoc]
    exact val_mul hV _ (G.ι m ≫ ξ₀) _ x
  exact (congrArg (fun z => val hV (liesOver_Phi hV D) (G.ι m ≫ z) x) he).trans (key _)

/-- The value at the universal point of `𝔸(N)`, in `C[N]`. -/
def c0 {C : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C)) :
    AddMonoidAlgebra C N :=
  cv hV G N m x β (D := CommAlgCat.of Γ(S, V) (AddMonoidAlgebra C N)) (constAlg (R := Γ(S, V)) N C)
    (AddMonoidAlgebra.of C N)

lemma cv_eq_eval {C D : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) :
    cv hV G N m x β τ a = evalAlg τ a (c0 hV G N m x β) := by
  have e1 : (evalAlg τ a).comp (constAlg (R := Γ(S, V)) N C) = τ := by
    refine AlgHom.ext fun c => ?_
    change evalAlg τ a (constAlg (R := Γ(S, V)) N C c) = τ c
    rw [constAlg_apply (R := Γ(S, V)), evalAlg_single]
    change _ * a 1 = _
    rw [map_one, mul_one]
  have e2 : ((evalAlg τ a : _ →ₐ[Γ(S, V)] D) : AddMonoidAlgebra C N →* D).comp
      (AddMonoidAlgebra.of C N) = a := by
    refine MonoidHom.ext fun n => ?_
    change evalAlg τ a (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1) = a n
    rw [evalAlg_single, map_one, one_mul]
    rfl
  have := cv_nat hV G N m x (D := CommAlgCat.of Γ(S, V) (AddMonoidAlgebra C N)) β (evalAlg τ a)
    (constAlg (R := Γ(S, V)) N C) (AddMonoidAlgebra.of C N)
  rw [e1, e2] at this
  exact this

lemma c0_coeff {C : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (k : N) (hk : (k : M) ≠ m) : (c0 hV G N m x β).coeff k = 0 := by
  let C2 : CommAlgCat.{u} Γ(S, V) := CommAlgCat.of Γ(S, V) (AddMonoidAlgebra C (M × N))
  let τ2 : C →ₐ[Γ(S, V)] C2 := constAlg (R := Γ(S, V)) (M × N) C
  let u : Multiplicative (M × N) →* C2 := AddMonoidAlgebra.of C (M × N)
  let a1 : Multiplicative N →* C2 :=
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.prod N.subtype (AddMonoidHom.id N)))
  let a2 : Multiplicative N →* C2 :=
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inr M N))
  let h : Multiplicative M →* C2 :=
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.inl M N))
  have e : (h.comp (AddMonoidHom.toMultiplicative N.subtype)) * a2 = a1 := by
    refine MonoidHom.ext fun n => ?_
    change (AddMonoidAlgebra.single (((Multiplicative.toAdd n : N) : M), (0 : N)) 1 *
      AddMonoidAlgebra.single ((0 : M), (Multiplicative.toAdd n : N)) 1 :
        AddMonoidAlgebra C (M × N)) =
      AddMonoidAlgebra.single (((Multiplicative.toAdd n : N) : M), (Multiplicative.toAdd n : N)) 1
    rw [AddMonoidAlgebra.single_mul_single]
    simp
  have q := cv_eqv hV G N m x β τ2 h a2
  rw [e, cv_eq_eval hV G N m x β τ2 a1, cv_eq_eval hV G N m x β τ2 a2] at q
  refine coeff_eq_zero_of_coact m (evalAlg τ2 a1 : _ →ₐ[Γ(S, V)] C2).toRingHom.toAddMonoidHom
    (evalAlg τ2 a2 : _ →ₐ[Γ(S, V)] C2).toRingHom.toAddMonoidHom ?_ ?_ _ q k hk
  · intro n c
    refine (evalAlg_single (D := C2) N C τ2 a1 n c).trans ?_
    change (AddMonoidAlgebra.single 0 c * AddMonoidAlgebra.single ((n : M), n) 1 :
      AddMonoidAlgebra C (M × N)) = _
    rw [AddMonoidAlgebra.single_mul_single]
    simp
  · intro n c
    refine (evalAlg_single (D := C2) N C τ2 a2 n c).trans ?_
    change (AddMonoidAlgebra.single 0 c * AddMonoidAlgebra.single ((0 : M), n) 1 :
      AddMonoidAlgebra C (M × N)) = _
    rw [AddMonoidAlgebra.single_mul_single]
    simp

/-- A graded map sends `E_m` to `0` for `m ∉ N`. -/
lemma cv_eq_zero {C D : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) (hm : m ∉ N) :
    cv hV G N m x β τ a = 0 := by
  have : c0 hV G N m x β = 0 := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun k => ?_)
    exact c0_coeff hV G N m x β k fun e => hm (e ▸ k.2)
  rw [cv_eq_eval, this, map_zero]

/-- A graded map sends `E_m` into `𝒪_T X^m`, for `m ∈ N`. -/
lemma cv_eq_mul {C D : CommAlgCat.{u} Γ(S, V)} (β : AttractorPt (vAction G) N (Phi hV C))
    (τ : C →ₐ[Γ(S, V)] D) (a : Multiplicative N →* D) (hm : m ∈ N) :
    cv hV G N m x β τ a = a (Multiplicative.ofAdd ⟨m, hm⟩) *
      τ (cv hV G N m x β (AlgHom.id _ C) 1) := by
  classical
  set c := (c0 hV G N m x β).coeff ⟨m, hm⟩ with hc
  have : c0 hV G N m x β = AddMonoidAlgebra.single ⟨m, hm⟩ c := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun k => ?_)
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases e : (⟨m, hm⟩ : N) = k
    · rw [if_pos e, ← e]
    · rw [if_neg e]
      exact c0_coeff hV G N m x β k fun e' => e (Subtype.ext e'.symm)
  rw [cv_eq_eval, cv_eq_eval, this, evalAlg_single, evalAlg_single]
  change _ = _ * τ (c * (1 : C))
  rw [mul_one, mul_comm]

end Compute

end AlgMag.VB
