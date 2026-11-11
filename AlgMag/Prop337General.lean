/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec8Limits

/-!
# Proposition 3.37, corrected statement

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026), Proposition 3.37. `M` is an arbitrary
commutative monoid, `X` a separated algebraic space locally of finite presentation over `S`,
`N = colim N_i` a directed union of submonoids, and `T → S` a quasi-compact scheme (the correction:
the printed statement for all `T` is false). Then `X^N(T) = colim X^{N_i}(T)`.

The printed proof is followed: `Γ(T)[N] = colim Γ(T)[N_i]`, Tag 049J, equivariance by density of
`A(M)_T × A(N)_T → A(M)_T × A(N_i)_T`. The passage from affine to quasi-compact `T` is the correction.
`hM : #M < B.cutoff` is the site cutoff: it puts `A(N)_T` and `A(M)_T × A(N)_T` in the site.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal

namespace AlgMag

namespace P337

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

attribute [local irreducible] spObj

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

/-! ### Size -/

lemma contains_iff {R : Type u} [CommRing R] : B.Contains (Spec (.of R)) ↔ #R < B.cutoff :=
  contains_iff_card

lemma contains_alg {R P : Type u} [CommRing R] [AddCommMonoid P] (hP : #P < B.cutoff)
    (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of (AddMonoidAlgebra R P))) :=
  contains_addMonoidAlgebra hP hR

/-! ### Rings, for a commutative monoid `M` -/

section Rings

variable (R' : Type u) [CommRing R'] (M : Type u) [AddCommMonoid M]

/-- The structure map `R → R[M]`. -/
noncomputable def jr : RH R' (AddMonoidAlgebra R' M) := AddMonoidAlgebra.singleZeroRingHom

/-- The universal point `M → R[M]`. -/
noncomputable def eM : Multiplicative M →* AddMonoidAlgebra R' M where
  toFun n := AddMonoidAlgebra.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' x y := by
    rw [AddMonoidAlgebra.single_mul_single, one_mul]; rfl

variable {R' M}

/-- `π[M]`. -/
noncomputable def mapR {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) (M : Type u)
    [AddCommMonoid M] : RH (AddMonoidAlgebra A M) (AddMonoidAlgebra C M) :=
  AddMonoidAlgebra.mapRingHom M π

lemma mapR_jr {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) :
    (mapR π M).comp (jr A M) = (jr C M).comp π := by
  refine RingHom.ext fun x => ?_
  change AddMonoidAlgebra.mapRingHom M π (AddMonoidAlgebra.single 0 x) = AddMonoidAlgebra.single 0 (π x)
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

lemma mapR_eM {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C) :
    (mapR π M).toMonoidHom.comp (eM A M) = eM C M := by
  refine MonoidHom.ext fun n => ?_
  refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
  rw [map_one]
  rfl

lemma mapR_injective {A C : Type u} [CommRing A] [CommRing C] (π : A →+* C)
    (h : Function.Injective π) : Function.Injective (mapR π M) := by
  intro x y e
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun m => h ?_)
  have := congrArg (fun z => z.coeff m) e
  simpa [mapR] using this

variable (N : AddSubmonoid M)

/-- The coaction `R[N] → R[N][M]`, `eₙ ↦ eₙ ⊗ eₙ`. -/
noncomputable def faceCoact (R : Type u) [CommRing R] :
    AddMonoidAlgebra R N →+* AddMonoidAlgebra (AddMonoidAlgebra R N) M :=
  AddMonoidAlgebra.liftNCRingHom
    ((AddMonoidAlgebra.singleZeroRingHom).comp (AddMonoidAlgebra.singleZeroRingHom))
    { toFun := fun n => AddMonoidAlgebra.single ((Multiplicative.toAdd n : N) : M)
        (AddMonoidAlgebra.single (Multiplicative.toAdd n) 1)
      map_one' := rfl
      map_mul' := fun x y => by
        rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl }
    (fun _ _ => Commute.all _ _)

lemma faceCoact_single {R : Type u} [CommRing R] (a : N) (r : R) :
    faceCoact N R (AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single (a : M) (AddMonoidAlgebra.single a r) := by
  have e : AddMonoidAlgebra.single a r =
      AddMonoidAlgebra.single (0 : N) r * AddMonoidAlgebra.single a (1 : R) := by
    rw [AddMonoidAlgebra.single_mul_single]; simp
  rw [e, map_mul]
  simp [faceCoact, AddMonoidAlgebra.single_mul_single]

end Rings

section Main

variable {M : Type u} [AddCommMonoid M]

/-- The coaction on `Γ(T)[N]`. -/
noncomputable def cN (T : BigFppfOver B S hS) (N : AddSubmonoid M) :
    RH (AddMonoidAlgebra (RT T) N) (AddMonoidAlgebra (AddMonoidAlgebra (RT T) N) M) :=
  faceCoact N _

/-- `R[L] → R[N]` for `L ≤ N`. -/
noncomputable def inclR (T : BigFppfOver B S hS) {L N : AddSubmonoid M} (h : L ≤ N) :
    RH (AddMonoidAlgebra (RT T) L) (AddMonoidAlgebra (RT T) N) :=
  AddMonoidAlgebra.mapDomainRingHom _ (AddSubmonoid.inclusion h)

lemma incl_injective (T : BigFppfOver B S hS) {L N : AddSubmonoid M} (h : L ≤ N) :
    Function.Injective (inclR T h) :=
  AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h)

lemma incl_ρN {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N) :
    (inclR T h).comp (ρN T L) = ρN T N := by
  refine RingHom.ext fun r => ?_
  simp [inclR, ρN]

lemma incl_mon {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N) :
    (inclR T h).toMonoidHom.comp (monN _ L) =
      (monN _ N).comp (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) := by
  refine MonoidHom.ext fun p => ?_
  simp [inclR, monN]

lemma mapR_incl_cN {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N) :
    (mapR (inclR T h) M).comp (cN T L) = (cN T N).comp (inclR T h) := by
  refine RingHom.ext fun x => ?_
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n r =>
    change mapR (inclR T h) M (faceCoact L _ (AddMonoidAlgebra.single n r)) =
      faceCoact N _ (inclR T h (AddMonoidAlgebra.single n r))
    have e : inclR T h (AddMonoidAlgebra.single n r) =
        AddMonoidAlgebra.single (AddSubmonoid.inclusion h n) r := by simp [inclR]
    rw [e, faceCoact_single, faceCoact_single]
    refine (AddMonoidAlgebra.mapRingHom_single _ _ _).trans ?_
    rw [e]
    rfl

lemma cN_ρN {T : BigFppfOver B S hS} {N : AddSubmonoid M} :
    (cN T N).comp (ρN T N) = (jr _ M).comp (ρN T N) := by
  refine RingHom.ext fun r => ?_
  refine (faceCoact_single N (0 : N) r).trans ?_
  rfl

/-- The ring map `R[N][M] → Γ(T')` of a pair of points of `𝔸(N)` and of `𝔸(M)`. -/
noncomputable def pairRing {T T' : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] {N : AddSubmonoid M}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) :
    RH (AddMonoidAlgebra (AddMonoidAlgebra (RT T) N) M) Γ((Sch).obj T', ⊤) :=
  AddMonoidAlgebra.liftNCRingHom (pointRing t a)
    (show Multiplicative M →* Γ((Sch).obj T', ⊤) from h) (fun _ _ => Commute.all _ _)

lemma pairRing_single {T T' : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] {N : AddSubmonoid M}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) (r) (m : M) :
    pairRing t h a (AddMonoidAlgebra.single m r) = pointRing t a r *
      (show Multiplicative M →* Γ((Sch).obj T', ⊤) from h) (Multiplicative.ofAdd m) :=
  lift_single' _ _ _ _ _

lemma pairRing_comp {T T' : BigFppfOver B S hS} [IsAffine ((Sch).obj T)] {N : AddSubmonoid M}
    (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T')) (a : APt (fppfO B S hS) N (op T')) :
    (pairRing t h a).comp ((jr _ M).comp (ρN T N)) = ((Sch).map t).appTop.hom := by
  refine RingHom.ext fun x => ?_
  have e : pairRing t h a (AddMonoidAlgebra.single 0 (AddMonoidAlgebra.single 0 x)) =
      ((Sch).map t).appTop.hom x := by
    rw [pairRing_single, ofAdd_zero, map_one, mul_one]
    exact congrArg (fun k : _ →+* _ => k x) (pointRing_comp t a)
  exact e

variable [hM : Fact (#M < B.cutoff)]

lemma contains_any (T : BigFppfOver B S hS) [IsAffine ((Sch).obj T)] (N : AddSubmonoid M) :
    B.Contains (Spec (.of (AddMonoidAlgebra (RT T) N))) :=
  contains_alg ((mk_subtype_le _).trans_lt hM.out) (contains_RT T)

lemma contains_M {R' : Type u} [CommRing R'] (h : B.Contains (Spec (.of R'))) :
    B.Contains (Spec (.of (AddMonoidAlgebra R' M))) :=
  contains_alg hM.out h

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {act : AAction (fppfO B S hS) M F}
variable {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

lemma ofLE_universal {L N : AddSubmonoid M} (h : L ≤ N) (φ : AttractorPt act L T) :
    (AttractorPt.ofLE h φ).app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N)) =
      F.map (spMap T (hC := contains_any T L) (hC' := contains_any T N) (inclR T h) (incl_ρN h)).op
        (φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L))) := by
  rw [app_sp φ (inclR T h) (incl_ρN h) (monN _ L), incl_mon]
  rfl

/-- The equivariance of a point on `𝔸(L)_T`, on the universal points of `𝔸(L)` and of `𝔸(M)`. -/
def IsKey (L : AddSubmonoid M) (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L)))) : Prop :=
  F.map (spMap T (hC := contains_any T L) (hC' := contains_M (contains_any T L))
    (cN T L) cN_ρN).op x₀ =
  act.smul (spPt (eM _ M)) (F.map (spMap T (hC := contains_any T L)
    (hC' := contains_M (contains_any T L)) (jr _ M) rfl).op x₀)

/-- A point of `F` on `𝔸(L)_T` which is equivariant for the universal point is a point of `F^L`. -/
theorem exists_attractorPt_of_key (L : AddSubmonoid M)
    (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L)))) (hk : IsKey (act := act) L x₀) :
    ∃ φ : AttractorPt act L T,
      φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L)) = x₀ := by
  have hCN := contains_any (hM := hM) T L
  have hCNM := contains_M (M := M) hCN
  let Uni := spUniversal T L hCN
  have hequiv : ∀ {T' : BigFppfOver B S hS} (t : T' ⟶ T) (h : APt (fppfO B S hS) M (op T'))
      (a : APt (fppfO B S hS) L (op T')),
      F.map (Uni.lift t (APt.toMagnet L h * a)).op x₀ = act.smul h (F.map (Uni.lift t a).op x₀) := by
    intro T' t h a
    let r : T' ⟶ spObj T ((jr _ M).comp (ρN T L)) hCNM :=
      spLift T _ hCNM t (pairRing t h a) (pairRing_comp t h a)
    have hrπ : r ≫ spToT T _ hCNM = t := spLift_toT T _ hCNM t _ _
    have hra : ∀ x', ((Sch).map r).appTop.hom (spSec T _ hCNM x') = pairRing t h a x' :=
      fun x' => spLift_appTop T _ hCNM t _ _ x'
    have l₁ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl = spUniLift T L hCN t a := by
      refine Uni.uniq t a _ ?_ ?_
      · change (r ≫ spMap T _ rfl) ≫ spToT T (ρN T L) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ rfl).op (spPt (monN _ L)) = a
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        change pairRing t h a (AddMonoidAlgebra.single 0 (monN _ L n)) = _
        rw [pairRing_single, ofAdd_zero, map_one, mul_one]
        change pointRing t a (AddMonoidAlgebra.single _ 1) = _
        rw [pointRing_single, map_one, one_mul]
        rfl
    have l₂ : r ≫ spMap T (hC := hCN) (hC' := hCNM) (cN T L) cN_ρN =
        spUniLift T L hCN t (APt.toMagnet L h * a) := by
      refine Uni.uniq t _ _ ?_ ?_
      · change (r ≫ spMap T _ _) ≫ spToT T (ρN T L) hCN = t
        rw [Category.assoc, spMap_toT, hrπ]
      · change APt.res (r ≫ spMap T _ _).op (spPt (monN _ L)) = _
        rw [op_comp, APt.res_comp, spPt_res]
        refine MonoidHom.ext fun n => ?_
        rw [res_spPt_apply, hra]
        have : (cN T L).toMonoidHom.comp (monN _ L) n = AddMonoidAlgebra.single
            ((Multiplicative.toAdd n : L) : M) (monN _ L n) := faceCoact_single L _ _
        rw [this, pairRing_single]
        change pointRing t a (AddMonoidAlgebra.single _ 1) * _ = _
        rw [pointRing_single, map_one, one_mul, mul_comm]
        rfl
    have hres : APt.res r.op (spPt (T := T) (ρ := (jr _ M).comp (ρN T L)) (hC := hCNM) (eM _ M)) = h := by
      refine MonoidHom.ext fun m => ?_
      rw [res_spPt_apply, hra]
      change pairRing t h a (AddMonoidAlgebra.single _ 1) = _
      rw [pairRing_single, map_one, one_mul]
      rfl
    have hsm := act.map_smul r.op (spPt (eM _ M))
      (F.map (spMap T (hC := hCN) (hC' := hCNM) (jr _ M) rfl).op x₀)
    rw [hres] at hsm
    change F.map (spUniLift T L hCN t (APt.toMagnet L h * a)).op x₀ =
      act.smul h (F.map (spUniLift T L hCN t a).op x₀)
    rw [← l₁, ← l₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    have hkk : F.map (spMap T (hC := hCN) (hC' := hCNM) (cN T L) cN_ρN).op x₀ = _ := hk
    rw [hkk]
    exact hsm
  refine ⟨(attractorPtEquivOfUniversal Uni).symm ⟨x₀, hequiv⟩, ?_⟩
  change F.map (Uni.lift Uni.π Uni.u).op x₀ = x₀
  rw [Uni.lift_self]
  simp
  rfl

/-- Equivariance of the value of a point of `X^P` on `Spec R'`, for a coaction `c` on `R'`. -/
lemma app_coact {R' : Type u} [CommRing R']
    {P : AddSubmonoid M} (φ : AttractorPt act P T) {ρ : RT T →+* R'}
    (hC : B.Contains (Spec (.of R'))) (ν : Multiplicative P →* R')
    (c : R' →+* AddMonoidAlgebra R' M) (hν : ∀ p : Multiplicative P, c (ν p) =
      AddMonoidAlgebra.single ((Multiplicative.toAdd p : P) : M) (ν p)) :
    φ.app (spToT T ((jr R' M).comp ρ) (contains_M hC)) (spPt (c.toMonoidHom.comp ν)) =
      act.smul (spPt (eM R' M)) (φ.app (spToT T ((jr R' M).comp ρ) (contains_M hC))
        (spPt ((jr R' M).toMonoidHom.comp ν))) := by
  rw [← φ.equivariant]
  congr 1
  refine MonoidHom.ext fun p => ?_
  have key : c (ν p) = eM R' M (Multiplicative.ofAdd ((Multiplicative.toAdd p : P) : M)) *
      jr R' M (ν p) := by
    rw [hν]
    change _ = AddMonoidAlgebra.single _ 1 * AddMonoidAlgebra.single 0 (ν p)
    rw [AddMonoidAlgebra.single_mul_single, one_mul, add_zero]
    rfl
  exact (congrArg (spSec T ((jr R' M).comp ρ) (contains_M hC)) key).trans (map_mul _ _ _)

/-- Conversely, the value of a point of `F^L` at the universal point is equivariant. -/
theorem isKey_app (L : AddSubmonoid M) (φ : AttractorPt act L T) :
    IsKey (act := act) L (φ.app (spToT T (ρN T L) (contains_any T L)) (spPt (monN _ L))) := by
  unfold IsKey
  rw [app_sp φ (cN T L) cN_ρN (monN _ L), app_sp φ (jr _ M) rfl (monN _ L)]
  exact app_coact (ρ := ρN T L) φ (contains_any T L) (monN _ L) (cN T L)
    (fun p => faceCoact_single L _ _)

/-- If the image of a point of `𝔸(L)` in `𝔸(N)` is equivariant, so is the point: the density step of
the printed proof. -/
theorem isKey_descend (hd : HasDensePullback F) {L N : AddSubmonoid M} (h : L ≤ N)
    (x₀ : F.obj (op (spObj T (ρN T L) (contains_any T L))))
    (hk : IsKey (act := act) N (F.map (spMap T (hC := contains_any T L) (hC' := contains_any T N)
      (inclR T h) (incl_ρN h)).op x₀)) :
    IsKey (act := act) L x₀ := by
  have hCL := contains_any (hM := hM) T L
  have hCN := contains_any (hM := hM) T N
  have hCLM := contains_M (M := M) hCL
  have hCNM := contains_M (M := M) hCN
  have hM' : (mapR (inclR T h) M).comp ((jr _ M).comp (ρN T L)) = (jr _ M).comp (ρN T N) := by
    rw [← RingHom.comp_assoc, mapR_jr, RingHom.comp_assoc, incl_ρN]
  let S₀ := spMap T (hC := hCLM) (hC' := hCNM) (mapR (inclR T h) M) hM'
  refine hd T (hC := hCLM) (hC' := hCNM) (mapR (inclR T h) M) hM' (mapR_injective _ (incl_injective _ h)) ?_
  have hsm := act.map_smul S₀.op (spPt (eM _ M))
    (F.map (spMap T (hC := hCL) (hC' := hCLM) (jr _ M) rfl).op x₀)
  refine Eq.trans ?_ hsm.symm
  rw [spPt_res, mapR_eM]
  have hk' := hk
  unfold IsKey at hk'
  have comm : ∀ (π₁ : _ →+* _) (h₁) (π₂ : _ →+* _) (h₂) (e : (mapR (inclR T h) M).comp π₁ = π₂.comp (inclR T h)),
      F.map S₀.op (F.map (spMap T (hC := hCL) (hC' := hCLM) π₁ h₁).op x₀) =
        F.map (spMap T (hC := hCN) (hC' := hCNM) π₂ h₂).op
          (F.map (spMap T (hC := hCL) (hC' := hCN) (inclR T h) (incl_ρN h)).op x₀) := by
    intro π₁ h₁ π₂ h₂ e
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, spMap_comp T, spMap_comp T]
    congr 3
    exact congrArg Quiver.Hom.op (spMap_congr (T := T) _ _ e)
  rw [comm (cN T L) cN_ρN (cN T N) cN_ρN (mapR_incl_cN h),
    comm (jr _ M) rfl (jr _ M) rfl (mapR_jr _)]
  exact hk'

omit hM [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
lemma mem_range_incl {T : BigFppfOver B S hS} {L N : AddSubmonoid M} (h : L ≤ N)
    (x : AddMonoidAlgebra (RT T) N) (hx : ∀ n : N, x.coeff n ≠ 0 → (n : M) ∈ L) :
    x ∈ (inclR T h).range := by
  rw [eq_sum_single x]
  refine Subring.sum_mem _ fun n hn => ?_
  refine ⟨AddMonoidAlgebra.single ⟨n, hx n (Finsupp.mem_support_iff.1 hn)⟩ (x.coeff n), ?_⟩
  simp [inclR]
  rfl

/-- **Proposition 3.37**, `T` affine: the surjectivity, by the printed proof. -/
theorem exists_ofLE_affine {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {aX : AAction (fppfO B S hS) M X}
    (hsep : IsSeparatedOver X) (hlim : IsLimitPreserving X)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Ni : ι →o AddSubmonoid M)
    {N : AddSubmonoid M} (hle : ∀ i, Ni i ≤ N) (hcov : ∀ x ∈ N, ∃ i, x ∈ Ni i)
    (φ : AttractorPt aX N T) :
    ∃ (i : ι) (φ' : AttractorPt aX (Ni i) T), AttractorPt.ofLE (hle i) φ' = φ := by
  classical
  obtain ⟨i, x', hx'⟩ := hlim T (ρ := ρN T N) (hC := contains_any T N) (ι := ι)
    (fun i => AddMonoidAlgebra (RT T) (Ni i)) (fun i => ρN T (Ni i)) (fun i => contains_any T (Ni i))
    (fun i => inclR T (hle i)) (fun i => incl_ρN (hle i)) (fun i => incl_injective T (hle i))
    (fun s => by
      let G : Finset N := s.biUnion fun x => x.coeff.support
      choose f hf using fun n : N => hcov n n.2
      obtain ⟨k, hk⟩ := (G.image f).exists_le
      refine ⟨k, fun x hx => mem_range_incl (hle k) x fun n hn => ?_⟩
      have hnG : n ∈ G := Finset.mem_biUnion.2 ⟨x, hx, Finsupp.mem_support_iff.2 hn⟩
      exact Ni.monotone (hk _ (Finset.mem_image_of_mem f hnG)) (hf n))
    (φ.app (spToT T (ρN T N) (contains_any T N)) (spPt (monN _ N)))
  have hP := hle i
  have hk : IsKey (act := aX) (Ni i) x' := isKey_descend (hasDensePullback_of_separated hsep) hP x' (by
    have e : X.map (spMap T (hC := contains_any T (Ni i)) (hC' := contains_any T N) (inclR T hP)
      (incl_ρN hP)).op x' = _ := hx'
    rw [e]
    exact isKey_app N φ)
  obtain ⟨φ', hφ'⟩ := exists_attractorPt_of_key (Ni i) x' hk
  refine ⟨i, φ', ?_⟩
  let Uni := spUniversal T N (contains_any T N)
  have key : (AttractorPt.ofLE hP φ').app Uni.π Uni.u = φ.app Uni.π Uni.u := by
    refine (ofLE_universal hP φ').trans ?_
    rw [hφ']
    exact hx'
  refine AttractorPt.ext ?_
  funext T' t a'
  rw [AttractorPt.app_eq_of_universal Uni, φ.app_eq_of_universal Uni, key]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- **Proposition 3.29** in the form needed: `X^L → X^N` is injective on points, for any `T`. -/
theorem ofLE_inj (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hd : HasDensePullback F) {L N : AddSubmonoid M} (h : L ≤ N) (T : BigFppfOver B S hS) :
    Function.Injective (AttractorPt.ofLE (act := act) (T := T) h) := by
  have shL := isSheaf_attractor act L _ hF
  intro φ ψ hφψ
  obtain ⟨I, V, π, hV, hS'⟩ := exists_affine_cover T
  refine (shL _ hS').isSeparatedFor.ext fun W g hg => ?_
  obtain ⟨_, a, b, ⟨i⟩, rfl⟩ := hg
  have main : AttractorPt.baseChange (π i) φ = AttractorPt.baseChange (π i) ψ := by
    have : IsAffine ((Sch).obj (V i)) := hV i
    set φ' := AttractorPt.baseChange (π i) φ with hφ'
    set ψ' := AttractorPt.baseChange (π i) ψ with hψ'
    have hφψ' : AttractorPt.ofLE h φ' = AttractorPt.ofLE h ψ' :=
      congrArg (AttractorPt.baseChange (π i)) hφψ
    let Uni := spUniversal (V i) L (contains_any (V i) L)
    suffices key : φ'.app Uni.π Uni.u = ψ'.app Uni.π Uni.u by
      refine AttractorPt.ext ?_
      funext T' t a'
      rw [φ'.app_eq_of_universal Uni, ψ'.app_eq_of_universal Uni, key]
    refine hd (V i) (hC := contains_any (V i) L) (hC' := contains_any (V i) N) (inclR (V i) h)
      (incl_ρN h) (incl_injective _ h) ?_
    refine (ofLE_universal h φ').symm.trans (Eq.trans ?_ (ofLE_universal h ψ'))
    rw [hφψ']
  exact congrArg (AttractorPt.baseChange a) main

end Main

end P337

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "Sch" => BigFppfOver.toScheme B S hS

variable {M : Type u} [AddCommMonoid M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {act : AAction (fppfO B S hS) M X}

/-- **Proposition 3.37**, surjectivity, for `T` quasi-compact: the correction of the printed statement.
Take a finite affine cover of `T`, a common index, and glue using the injectivity of `X^{N_i} → X^N`. -/
theorem prop337_exists (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) (hM : #M < B.cutoff)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Ni : ι →o AddSubmonoid M)
    {N : AddSubmonoid M} (hle : ∀ i, Ni i ≤ N) (hcov : ∀ x ∈ N, ∃ i, x ∈ Ni i)
    {T : BigFppfOver B S hS} [CompactSpace ((Sch).obj T)] (φ : AttractorPt act N T) :
    ∃ (i : ι) (φ' : AttractorPt act (Ni i) T), AttractorPt.ofLE (hle i) φ' = φ := by
  classical
  haveI : Fact (#M < B.cutoff) := ⟨hM⟩
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hd := hasDensePullback_of_separated hsep
  -- a finite affine cover
  have hcover : (Set.univ : Set ((Sch).obj T)) ⊆
      ⋃ U : ((Sch).obj T).affineOpens, ((U.1 : ((Sch).obj T).Opens) : Set ((Sch).obj T)) := by
    intro x _
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := (Sch).obj T) (x := x)
      (U := ⊤) trivial
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun U => U.1.isOpen) hcover
  let κ : Type u := {U // U ∈ t}
  let O : κ → ((Sch).obj T).Opens := fun a => a.1.1
  have hOa : ∀ a, IsAffine ((Sch).obj (openObj (O a))) := fun a => a.1.2
  have hO : ∀ x, ∃ a, x ∈ O a := by
    intro x
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨U, hU, hx⟩ := this
    exact ⟨⟨U, hU⟩, hx⟩
  have hloc : ∀ a : κ, ∃ (i : ι) (φ' : AttractorPt act (Ni i) (openObj (O a))),
      AttractorPt.ofLE (hle i) φ' = φ.baseChange (openJ (O a)) := fun a => by
    haveI := hOa a
    exact P337.exists_ofLE_affine hsep (isLimitPreserving_of_lfp hX hfp) Ni hle hcov _
  choose i₀ φ₀ hφ₀ using hloc
  haveI : Finite κ := t.finite_toSet.to_subtype
  obtain ⟨k, hk⟩ := Finite.exists_le i₀
  let ψ : ∀ a : κ, AttractorPt act (Ni k) (openObj (O a)) := fun a =>
    AttractorPt.ofLE (Ni.monotone (hk a)) (φ₀ a)
  have hψ : ∀ a, AttractorPt.ofLE (hle k) (ψ a) = φ.baseChange (openJ (O a)) := fun a =>
    Eq.trans rfl (hφ₀ a)
  have hmem : Sieve.ofArrows (fun a => openObj (O a)) (fun a => openJ (O a)) ∈
      BigFppfOver.topology B S hS T := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
      (fun a => inferInstanceAs (IsOpenImmersion (iV _))) fun x => ?_
    obtain ⟨c, hc⟩ := hO x
    exact ⟨c, (⟨x, hc⟩ : O c), rfl⟩
  have hshk := isSheaf_attractor act (Ni k) _ hsh
  have hsf : (Presieve.ofArrows _ (fun a => openJ (O a))).IsSheafFor (attractor act (Ni k)) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hshk _ hmem
  obtain ⟨g, hg, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf ψ (by
    intro a b Z ga gb hab
    apply P337.ofLE_inj (act := act) hsh hd (hle k) Z
    change AttractorPt.baseChange ga (AttractorPt.ofLE (hle k) (ψ a)) =
      AttractorPt.baseChange gb (AttractorPt.ofLE (hle k) (ψ b))
    rw [hψ, hψ]
    refine AttractorPt.ext ?_
    funext T' s c
    change φ.app (s ≫ ga ≫ openJ (O a)) c = φ.app (s ≫ gb ≫ openJ (O b)) c
    rw [hab])
  refine ⟨k, g, ?_⟩
  refine ((isSheaf_attractor act N _ hsh) _ hmem).isSeparatedFor.ext fun W h' hh => ?_
  obtain ⟨_, r, s', ⟨a⟩, rfl⟩ := hh
  have h1 : AttractorPt.baseChange (openJ (O a)) g = ψ a := hg a
  have h2 : AttractorPt.baseChange (openJ (O a)) (AttractorPt.ofLE (hle k) g) =
      φ.baseChange (openJ (O a)) := by
    rw [← hψ, ← h1]
    rfl
  exact congrArg (AttractorPt.baseChange r) h2

/-- The diagram `i ↦ X^{N_i}(T)`. -/
noncomputable def prop337Diagram {ι : Type u} [Preorder ι] (Ni : ι →o AddSubmonoid M) (T : BigFppfOver B S hS) :
    ι ⥤ Type _ where
  obj i := AttractorPt act (Ni i) T
  map f := ↾ AttractorPt.ofLE (Ni.monotone (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone `X^{N_i}(T) → X^N(T)`. -/
noncomputable def prop337Cocone {ι : Type u} [Preorder ι] (Ni : ι →o AddSubmonoid M) {N : AddSubmonoid M}
    (hle : ∀ i, Ni i ≤ N) (T : BigFppfOver B S hS) : Cocone (prop337Diagram (act := act) Ni T) where
  pt := AttractorPt act N T
  ι := { app := fun i => ↾ AttractorPt.ofLE (hle i) }

/-- **Proposition 3.37** (corrected): `X` separated and locally of finite presentation over `S`, `N` a
directed union of submonoids `N_i` of an arbitrary commutative monoid `M`, `T → S` quasi-compact. Then
`X^N(T) = colim X^{N_i}(T)`. `hM` is the size cutoff of the site. -/
noncomputable def prop337_colimit (hX : IsAlgebraicSpace B S hS X) (hsep : IsSeparatedOver X)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS (terminal.from X)) (hM : #M < B.cutoff)
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Ni : ι →o AddSubmonoid M)
    {N : AddSubmonoid M} (hle : ∀ i, Ni i ≤ N) (hcov : ∀ x ∈ N, ∃ i, x ∈ Ni i)
    (T : BigFppfOver B S hS) [CompactSpace ((Sch).obj T)] :
    IsColimit (prop337Cocone (act := act) Ni hle T) :=
  haveI : Fact (#M < B.cutoff) := ⟨hM⟩
  Types.FilteredColimit.isColimitOf _ _
    (fun φ => by
      obtain ⟨i, φ', h⟩ := prop337_exists hX hsep hfp hM Ni hle hcov φ
      exact ⟨i, φ', h.symm⟩)
    (fun i j x y h => by
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
      exact P337.ofLE_inj (act := act) ((isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf)
        (hasDensePullback_of_separated hsep) (hle k) T h)

end AlgMag

#print axioms AlgMag.prop337_exists
#print axioms AlgMag.prop337_colimit
