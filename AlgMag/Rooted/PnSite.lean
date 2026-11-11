/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Rooted.DoubleScalarRooted
import AlgMag.Prop337General
import AlgMag.Sec5Etale

/-!
# Weighted `ℙ(ι)` over a scheme `S`: pure magnets and rootedness

Brochard–Mayeux, *Rooted spaces*, Theorem `thm:Pn` and Example `ex:Pn`, over an arbitrary nonempty scheme `S`.

`pnS B S hS ι` is `ℙ(ι)_S` on the big affine fppf site `BigAffineFppf B S hS` of `S` (Stacks 021S (2), whose
sheaves are the fppf sheaves on `Sch/S`, `bigAffineFppfInclusion_isDenseSubsite`): its value on an affine
`V → S` is the set of rank one direct summands of `Γ(V)^ι`. `act B S hS w` is the action of `D(M)_S` with
weights `w`, `h • [v] = [(h(w i) v i)_i]`. Attractors are computed on these affine test objects.
Proposition `attractor-limits`.

## Main results

* `mem_image_iff`: `K ∈ X^N(V)` iff `K` has a rank one projector whose `(i, j)` entry vanishes when
  `w i - w j ∉ N`. One direction is the universal point of `𝔸(N)` over `Spec Γ(V)[N]` (`exists_proj_of_attractor`),
  the other the twisted projector (`liftPt`).
* `image_eq_iff`: `X^N = X^L` iff `N ∩ Φ = L ∩ Φ`, by tangent vectors over `κ(x)[ε]`, `x ∈ S`.
* `isPure_iff`, `pureMagnets_bijOn`, `isPure_closure`, `pn_joinDense`: rooted by `Φ = Om w`.
* `prop41`, `dsAct_joinDense`, `ncard_pure`: `D(ℤ²)` on `ℙ²_S`, rooted by `Φ`, `29` pure magnets.

Hypotheses: universe `0` (the matrix algebra of `AlgMag.DoubleScalar` is stated in `Type`), `S` nonempty
(over the empty scheme all attractors agree), `#M < B.cutoff` (so that `Spec Γ(V)[M]` is a test object; automatic
for `M` countable). The fppf sheaf property of `pnS` and its representability are not formalized here.
-/

open CategoryTheory Opposite AlgebraicGeometry Matrix Cardinal

set_option linter.unusedSectionVars false

namespace AlgMag.DoubleScalar.PnSite

variable {B : BigFppfSite.{0}} {S : Scheme.{0}} {hS : B.Contains S}

local notation "SITE" => BigFppfOver B S hS
local notation "SCH" => BigFppfOver.toScheme B S hS

/-! ### Twisted projectors -/

section Twist

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommGroup M] (w : ι → M)
variable {D : Type} [CommRing D]

/-- `P` is supported on `N`: `P i j = 0` when `w i - w j ∉ N`. -/
def Supp (N : AddSubmonoid M) (P : Matrix ι ι D) : Prop := ∀ i j, w i - w j ∉ N → P i j = 0

/-- A character of `N`, extended by anything outside `N`. -/
structure IsChar (N : AddSubmonoid M) (c : M → D) : Prop where
  zero : c 0 = 1
  add : ∀ e f, e ∈ N → f ∈ N → c e * c f = c (e + f)

lemma rng_map_inj {D' : Type} [CommRing D'] (e : D ≃+* D') {A A' : Matrix ι ι D}
    (h : rng (A.map e) = rng (A'.map e)) : rng A = rng A' := by
  have := congrArg (bcv (e.symm : D' →+* D)) h
  rw [bcv_rng, bcv_rng, Matrix.map_map, Matrix.map_map] at this
  have k : ∀ X : Matrix ι ι D, X.map ((e.symm : D' →+* D) ∘ e) = X := fun X => by
    ext i j
    simp
  rwa [k, k] at this

/-- The twist `(P i j c(w i - w j))`. -/
def tw (P : Matrix ι ι D) (c : M → D) : Matrix ι ι D := Matrix.of fun i j => P i j * c (w i - w j)

variable {w}

lemma isRankOneProj_tw {N : AddSubmonoid M} {P : Matrix ι ι D} (hP : IsRankOneProj P)
    (hs : Supp w N P) {c : M → D} (hc : IsChar N c) : IsRankOneProj (tw w P c) := by
  refine isRankOneProj_of_twist hP (fun i j => c (w i - w j)) ?_ ?_ ?_
  · intro i
    simp only [sub_self]
    exact hc.zero
  · intro i j k
    by_cases h1 : w i - w j ∈ N
    · by_cases h2 : w j - w k ∈ N
      · have e : (w i - w j) + (w j - w k) = w i - w k := by abel
        rw [hc.add _ _ h1 h2, e]
      · rw [hs j k h2]; ring
    · rw [hs i j h1]; ring
  · intro i j k l
    have hmin := hP.minor i j k l
    by_cases h1 : w i - w j ∈ N
    · by_cases h2 : w k - w l ∈ N
      · by_cases h3 : w i - w l ∈ N
        · by_cases h4 : w k - w j ∈ N
          · have e : (w i - w j) + (w k - w l) = (w i - w l) + (w k - w j) := by abel
            rw [hc.add _ _ h1 h2, hc.add _ _ h3 h4, e, hmin]
          · have h0 : P i l * P k j = 0 := by rw [hs k j h4, mul_zero]
            rw [hmin, h0]; ring
        · have h0 : P i l * P k j = 0 := by rw [hs i l h3, zero_mul]
          rw [hmin, h0]; ring
      · have h0 : P i j * P k l = 0 := by rw [hs k l h2, mul_zero]
        rw [← hmin, h0]; ring
    · have h0 : P i j * P k l = 0 := by rw [hs i j h1, zero_mul]
      rw [← hmin, h0]; ring

lemma tw_mul {N : AddSubmonoid M} {P P' : Matrix ι ι D} (hs : Supp w N P) (hs' : Supp w N P')
    {c : M → D} (hc : IsChar N c) : tw w P c * tw w P' c = tw w (P * P') c := by
  ext i k
  simp only [tw, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : w i - w j ∈ N
  · by_cases h2 : w j - w k ∈ N
    · have e : (w i - w j) + (w j - w k) = w i - w k := by abel
      rw [← e, ← hc.add _ _ h1 h2]; ring
    · rw [hs' j k h2]; ring
  · rw [hs i j h1]; ring

/-- The twisted line does not depend on the supported projector. -/
lemma rng_tw_eq {N : AddSubmonoid M} {P P' : Matrix ι ι D} (hP : IsRankOneProj P)
    (hP' : IsRankOneProj P') (hs : Supp w N P) (hs' : Supp w N P') (h : rng P = rng P')
    {c : M → D} (hc : IsChar N c) : rng (tw w P c) = rng (tw w P' c) := by
  refine rng_eq_of_mul ?_ ?_
  · rw [tw_mul hs hs' hc, mul_eq_of_rng_le hP.idem h.ge]
  · rw [tw_mul hs' hs hc, mul_eq_of_rng_le hP'.idem h.le]

lemma tw_eq_self {N : AddSubmonoid M} {P : Matrix ι ι D} (hs : Supp w N P) {c : M → D}
    (hc : ∀ e ∈ N, c e = 1) : tw w P c = P := by
  ext i j
  simp only [tw, Matrix.of_apply]
  by_cases h : w i - w j ∈ N
  · rw [hc _ h, mul_one]
  · rw [hs i j h, zero_mul]

lemma Supp.map {N : AddSubmonoid M} {P : Matrix ι ι D} (hs : Supp w N P) {D' : Type} [CommRing D']
    (φ : D →+* D') : Supp w N (P.map φ) := fun i j h => by
  rw [Matrix.map_apply, hs i j h, map_zero]

lemma tw_map (P : Matrix ι ι D) (c : M → D) {D' : Type} [CommRing D'] (φ : D →+* D') :
    (tw w P c).map φ = tw w (P.map φ) (fun e => φ (c e)) := by
  ext i j
  simp [tw]

lemma supp_iff_of_inter {N L : AddSubmonoid M} (h : (N : Set M) ∩ Om w = (L : Set M) ∩ Om w)
    (P : Matrix ι ι D) : Supp w N P → Supp w L P := by
  intro hs i j hij
  refine hs i j fun hn => hij ?_
  by_cases hne : i = j
  · subst hne
    simp
  · have : w i - w j ∈ (N : Set M) ∩ Om w := ⟨hn, i, j, hne, rfl⟩
    rw [h] at this
    exact this.1

/-- **The tangent test.** A rank one projector with image `D (e_s + ε e_j)`, `ε² = 0 ≠ ε`, has
`P j s ≠ 0`. -/
lemma tangent_contra {P : Matrix ι ι D} (hP : IsRankOneProj P) {s j : ι} (hj : j ≠ s) {u : ι → D}
    {e : D} (hus : u s = 1) (huj : u j = e) (hu0 : ∀ i, i ≠ s → i ≠ j → u i = 0) (hee : e * e = 0)
    (he : e ≠ 0) (hK : Submodule.span D {u} = rng P) (h0 : P j s = 0) : False := by
  classical
  have hfix : P *ᵥ u = u := (mem_rng_iff hP.idem).mp (hK ▸ Submodule.mem_span_singleton_self u)
  have h1 : P j s = P s s * e := by
    have := hP.cross (col_fixed hP.idem s) hfix j s
    rw [hus, mul_one, huj] at this
    exact this
  have h2 : P s s + P s j * e = 1 := by
    have := congrFun hfix s
    rw [hus] at this
    change ∑ k, P s k * u k = 1 at this
    rw [← this, Finset.sum_eq_add_of_mem s j (Finset.mem_univ _) (Finset.mem_univ _) hj.symm]
    · rw [hus, mul_one, huj]
    · intro c _ hc
      rw [hu0 c hc.1 hc.2, mul_zero]
  have e' : (P s s + P s j * e) * e = P s s * e := by
    rw [add_mul, mul_assoc, hee, mul_zero, add_zero]
  rw [h2, one_mul, ← h1, h0] at e'
  exact he e'

end Twist

/-! ### The functor `ℙ(ι)_S` on the affine fppf site -/

section Functor

local notation "AFF" => BigAffineFppf B S hS

variable (B S hS) in
/-- Functions on the big affine fppf site of `S`. -/
noncomputable abbrev OA : (BigAffineFppf B S hS)ᵒᵖ ⥤ CommRingCat.{0} :=
  (BigAffineFppf.inclusion B S hS).op ⋙ fppfO B S hS

variable (B S hS) in
/-- Functions on an affine object. -/
abbrev O (V : BigAffineFppf B S hS) : Type := (OA B S hS).obj (op V)

/-- Pullback of functions. -/
noncomputable def gm {V V' : AFF} (s : V' ⟶ V) : O B S hS V →+* O B S hS V' :=
  ((OA B S hS).map s.op).hom

lemma gm_comp {V V' V'' : AFF} (s' : V'' ⟶ V') (s : V' ⟶ V) :
    gm (s' ≫ s) = (gm s').comp (gm s) := by
  simp only [gm, op_comp, Functor.map_comp, CommRingCat.hom_comp]

lemma gm_id (V : AFF) : gm (𝟙 V) = RingHom.id _ := by
  simp only [gm, op_id]
  rfl

variable (ι : Type) [Fintype ι] [DecidableEq ι]

variable (B S hS) in
/-- **`ℙ(ι)_S`** on the big affine fppf site of `S` (Stacks 021S): `ℙ(ι)_S(V)` is the set of rank one direct
summands of `Γ(V)^ι`. -/
noncomputable def pnS : (BigAffineFppf B S hS)ᵒᵖ ⥤ Type where
  obj V := {K : Submodule (O B S hS (unop V)) (ι → O B S hS (unop V)) // IsLineN K}
  map f := ↾ fun K => ⟨bcv (gm f.unop) K.1, K.2.bcv _⟩
  map_id V := by
    ext K x
    change x ∈ bcv (gm (𝟙 (unop V))) K.1 ↔ x ∈ K.1
    rw [gm_id, bcv_id]
  map_comp f g := by
    ext K x
    change x ∈ bcv (gm (g.unop ≫ f.unop)) K.1 ↔ x ∈ bcv (gm g.unop) (bcv (gm f.unop) K.1)
    rw [gm_comp, bcv_comp]

variable {ι}

lemma dgl_one {D : Type} [CommRing D] : dgl (fun _ : ι => (1 : D)) = LinearMap.id := by
  ext x i
  simp [dgl]

lemma dgl_mul {D : Type} [CommRing D] (u u' : ι → D) :
    dgl (fun i => u i * u' i) = (dgl u).comp (dgl u') := by
  ext x i
  simp [dgl, mul_assoc]

variable {M : Type} [AddCommGroup M] (w : ι → M)

variable (B S hS) in
/-- **The action of `D(M)_S` on `ℙ(ι)_S` with weights `w`**: `h • [v] = [(h(w i) v i)_i]`. -/
noncomputable def act : AAction (OA B S hS) M (pnS B S hS ι) where
  smul {U} h K := ⟨K.1.map (dgl fun i => h (Multiplicative.ofAdd (w i))),
    K.2.map_dgl (v := fun i => h (Multiplicative.ofAdd (-w i))) fun i => apt_inv h (w i)⟩
  one_smul {U} K := by
    refine Subtype.ext ?_
    change K.1.map (dgl fun i => (1 : APt (OA B S hS) M U) (Multiplicative.ofAdd (w i))) = K.1
    simp only [MonoidHom.one_apply]
    rw [dgl_one, Submodule.map_id]
  mul_smul {U} g h K := by
    refine Subtype.ext ?_
    change K.1.map (dgl fun i => (g * h) (Multiplicative.ofAdd (w i))) =
      (K.1.map (dgl fun i => h (Multiplicative.ofAdd (w i)))).map
        (dgl fun i => g (Multiplicative.ofAdd (w i)))
    rw [← Submodule.map_comp, ← dgl_mul]
    simp only [MonoidHom.mul_apply]
  map_smul {U U'} f h K := by
    refine Subtype.ext ?_
    exact bcv_map_dgl (gm f.unop) (fun i => h (Multiplicative.ofAdd (w i))) K.1

/-! ### Attractors -/

variable {w}

open Classical in
/-- The coordinate `a(e)` of `a ∈ 𝔸(N)`, zero if `e ∉ N`. -/
noncomputable def xv (N : AddSubmonoid M) (e : M) {V : AFF} (a : APt (OA B S hS) N (op V)) :
    O B S hS V :=
  if h : e ∈ N then a (Multiplicative.ofAdd (⟨e, h⟩ : N)) else 0

lemma xv_isChar (N : AddSubmonoid M) {V : AFF} (a : APt (OA B S hS) N (op V)) :
    IsChar N (fun e => xv N e a) where
  zero := by
    unfold xv
    rw [dif_pos N.zero_mem]
    exact a.map_one
  add e f he hf := by
    unfold xv
    rw [dif_pos he, dif_pos hf, dif_pos (N.add_mem he hf)]
    exact (a.map_mul (Multiplicative.ofAdd (⟨e, he⟩ : N)) (Multiplicative.ofAdd (⟨f, hf⟩ : N))).symm

lemma xv_res (N : AddSubmonoid M) (e : M) {V V' : AFF} (s : V' ⟶ V)
    (a : APt (OA B S hS) N (op V)) : xv N e (APt.res s.op a) = gm s (xv N e a) := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (map_zero _).symm

lemma xv_mul (N : AddSubmonoid M) (e : M) {V : AFF} (g : APt (OA B S hS) M (op V))
    (a : APt (OA B S hS) N (op V)) :
    xv N e (APt.toMagnet N g * a) = g (Multiplicative.ofAdd e) * xv N e a := by
  unfold xv
  split_ifs with h
  · rfl
  · exact (mul_zero _).symm

lemma xv_one (N : AddSubmonoid M) {e : M} (h : e ∈ N) {V : AFF} :
    xv N e (1 : APt (OA B S hS) N (op V)) = 1 := by
  unfold xv
  rw [dif_pos h]
  rfl

section Lift

variable {N : AddSubmonoid M} {T : BigAffineFppf B S hS} {P : Matrix ι ι (O B S hS T)} (hP : IsRankOneProj P)
  (hs : Supp w N P)

variable (w) in
/-- **The converse of the key step.** A rank one projector supported on `N` gives a point of `X^N`. -/
noncomputable def liftPt : AttractorPt (act B S hS w) N T where
  app {T'} t a := ⟨rng (tw w (P.map (gm t)) fun e => xv N e a), _,
    isRankOneProj_tw (hP.map _) (hs.map _) (xv_isChar N a), rfl⟩
  naturality {T' T''} s t a := by
    refine Subtype.ext ?_
    change _ = bcv (gm s) (rng _)
    rw [bcv_rng, tw_map, gm_comp, Matrix.map_map]
    exact congrArg rng (congrArg₂ (tw w) rfl (funext fun e => xv_res N e s a))
  equivariant {T'} t g a := by
    refine Subtype.ext ?_
    change _ = (rng _).map _
    rw [map_dgl_rng (v := fun i => g (Multiplicative.ofAdd (-w i))) (fun i => apt_inv g (w i))]
    refine congrArg rng (Matrix.ext fun i j => ?_)
    simp only [tw, Matrix.of_apply]
    rw [xv_mul, apt_sub g (w i) (w j)]
    ring

lemma liftPt_toPoint : ((liftPt w hP hs).toPoint).1 = rng P := by
  change rng _ = rng P
  rw [gm_id, show P.map (RingHom.id _) = P from Matrix.ext fun _ _ => rfl,
    tw_eq_self hs fun e he => xv_one N he]


end Lift

section Core

variable [hM : Fact (#M < B.cutoff)] {N : AddSubmonoid M}

/-- **The key step**, by the universal point of `𝔸(N)` over `Spec Γ(T)[N]`: a point of `X^N` has a rank one
projector supported on `N`. -/
theorem exists_proj_of_attractor {T : AFF} (φ : AttractorPt (act B S hS w) N T)
    {P : Matrix ι ι (O B S hS T)} (hP : IsRankOneProj P) (hK : φ.toPoint.1 = rng P) :
    ∃ P' : Matrix ι ι (O B S hS T), IsRankOneProj P' ∧ rng P' = rng P ∧ Supp w N P' := by
  classical
  have : IsAffine ((SCH).obj T.obj) := T.property
  let P0 : Matrix ι ι (RT T.obj) := P
  have hP0 : IsRankOneProj P0 := hP
  let hCN : B.Contains (Spec (.of (AddMonoidAlgebra (RT T.obj) N))) := P337.contains_any T.obj N
  let hCM : B.Contains (Spec (.of (AddMonoidAlgebra (RT T.obj) M))) :=
    P337.contains_M (contains_RT T.obj)
  let ρM : RT T.obj →+* AddMonoidAlgebra (RT T.obj) M := AddMonoidAlgebra.singleZeroRingHom
  let EN : AFF := ⟨spObj T.obj (ρN T.obj N) hCN, inferInstance⟩
  let EZ : AFF := ⟨spObj T.obj ρM hCM, inferInstance⟩
  let tN : EN ⟶ T := ObjectProperty.homMk (spToT T.obj (ρN T.obj N) hCN)
  let tZ : EZ ⟶ T := ObjectProperty.homMk (spToT T.obj ρM hCM)
  let τ : AddMonoidAlgebra (RT T.obj) N →+* AddMonoidAlgebra (RT T.obj) M :=
    (AddMonoidAlgebra.mapDomainAlgHom (RT T.obj) (RT T.obj) N.subtype).toRingHom
  have hτ : τ.comp (ρN T.obj N) = ρM := RingHom.ext fun r => by
    change AddMonoidAlgebra.mapDomainAlgHom (RT T.obj) (RT T.obj) N.subtype
      (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
    simp
  let tτ : EZ ⟶ EN := ObjectProperty.homMk (spMap T.obj (hC := hCN) (hC' := hCM) τ hτ)
  have htt : tτ ≫ tN = tZ := ObjectProperty.hom_ext _ (spMap_toT T.obj τ hτ)
  let σN := spSec T.obj (ρN T.obj N) hCN
  let σM := spSec T.obj ρM hCM
  let aN : APt (OA B S hS) N (op EN) :=
    spPt (T := T.obj) (ρ := ρN T.obj N) (hC := hCN) (AddMonoidAlgebra.of (RT T.obj) N)
  let hU : APt (OA B S hS) M (op EZ) :=
    spPt (T := T.obj) (ρ := ρM) (hC := hCM) (AddMonoidAlgebra.of (RT T.obj) M)
  have e1 := φ.naturality tτ tN aN
  rw [htt] at e1
  have e2 : APt.res tτ.op aN = APt.toMagnet N hU * 1 := by
    refine MonoidHom.ext fun n => ?_
    rw [mul_one]
    refine (spMap_appTop T.obj (hC := hCN) (hC' := hCM) τ hτ _).trans ?_
    change σM (AddMonoidAlgebra.mapDomainAlgHom (RT T.obj) (RT T.obj) N.subtype
      (AddMonoidAlgebra.single _ 1)) = σM (AddMonoidAlgebra.single _ 1)
    simp
  have e3 := φ.equivariant tZ hU 1
  have e4 := φ.naturality tZ (𝟙 T) 1
  rw [Category.comp_id, show APt.res tZ.op (1 : APt (OA B S hS) N (op T)) = 1 from by ext; simp]
    at e4
  rw [e2, e3, e4] at e1
  obtain ⟨Q, hQ, hQK⟩ := (φ.app tN aN).2
  have v1 := congrArg Subtype.val e1
  change (bcv (gm tZ) φ.toPoint.1).map (dgl fun i => hU (Multiplicative.ofAdd (w i))) =
    bcv (gm tτ) (φ.app tN aN).1 at v1
  rw [hK, hQK, bcv_rng, bcv_rng, map_dgl_rng (v := fun i => hU (Multiplicative.ofAdd (-w i)))
    (fun i => apt_inv hU (w i))] at v1
  let eN := RingEquiv.ofBijective σN (spSec_bijective T.obj (ρN T.obj N) hCN)
  let eM := RingEquiv.ofBijective σM (spSec_bijective T.obj ρM hCM)
  let ψN : O B S hS EN →+* AddMonoidAlgebra (RT T.obj) N := eN.symm.toRingHom
  let Q' : Matrix ι ι (AddMonoidAlgebra (RT T.obj) N) := Q.map ψN
  let A : Matrix ι ι (AddMonoidAlgebra (RT T.obj) M) := Q'.map τ
  let Tm : Matrix ι ι (AddMonoidAlgebra (RT T.obj) M) :=
    Matrix.of fun i j => AddMonoidAlgebra.single (w i - w j) (P0 i j)
  have hA : Q.map (gm tτ) = A.map σM := by
    ext i j
    simp only [Matrix.map_apply, A, Q']
    have : Q i j = σN (eN.symm (Q i j)) := (eN.apply_symm_apply _).symm
    conv_lhs => rw [this]
    exact spMap_appTop T.obj (hC := hCN) (hC' := hCM) τ hτ _
  have hT : (Matrix.of fun i j => (P.map (gm tZ)) i j *
      (hU (Multiplicative.ofAdd (w i)) * hU (Multiplicative.ofAdd (-w j)))) = Tm.map σM := by
    ext i j
    simp only [Matrix.of_apply, Matrix.map_apply, Tm]
    have h1 : gm tZ (P i j) = σM (ρM (P i j)) := spToT_appTop T.obj ρM hCM (P i j)
    rw [h1]
    change σM _ * (σM (AddMonoidAlgebra.single (w i) 1) * σM (AddMonoidAlgebra.single (-w j) 1)) = _
    rw [← map_mul, ← map_mul]
    congr 1
    change (AddMonoidAlgebra.single 0 (P0 i j) : AddMonoidAlgebra (RT T.obj) M) *
      (AddMonoidAlgebra.single (w i) 1 * AddMonoidAlgebra.single (-w j) 1) = _
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
    simp [sub_eq_add_neg]
  rw [hA, hT] at v1
  have h : rng A = rng Tm := (rng_map_inj eM v1).symm
  obtain ⟨P', hP', e, hs⟩ := coeff_core w N hP0 ((hQ.map ψN).map τ)
    (fun i j n hn => coeff_mapSub N _ hn) (isRankOneProj_single w hP0) h
  exact ⟨P', hP', e, hs⟩

/-- **The attractor, on points.** `K ∈ X^N(T)` iff `K` has a rank one projector supported on `N`. -/
theorem mem_image_iff {T : AFF} (K : (pnS B S hS ι).obj (op T)) :
    K ∈ attractorImage (act B S hS w) N T ↔
      ∃ P : Matrix ι ι (O B S hS T), IsRankOneProj P ∧ K.1 = rng P ∧ Supp w N P := by
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨P, hP, hK⟩ := φ.toPoint.2
    obtain ⟨P', hP', e, hs⟩ := exists_proj_of_attractor φ hP hK
    exact ⟨P', hP', hK.trans e.symm, hs⟩
  · rintro ⟨P, hP, hK, hs⟩
    exact ⟨liftPt w hP hs, Subtype.ext ((liftPt_toPoint hP hs).trans hK.symm)⟩

end Core

section Tangent

variable [hM : Fact (#M < B.cutoff)] (x₀ : S)

variable (B hS) in
/-- `Spec κ(x₀)` as an object of the site. -/
noncomputable abbrev T0 : BigFppfOver B S hS :=
  siteObject B S hS (B.residueField_spec_contains hS x₀) (S.fromSpecResidueField x₀)

instance : IsAffine ((SCH).obj (T0 B hS x₀)) := by
  change IsAffine (Spec _)
  infer_instance

lemma nontrivial_T0 : Nontrivial (RT (T0 B hS x₀)) := by
  change Nontrivial Γ(Spec (S.residueField x₀), ⊤)
  exact (Scheme.ΓSpecIso (S.residueField x₀)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

lemma contains_eps : B.Contains (Spec (.of (DualNumber (RT (T0 B hS x₀))))) := by
  have h := P337.contains_iff.mp (contains_RT (T0 B hS x₀))
  refine P337.contains_iff.mpr ?_
  change #(RT (T0 B hS x₀) × RT (T0 B hS x₀)) < _
  rw [Cardinal.mk_prod, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le h h

variable (B hS) in
/-- `Spec κ(x₀)[ε]`, the test object. -/
noncomputable abbrev Te : AFF :=
  ⟨spObj (T0 B hS x₀) (algebraMap _ (DualNumber (RT (T0 B hS x₀)))) (contains_eps x₀), inferInstance⟩

/-- `κ(x₀)[ε] → Γ(Spec κ(x₀)[ε])`. -/
noncomputable def ψe : DualNumber (RT (T0 B hS x₀)) →+* O B S hS (Te B hS x₀) :=
  spSec (T0 B hS x₀) (algebraMap _ (DualNumber (RT (T0 B hS x₀)))) (contains_eps x₀)

lemma ψe_injective : Function.Injective (ψe (B := B) (hS := hS) x₀) :=
  (spSec_bijective (T0 B hS x₀) _ (contains_eps x₀)).1

lemma isLineN_span (R : Type) [CommRing R] (s j : ι) :
    IsLineN (Submodule.span (DualNumber R) {tangentVec R s j}) :=
  ⟨chartProj s _, isRankOneProj_chartProj s (tangentVec_self s j),
    (rng_chartProj s (tangentVec_self s j)).symm⟩

variable (B hS) in
/-- The tangent vector `e_s + ε e_j` at the fixed point `s`, over `Spec κ(x₀)[ε]`. -/
noncomputable def Ke (s j : ι) : (pnS B S hS ι).obj (op (Te B hS x₀)) :=
  ⟨bcv (ψe x₀) (Submodule.span _ {tangentVec (RT (T0 B hS x₀)) s j}),
    (isLineN_span _ s j).bcv (ψe x₀)⟩

lemma chart_supp {R : Type} [CommRing R] {N : AddSubmonoid M} {s j : ι} (h : w j - w s ∈ N) :
    Supp w N (chartProj s (tangentVec R s j)) := by
  intro i k hik
  change (if k = s then tangentVec R s j i else 0) = 0
  by_cases hk : k = s
  · subst hk
    rw [if_pos rfl]
    by_cases hi : i = k
    · subst hi; simp at hik
    · by_cases hij : i = j
      · subst hij; exact absurd h hik
      · exact tangentVec_other hi hij
  · rw [if_neg hk]

lemma tangent_mem {N : AddSubmonoid M} {s j : ι} (h : w j - w s ∈ N) :
    Ke B hS x₀ s j ∈ attractorImage (act B S hS w) N (Te B hS x₀) := by
  refine (mem_image_iff _).mpr ⟨(chartProj s (tangentVec _ s j)).map (ψe x₀),
    (isRankOneProj_chartProj s (tangentVec_self s j)).map _, ?_, (chart_supp h).map _⟩
  change bcv (ψe x₀) _ = _
  rw [← rng_chartProj s (tangentVec_self s j), bcv_rng]

lemma mem_of_tangent {L : AddSubmonoid M} {s j : ι} (hj : j ≠ s)
    (h : Ke B hS x₀ s j ∈ attractorImage (act B S hS w) L (Te B hS x₀)) : w j - w s ∈ L := by
  classical
  have := nontrivial_T0 (B := B) (hS := hS) x₀
  by_contra hL
  obtain ⟨P, hP, hK, hs⟩ := (mem_image_iff _).mp h
  have hK' : Submodule.span _ {fun i => ψe x₀ (tangentVec (RT (T0 B hS x₀)) s j i)} = rng P := by
    rw [← hK]
    change _ = bcv (ψe x₀) _
    rw [bcv_span, Set.image_singleton]
  refine tangent_contra hP hj (e := ψe x₀ DualNumber.eps) ?_ ?_ ?_ ?_ ?_ hK' (hs j s hL)
  · simp [tangentVec_self]
  · simp [tangentVec_of_ne hj]
  · intro i h1 h2
    simp [tangentVec_other h1 h2]
  · rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  · intro h0
    have := ψe_injective (B := B) (hS := hS) x₀ (h0.trans (map_zero _).symm)
    exact one_ne_zero (α := RT (T0 B hS x₀)) (by simpa using congrArg TrivSqZeroExt.snd this)

variable (w) in
/-- **`X^N = X^L` iff `N ∩ Φ = L ∩ Φ`**, for `ℙ(ι)_S`, `S` nonempty. -/
theorem image_eq_iff [Nonempty S] {N L : AddSubmonoid M} :
    attractorImage (act B S hS w) N = attractorImage (act B S hS w) L ↔
      (N : Set M) ∩ Om w = (L : Set M) ∩ Om w := by
  constructor
  · intro e
    have key : ∀ {N L : AddSubmonoid M}, attractorImage (act B S hS w) N =
        attractorImage (act B S hS w) L → (N : Set M) ∩ Om w ⊆ (L : Set M) ∩ Om w := by
      rintro N L e _ ⟨hx, i, j, hij, rfl⟩
      refine ⟨?_, i, j, hij, rfl⟩
      refine mem_of_tangent (B := B) (hS := hS) (w := w) (Classical.arbitrary S) hij ?_
      rw [← e]
      exact tangent_mem (B := B) (hS := hS) (w := w) (Classical.arbitrary S) hx
    exact Set.Subset.antisymm (key e) (key e.symm)
  · intro h
    funext T
    ext K
    rw [mem_image_iff, mem_image_iff]
    constructor
    · rintro ⟨P, hP, hK, hs⟩
      exact ⟨P, hP, hK, supp_iff_of_inter h P hs⟩
    · rintro ⟨P, hP, hK, hs⟩
      exact ⟨P, hP, hK, supp_iff_of_inter h.symm P hs⟩

end Tangent

end Functor

/-! ### Pure magnets and rootedness -/

section Abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommGroup M] (w : ι → M)
variable {α : Type*} [CompleteLattice α] {Y : AddSubmonoid M → α}
  (hY : ∀ N L : AddSubmonoid M, Y N = Y L ↔ (N : Set M) ∩ Om w = (L : Set M) ∩ Om w)
include hY

omit hY in
lemma closure_inter_inter' (N : AddSubmonoid M) :
    ((AddSubmonoid.closure ((N : Set M) ∩ Om w) : AddSubmonoid M) : Set M) ∩ Om w =
      (N : Set M) ∩ Om w := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hx, hO⟩
    exact ⟨(AddSubmonoid.closure_le.mpr Set.inter_subset_left) hx, hO⟩
  · exact fun x hx => ⟨AddSubmonoid.subset_closure hx, hx.2⟩

theorem isPure_iff_of {N : AddSubmonoid M} :
    IsPure Y N ↔ N = AddSubmonoid.closure ((N : Set M) ∩ Om w) := by
  constructor
  · exact fun h => IsPure.eq_closure_inter (fun N => (hY _ _).2 (closure_inter_inter' w N).symm) h
  · intro h L e
    rw [h]
    refine AddSubmonoid.closure_le.mpr ?_
    rw [(hY _ _).1 e]
    exact Set.inter_subset_left

theorem pureMagnets_bijOn_of :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Om w) (pureMagnets Y) {E | AddStableIn w E} := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    refine ⟨Set.inter_subset_right, ?_⟩
    change _ ∩ _ = _
    rw [← (isPure_iff_of w hY).mp hN]
  · intro N hN L hL e
    rw [(isPure_iff_of w hY).mp hN, (isPure_iff_of w hY).mp hL]
    exact congrArg _ e
  · intro E hE
    have hE' : ((AddSubmonoid.closure E : AddSubmonoid M) : Set M) ∩ Om w = E := hE.2
    refine ⟨AddSubmonoid.closure E, ?_, hE'⟩
    refine (isPure_iff_of w hY).mpr ?_
    change _ = AddSubmonoid.closure (_ ∩ _)
    rw [hE']

theorem isPure_closure_of {E : Set M} (hE : AddStableIn w E) : IsPure Y (AddSubmonoid.closure E) := by
  refine (isPure_iff_of w hY).mpr ?_
  rw [hE.2]

theorem joinDense_of : AlgMag.Rooted.IsJoinDense (IsPure Y) (AlgMag.Rooted.mono '' Om w) := by
  rw [AlgMag.Rooted.isJoinDense_mono_iff]
  exact ⟨fun N hN => (pureMagnets_bijOn_of w hY).mapsTo hN,
    fun N hN => ((isPure_iff_of w hY).1 hN).symm, fun E hE => isPure_closure_of w hY hE⟩

end Abstract

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommGroup M] (w : ι → M)
variable [Fact (#M < B.cutoff)] [Nonempty S]

/-- **Theorem `thm:Pn`, pure magnets.** A magnet of `D(M)_S` acting on `ℙ(ι)_S` is pure iff it is generated by
its elements in `Φ`. -/
theorem isPure_iff {N : AddSubmonoid M} :
    IsPure (attractorImage (act B S hS w)) N ↔ N = AddSubmonoid.closure ((N : Set M) ∩ Om w) :=
  isPure_iff_of w fun _ _ => image_eq_iff w

/-- **Proposition 4.1 for `ℙ(ι)_S`.** `N ↦ N ∩ Φ` is a bijection from the pure magnets to the additively stable
subsets of `Φ`. -/
theorem pureMagnets_bijOn :
    Set.BijOn (fun N : AddSubmonoid M => (N : Set M) ∩ Om w)
      (pureMagnets (attractorImage (act B S hS w))) {E | AddStableIn w E} :=
  pureMagnets_bijOn_of w fun _ _ => image_eq_iff w

/-- The inverse bijection: a stable set is sent to the monoid it generates. -/
theorem isPure_closure {E : Set M} (hE : AddStableIn w E) :
    IsPure (attractorImage (act B S hS w)) (AddSubmonoid.closure E) :=
  isPure_closure_of w (fun _ _ => image_eq_iff w) hE

/-- **Theorem `thm:Pn`.** The action of `D(M)_S` on `ℙ(ι)_S` with weights `w` is rooted by the weight
differences `Φ = Om w`. -/
theorem pn_joinDense :
    AlgMag.Rooted.IsJoinDense (IsPure (attractorImage (act B S hS w))) (AlgMag.Rooted.mono '' Om w) :=
  joinDense_of w fun _ _ => image_eq_iff w

end Main

section DoubleScalar

variable [Nonempty S]

instance fact_cutoff_int2 : Fact (#(ℤ × ℤ) < B.cutoff) :=
  ⟨Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff⟩

/-- **Example `ex:Pn`, Proposition 4.1 over `S`.** `D(ℤ²)` acting on `ℙ²_S` with weights
`((1,0), (0,1), (0,0))`: the pure magnets are the `[E⟩`, `E ⊆ Φ` additively stable. -/
theorem prop41 :
    Set.BijOn (fun N : AddSubmonoid (ℤ × ℤ) => (N : Set (ℤ × ℤ)) ∩ (Phi : Set (ℤ × ℤ)))
      (pureMagnets (attractorImage (act B S hS wP))) {E | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} := by
  have h := pureMagnets_bijOn (B := B) (S := S) (hS := hS) wP
  have e : {E | AddStableIn wP E} = {E : Set (ℤ × ℤ) | E ⊆ (Phi : Set (ℤ × ℤ)) ∧ AddStable E} := by
    ext E
    change (E ⊆ Om wP ∧ _ ∩ Om wP = E) ↔ _
    rw [om_eq]
    rfl
  rw [e] at h
  simp only [om_eq] at h
  exact h

/-- **Example `ex:Pn`.** `D(ℤ²)` acting on `ℙ²_S` is rooted by `Φ`. -/
theorem dsAct_joinDense :
    AlgMag.Rooted.IsJoinDense (IsPure (attractorImage (act B S hS wP)))
      (AlgMag.Rooted.mono '' (Phi : Set (ℤ × ℤ))) := by
  rw [← om_eq]
  exact pn_joinDense wP

/-- **§4 over `S`.** `D(ℤ²)` acting on `ℙ²_S` has `29` pure magnets. -/
theorem ncard_pure : (pureMagnets (attractorImage (act B S hS wP))).ncard = 29 := by
  have h := prop41 (B := B) (S := S) (hS := hS)
  rw [stable_set_eq] at h
  have e1 := h.injOn.ncard_image
  rw [h.image_eq, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset,
    card_stable] at e1
  exact e1.symm

end DoubleScalar

end AlgMag.DoubleScalar.PnSite

#print axioms AlgMag.DoubleScalar.PnSite.mem_image_iff
#print axioms AlgMag.DoubleScalar.PnSite.image_eq_iff
#print axioms AlgMag.DoubleScalar.PnSite.pn_joinDense
#print axioms AlgMag.DoubleScalar.PnSite.pureMagnets_bijOn
#print axioms AlgMag.DoubleScalar.PnSite.dsAct_joinDense
#print axioms AlgMag.DoubleScalar.PnSite.ncard_pure
