/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.GeneralBase
import AlgMag.Sec15PureMagnets

/-!
# Example 15.10 (ii) over an arbitrary base

`D(G)_S` acting on itself by multiplication has `Π(a) = {0, G}`, for `S` any nonempty scheme.
`AlgMag.pureMagnets_group_self` treats `S = Spec R`. `G` is any nonzero group, in particular `ℤⁿ`,
`n ≥ 1`. For `n = 0` the printed set `{0, ℤⁿ}` has one element, and the statement is also true.
-/

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgMag.Leftover

open AlgMag.GB

variable {G : Type u} [AddCommGroup G] {S : Scheme.{u}}

section Core

variable (R : CommRingCat.{u}) (p : Spec R ⟶ S)

/-- `Spec C` over `S`, for an `R`-algebra `C`. -/
private noncomputable abbrev sp {C : CommRingCat.{u}} (ψ : R ⟶ C) : Over S :=
  Over.mk (Spec.map ψ ≫ p)

/-- The `Spec C → Spec R`, over `S`. -/
private noncomputable abbrev spι {C : CommRingCat.{u}} (ψ : R ⟶ C) :
    sp R p ψ ⟶ Over.mk p :=
  Over.homMk (Spec.map ψ) rfl

/-- The monoid map `P → Γ(Spec R[P])`. -/
private noncomputable def uni (P : Type u) [AddCommMonoid P] :
    Multiplicative P →* Γ(Spec (CommRingCat.of (AddMonoidAlgebra R P)), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R P))).inv.hom.toMonoidHom).comp
    (AddMonoidAlgebra.of R P)

private noncomputable abbrev cst (P : Type u) [AddCommMonoid P] :
    R ⟶ CommRingCat.of (AddMonoidAlgebra R P) :=
  CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R P))

private lemma uni_ev (P : Type u) [AddCommMonoid P] (a : Multiplicative P) :
    (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R P))).hom.hom (uni R P a) =
      AddMonoidAlgebra.single (Multiplicative.toAdd a) 1 := by
  have := congrArg (fun k => k.hom (AddMonoidAlgebra.of R P a))
    (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R P))).inv_hom_id
  exact this

private lemma gam {A B : CommRingCat.{u}} (ψ : A ⟶ B) (z : Γ(Spec A, ⊤)) :
    (Scheme.ΓSpecIso B).hom.hom ((Spec.map ψ).appTop.hom z) =
      ψ.hom ((Scheme.ΓSpecIso A).hom.hom z) :=
  congrArg (fun k => k.hom z) (Scheme.ΓSpecIso_naturality ψ)

/-- The core of Example 15.10 (ii): over `Spec R ≠ ∅`, `X^K` has no point for `K ≠ G`. For the
universal `h` on `R[G]`, equivariance gives `φ(h|_K) = h · x`, whose `m`-coordinate is `c X^m` with
`c` a unit. It comes from `R[K]`, so `m ∈ K`. -/
theorem no_point_core [Nontrivial R] {K : AddSubmonoid G} {m : G} (hm : m ∉ K)
    (φ : AttractorPt (aAction (⊤ : AddSubmonoid G) S) K (Over.mk p)) : False := by
  let i : CommRingCat.of (AddMonoidAlgebra R K) ⟶ CommRingCat.of (AddMonoidAlgebra R G) :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R K.subtype)
  have hi : cst R K ≫ i = cst R G := by
    ext r
    simp [i, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapDomain_single]
  let tK := spι R p (cst R K)
  let tG := spι R p (cst R G)
  let s : sp R p (cst R G) ⟶ sp R p (cst R K) := Over.homMk (Spec.map i) (by
    change Spec.map i ≫ Spec.map (cst R K) ≫ p = Spec.map (cst R G) ≫ p
    rw [← Category.assoc, ← Spec.map_comp, hi])
  have hst : s ≫ tK = tG := by
    apply Over.OverMorphism.ext
    change Spec.map i ≫ Spec.map (cst R K) = Spec.map (cst R G)
    rw [← Spec.map_comp, hi]
  let u : APt (overO S) K (op (sp R p (cst R K))) := uni R K
  let h : APt (overO S) G (op (sp R p (cst R G))) := uni R G
  have hu : APt.res s.op u = APt.toMagnet K h := by
    ext n
    apply (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R G))).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso _).hom.hom ((Spec.map i).appTop.hom (uni R K (Multiplicative.ofAdd n))) =
      (Scheme.ΓSpecIso _).hom.hom (uni R G (Multiplicative.ofAdd (n : G)))
    rw [gam, uni_ev, uni_ev]
    simp [i, AddMonoidAlgebra.mapDomain_single]
  have nat := φ.naturality s tK u
  have eqv := φ.equivariant tG h 1
  have one := φ.naturality tG (𝟙 _) 1
  rw [hst, hu] at nat
  have one' : φ.app tG 1 = tG ≫ φ.toPoint := by
    have e : APt.res tG.op (1 : APt (overO S) K (op (Over.mk p))) = 1 := by ext; simp
    rw [Category.comp_id, e] at one
    exact one
  rw [mul_one] at eqv
  rw [nat, one'] at eqv
  let m' : Multiplicative (⊤ : AddSubmonoid G) := Multiplicative.ofAdd ⟨m, trivial⟩
  let y := φ.app tK u
  have key : APt.res s.op (pts _ y) m' =
      APt.toMagnet (⊤ : AddSubmonoid G) h m' * APt.res tG.op (pts _ φ.toPoint) m' := by
    have := congrArg (fun z => pts (sp R p (cst R G)) z m') eqv
    change pts _ (s ≫ y) m' = pts _ ((pts _).symm (_ * pts _ (tG ≫ φ.toPoint))) m' at this
    rw [pts_comp, Equiv.apply_symm_apply, pts_comp] at this
    exact this
  let c : R := (Scheme.ΓSpecIso R).hom.hom (pts _ φ.toPoint m')
  let e : AddMonoidAlgebra R K := (Scheme.ΓSpecIso _).hom.hom (pts _ y m')
  have key2 : i.hom e = AddMonoidAlgebra.single m 1 * algebraMap R (AddMonoidAlgebra R G) c := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra R G))).hom.hom key
    replace this := this.trans (RingHom.map_mul _ _ _)
    change (Scheme.ΓSpecIso _).hom.hom ((Spec.map i).appTop.hom (pts _ y m')) =
      (Scheme.ΓSpecIso _).hom.hom (uni R G (Multiplicative.ofAdd m)) *
        (Scheme.ΓSpecIso _).hom.hom ((Spec.map (cst R G)).appTop.hom (pts _ φ.toPoint m')) at this
    refine (gam i (pts _ y m')).symm.trans (this.trans ?_)
    exact congrArg₂ (· * ·) (uni_ev R G _) (gam (cst R G) (pts _ φ.toPoint m'))
  have hc : IsUnit c := by
    let m'' : Multiplicative (⊤ : AddSubmonoid G) := Multiplicative.ofAdd ⟨-m, trivial⟩
    have h1 : m' * m'' = 1 := by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (add_neg_cancel m)
    have h0 : (pts _ φ.toPoint) m' * (pts _ φ.toPoint) m'' = 1 :=
      (map_mul (pts _ φ.toPoint) m' m'').symm.trans (by rw [h1, map_one])
    have h2 := (RingHom.map_mul (Scheme.ΓSpecIso R).hom.hom _ _).symm.trans
      ((congrArg (Scheme.ΓSpecIso R).hom.hom h0).trans (RingHom.map_one _))
    exact IsUnit.of_mul_eq_one _ h2
  have h3 := congrArg (fun z : AddMonoidAlgebra R G => z.coeff m) key2
  have h4 : (i.hom e : AddMonoidAlgebra R G).coeff m = 0 := by
    change (AddMonoidAlgebra.mapDomain K.subtype e).coeff m = 0
    rw [AddMonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_notin_range _ _ (by simpa using hm)
  have h5 : (AddMonoidAlgebra.single m 1 * algebraMap R (AddMonoidAlgebra R G) c).coeff m = c := by
    simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.single_mul_single]
  simp only [h4, h5] at h3
  exact hc.ne_zero h3.symm

end Core

/-- **Example 15.10 (ii), core.** `X^K` has no point over a nonempty `T`, for `K ≠ G`. -/
theorem no_point {K : AddSubmonoid G} (hK : K ≠ ⊤) {T : Over S} [Nonempty T.left]
    (φ : AttractorPt (aAction (⊤ : AddSubmonoid G) S) K T) : False := by
  obtain ⟨m, hm⟩ : ∃ m, m ∉ K := by
    by_contra! h
    exact hK (top_le_iff.mp fun x _ => h x)
  obtain ⟨x⟩ := ‹Nonempty T.left›
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := T.left) (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : Nontrivial Γ(T.left, U) := T.left.component_nontrivial U
  let g : Over.mk (hU.fromSpec ≫ T.hom) ⟶ T := Over.homMk hU.fromSpec rfl
  exact no_point_core (CommRingCat.of Γ(T.left, U)) (hU.fromSpec ≫ T.hom) hm (φ.baseChange g)

/-- Over an empty `T`, every point lies in `X^K`. -/
theorem mem_image_of_isEmpty (K : AddSubmonoid G) {T : Over S} [IsEmpty T.left]
    (x : T ⟶ A (⊤ : AddSubmonoid G) S) :
    x ∈ attractorImage (aAction (⊤ : AddSubmonoid G) S) K T := by
  have ext : ∀ {T' : Over S} (_ : T' ⟶ T) (a b : T' ⟶ A (⊤ : AddSubmonoid G) S), a = b := by
    intro T' t a b
    haveI : IsEmpty T'.left := ⟨fun y => isEmptyElim (t.left y)⟩
    exact Over.OverMorphism.ext ((isInitialOfIsEmpty (X := T'.left)).hom_ext _ _)
  exact ⟨⟨fun {T'} t _ => t ≫ x, fun s t a => ext (s ≫ t) _ _,
    fun t h a => ext t _ _⟩, Category.id_comp x⟩

/-- **Example 15.10 (ii)**, `S` any nonempty scheme: for `D(G)_S` acting on itself by multiplication,
`Π(a) = {0, G}`, with `G ≠ 0` a group, e.g. `G = ℤⁿ`, `n ≥ 1`. -/
theorem ex1510_ii [Nontrivial G] [Nonempty S] :
    pureMagnets (attractorImage (aAction (⊤ : AddSubmonoid G) S)) = {⊥, ⊤} := by
  have hne : ∀ K L : AddSubmonoid G, K ≠ ⊤ → L ≠ ⊤ →
      attractorImage (aAction (⊤ : AddSubmonoid G) S) K =
        attractorImage (aAction (⊤ : AddSubmonoid G) S) L := by
    have sub : ∀ K L : AddSubmonoid G, K ≠ ⊤ → ∀ T,
        attractorImage (aAction (⊤ : AddSubmonoid G) S) K T ⊆
          attractorImage (aAction (⊤ : AddSubmonoid G) S) L T := by
      rintro K L hK T x ⟨φ, rfl⟩
      rcases isEmpty_or_nonempty T.left with h | h
      · exact mem_image_of_isEmpty L _
      · exact (no_point hK φ).elim
    intro K L hK hL
    funext T
    exact Set.Subset.antisymm (sub K L hK T) (sub L K hL T)
  have htop : ∀ K : AddSubmonoid G, K ≠ ⊤ →
      attractorImage (aAction (⊤ : AddSubmonoid G) S) ⊤ ≠
        attractorImage (aAction (⊤ : AddSubmonoid G) S) K := by
    intro K hK e
    let T : Over S := Over.mk (𝟙 S)
    haveI : Nonempty T.left := ‹Nonempty S›
    have hx : (pts T).symm 1 ∈ attractorImage (aAction (⊤ : AddSubmonoid G) S) ⊤ T :=
      ⟨(attractorTopEquiv (aAction (⊤ : AddSubmonoid G) S) T).symm ((pts T).symm 1),
        (attractorTopEquiv (aAction (⊤ : AddSubmonoid G) S) T).apply_symm_apply _⟩
    rw [e] at hx
    obtain ⟨φ, -⟩ := hx
    exact no_point hK φ
  have hbt : (⊥ : AddSubmonoid G) ≠ ⊤ := bot_ne_top
  ext N
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hN
    by_cases hNt : N = ⊤
    · exact Or.inr hNt
    · exact Or.inl (le_bot_iff.mp (hN ⊥ (hne N ⊥ hNt hbt)))
  · rintro (rfl | rfl)
    · exact isPure_bot
    · intro K hK
      by_contra hne'
      exact htop K (fun e => hne' (by simp [e])) hK


end AlgMag.Leftover

#print axioms AlgMag.Leftover.ex1510_ii
