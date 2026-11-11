/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsF1Glue

/-!
# X-products of attractors: extension of scalars from `F₁` to `ℤ`, Proposition 3.2

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, §2 and §3.

§2 of the paper defines `X ⊗_{F₁} ℤ` as follows: for `X = spec Q` it is `Spec ℤ[Q]`, "and the general
construction is obtained by gluing these affine pieces". This is `AlgMag.XP.F1.IsF1BaseChange X Y`:
`X` is glued from affines `spec Q_j` along localizations `Q_i ← Q_j`, and `Y` is the colimit of the
diagram of the `Spec ℤ[Q_j]`.

## Main results

* `AlgMag.XP.F1.AffineAtlas`, `AlgMag.XP.F1.IsF1BaseChange`: the construction `X ⊗_{F₁} ℤ` of §2.
* `AlgMag.XP.F1.prop32`: **Proposition 3.2**: `𝒩` is a monoscheme with `𝒩 ⊗_{F₁} ℤ = 𝔸(𝒩)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option linter.unusedSectionVars false

namespace AlgMag.XP.F1

noncomputable section

section Comap

variable {P Q : Type u} [CommMonoid P] [CommMonoid Q] (θ : P →* Q)

/-- The inverse image of a prime under a homomorphism of monoids: `spec Q → spec P` on points. -/
def comap (z : MPrime Q) : MPrime P where
  carrier := θ ⁻¹' z.carrier
  ideal q a h := by
    change θ (q * a) ∈ z.carrier
    rw [map_mul]
    exact z.ideal _ h
  one_notMem h := z.one_notMem (by simpa using h)
  prime {a b} h := z.prime (by simpa [map_mul] using h)

lemma comap_compl {z : MPrime Q} {f : P} (hf : f ∈ (comap θ z).compl) : θ f ∈ z.compl := hf

/-- The stalk map `P_{θ⁻¹ 𝔮} → Q_𝔮`. -/
def locMap (z : specTop Q) : Loc P (show specTop P from comap θ z) →* Loc Q z :=
  (Localization.monoidOf (MPrime.compl (Q := P) (comap θ z))).lift
    (g := ((Localization.monoidOf (MPrime.compl (Q := Q) z)).toMonoidHom).comp θ) fun y =>
      (Localization.monoidOf (MPrime.compl (Q := Q) z)).map_units ⟨θ y.1, comap_compl θ y.2⟩

lemma locMap_mk (z : specTop Q) (a f : P) (hf : f ∈ (comap θ (show MPrime Q from z)).compl) :
    locMap θ z (Localization.mk a ⟨f, hf⟩) = Localization.mk (θ a) ⟨θ f, comap_compl θ hf⟩ := by
  rw [Localization.mk_eq_monoidOf_mk', Localization.mk_eq_monoidOf_mk']
  refine (Submonoid.LocalizationMap.lift_mk'_spec _ _ _ _ _).2 ?_
  exact ((Localization.monoidOf (MPrime.compl (Q := Q) z)).mk'_spec' (θ a)
    ⟨θ f, comap_compl θ hf⟩).symm

end Comap

section Atlas

open GB

lemma AZmap_id (P : Type u) [AddCommMonoid P] : AZmap (AddMonoidHom.id P) = 𝟙 (AZ P) := by
  apply (ptsZ _).injective
  have := ptsZ_AZmap (AddMonoidHom.id P) (𝟙 (AZ P))
  rw [Category.id_comp] at this
  exact this

lemma AZmap_comp {P P' P'' : Type u} [AddCommMonoid P] [AddCommMonoid P'] [AddCommMonoid P'']
    (φ : P →+ P') (ψ : P' →+ P'') : AZmap (ψ.comp φ) = AZmap ψ ≫ AZmap φ := by
  apply (ptsZ _).injective
  have h1 := ptsZ_AZmap (ψ.comp φ) (𝟙 (AZ P''))
  have h2 := ptsZ_AZmap φ (AZmap ψ)
  have h3 := ptsZ_AZmap ψ (𝟙 (AZ P''))
  rw [Category.id_comp] at h1 h3
  rw [h1, h2, h3]
  rfl

/-- `X` glued from affines along localizations: the atlases entering the definition of `X ⊗_{F₁} ℤ` in
§2. The `spec Q_j` are open in `X`, they cover `X`, and their intersections are unions of the
`spec Q_k`, `k → i, j`; the transition maps are the localizations `Q_j → Q_i`, on points and on
sections. -/
structure AffineAtlas (X : MonoidalSpace.{u}) where
  /-- The index category. -/
  J : Type u
  [cat : SmallCategory J]
  /-- The monoids. -/
  Q : Jᵒᵖ ⥤ AddCommMonCat.{u}
  /-- The charts. -/
  a : ∀ j, spec (Multiplicative (Q.obj (op j))) ⟶ X
  isOpen : ∀ j, SheafedSpace.IsOpenImmersion (a j)
  surj : ∀ x : X, ∃ j, ∃ y, (a j).hom.base y = x
  isLoc : ∀ {i j : J} (f : i ⟶ j), ∃ s : Q.obj (op j),
    AddSubmonoid.IsLocalizationMap (AddSubmonoid.multiples s) (Q.map f.op).hom
  compat_pt : ∀ {i j : J} (f : i ⟶ j) (z : MPrime (Multiplicative (Q.obj (op i)))),
    (a j).hom.base (comap (AddMonoidHom.toMultiplicative (Q.map f.op).hom) z) = (a i).hom.base z
  compat_sec : ∀ {i j : J} (f : i ⟶ j) (U : Opens X) (s : X.presheaf.obj (op U))
    (z : MPrime (Multiplicative (Q.obj (op i)))) (hz : (a i).hom.base z ∈ U)
    (hz' : (a j).hom.base (comap (AddMonoidHom.toMultiplicative (Q.map f.op).hom) z) ∈ U),
    (show sections _ ((Opens.map (a i).hom.base).obj U) from (a i).hom.c.app (op U) s).1 ⟨z, hz⟩ =
      locMap (AddMonoidHom.toMultiplicative (Q.map f.op).hom) z
        ((show sections _ ((Opens.map (a j).hom.base).obj U) from (a j).hom.c.app (op U) s).1 ⟨_, hz'⟩)
  overlap : ∀ (i j : J) (y : MPrime (Multiplicative (Q.obj (op i))))
    (y' : MPrime (Multiplicative (Q.obj (op j)))), (a i).hom.base y = (a j).hom.base y' →
    ∃ (k : J) (f : k ⟶ i) (g : k ⟶ j) (z : MPrime (Multiplicative (Q.obj (op k)))),
      comap (AddMonoidHom.toMultiplicative (Q.map f.op).hom) z = y ∧
      comap (AddMonoidHom.toMultiplicative (Q.map g.op).hom) z = y'

attribute [instance] AffineAtlas.cat

/-- The diagram of the schemes `Spec ℤ[Q_j]` of an atlas. -/
def AffineAtlas.diag {X : MonoidalSpace.{u}} (G : AffineAtlas X) : G.J ⥤ Scheme.{u} where
  obj j := AZ (G.Q.obj (op j))
  map {i j} f := AZmap (G.Q.map f.op).hom
  map_id j := by
    rw [← AZmap_id]
    congr 1
    rw [op_id, G.Q.map_id]
    rfl
  map_comp {i j k} f g := by
    rw [← AZmap_comp]
    congr 1
    rw [op_comp, G.Q.map_comp]
    rfl

/-- `Y = X ⊗_{F₁} ℤ` (§2): `Y` is obtained by gluing the affine pieces `Spec ℤ[Q_j]` for an atlas of `X`. -/
def IsF1BaseChange (X : MonoidalSpace.{u}) (Y : Scheme.{u}) : Prop :=
  ∃ (G : AffineAtlas X) (c : Cocone G.diag), Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ Y)

end Atlas

section Family

open GB

variable {M : Type u} [AddCommGroup M] {A : Type u} (𝓝 : MagnetFamily M A)

/-- The submonoid at a vertex of the diagram: `Z` or `N_α`. -/
def vP : WidePushoutShape A → AddSubmonoid M
  | none => 𝓝.Z.toAddSubmonoid
  | some α => 𝓝.N α

lemma vP_le (j : WidePushoutShape A) : vP 𝓝 j ≤ 𝓝.Z.toAddSubmonoid := by
  cases j with
  | none => exact le_rfl
  | some α => exact 𝓝.le α

lemma vP_anti {i j : WidePushoutShape A} (f : i ⟶ j) : vP 𝓝 j ≤ vP 𝓝 i := by
  cases f with
  | id => exact le_rfl
  | init α => exact 𝓝.le α

/-- The monoids of the atlas of `𝒩`. -/
def vQ : (WidePushoutShape A)ᵒᵖ ⥤ AddCommMonCat.{u} where
  obj j := AddCommMonCat.of (vP 𝓝 (unop j))
  map f := AddCommMonCat.ofHom (AddSubmonoid.inclusion (vP_anti 𝓝 f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The chart at a vertex. -/
def vChart : ∀ j : WidePushoutShape A, Chart 𝓝 (vP 𝓝 j) (vP_le 𝓝 j)
  | none => chart₀ 𝓝
  | some α => chartα 𝓝 α

lemma comap_incl_id (j : WidePushoutShape A) (h : vP 𝓝 j ≤ vP 𝓝 j)
    (z : MPrime (Multiplicative (vP 𝓝 j))) :
    comap (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) z = z := by
  refine MPrime.ext ?_
  ext x
  rfl

lemma comap_empty {P P' : AddSubmonoid M} (h : P ≤ P') (z : MPrime (Multiplicative P'))
    (hz : ¬ z.carrier.Nonempty) :
    ¬ (comap (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) z).carrier.Nonempty := by
  rintro ⟨x, hx⟩
  exact hz ⟨_, hx⟩

lemma vChart_compat {i j : WidePushoutShape A} (f : i ⟶ j)
    (z : MPrime (Multiplicative (vP 𝓝 i))) :
    (vChart 𝓝 j).j (comap (AddMonoidHom.toMultiplicative
      (AddSubmonoid.inclusion (vP_anti 𝓝 f))) z) = (vChart 𝓝 i).j z := by
  cases f with
  | id => rw [comap_incl_id]
  | init α =>
    change jα α _ = none
    exact jα_of_empty (comap_empty _ z (not_nonempty_j₀ z))

lemma locToZ_locMap {P P' : AddSubmonoid M} (h : P ≤ P') (hP' : P' ≤ 𝓝.Z.toAddSubmonoid)
    (z : MPrime (Multiplicative P')) (w : Loc (Multiplicative P)
      (show specTop _ from comap (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) z)) :
    locToZ hP' z (locMap (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) z w) =
      locToZ (h.trans hP') _ w := by
  induction w using Localization.induction_on with
  | H y =>
  obtain ⟨a, ⟨f, hf⟩⟩ := y
  have e1 := locMap_mk (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion h)) z a f hf
  refine (congrArg (locToZ hP' z) e1).trans ?_
  refine (locToZ_mk hP' z _ _ _).trans ?_
  exact (locToZ_mk (h.trans hP') _ a f hf).symm

/-- `P → P'` is a localization at `s`, when `P'` is `P` with `s` inverted. -/
lemma isLoc_incl {P P' : AddSubmonoid M} (h : P ≤ P') (s : P) (hL : ∀ z ∈ P', ∃ k : ℕ, z + k • s.1 ∈ P)
    (hn : -s.1 ∈ P') :
    AddSubmonoid.IsLocalizationMap (AddSubmonoid.multiples s) (AddSubmonoid.inclusion h) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    have hs : IsAddUnit (AddSubmonoid.inclusion h s) :=
      IsAddUnit.of_add_eq_zero (⟨-s.1, hn⟩ : P') (Subtype.ext (add_neg_cancel s.1))
    have e : (AddSubmonoid.inclusion h) ((fun k : ℕ => k • s) k) = k • AddSubmonoid.inclusion h s :=
      map_nsmul (AddSubmonoid.inclusion h) k s
    rw [show (AddSubmonoid.inclusion h) ((fun k : ℕ => k • s) k) = _ from e]
    exact hs.nsmul k
  · intro z
    obtain ⟨k, hk⟩ := hL z.1 z.2
    exact ⟨(⟨_, hk⟩, ⟨k • s, k, rfl⟩), Subtype.ext rfl⟩
  · intro x y hxy
    refine ⟨0, ?_⟩
    rw [AddSubmonoid.inclusion_injective h hxy]

variable [Nonempty A]

/-- The atlas of `𝒩`: the charts `spec N_α` and `spec N^gp`. -/
def nAtlas : AffineAtlas (NSpace 𝓝) where
  J := WidePushoutShape A
  Q := vQ 𝓝
  a j := (vChart 𝓝 j).toN
  isOpen j := (vChart 𝓝 j).isOpenImmersion
  surj x := by
    rcases x with _ | ⟨⟨⟨α, p⟩, hp⟩⟩
    · obtain ⟨α⟩ := ‹Nonempty A›
      exact ⟨some α, botPrime _, jα_of_empty fun h => h.elim fun _ hx => hx⟩
    · exact ⟨some α, p, jα_of_nonempty hp⟩
  isLoc {i j} f := by
    cases f with
    | @id j =>
      exact ⟨0, isLoc_incl le_rfl 0 (fun z hz => ⟨0, by simpa using hz⟩) (by simp)⟩
    | init α =>
      obtain ⟨t, ht, hk⟩ := exists_denominator (𝓝.fg α)
      refine ⟨⟨t, ht⟩, isLoc_incl (𝓝.le α) _ (fun z hz => hk z ?_) ?_⟩
      · rw [𝓝.gp α]
        exact hz
      · exact 𝓝.Z.neg_mem (𝓝.le α ht)
  compat_pt f z := vChart_compat 𝓝 f z
  compat_sec {i j} f U s z hz hz' := by
    apply locToZ_injective (vP_le 𝓝 i) z
    refine ((vChart 𝓝 i).locToZ_val s ⟨z, hz⟩).trans ?_
    refine Eq.trans ?_ (locToZ_locMap 𝓝 (vP_anti 𝓝 f) (vP_le 𝓝 i) z _).symm
    refine Eq.trans ?_ ((vChart 𝓝 j).locToZ_val s ⟨_, hz'⟩).symm
    exact congrArg s.1 (Subtype.ext (vChart_compat 𝓝 f z).symm)
  overlap i j y y' h := by
    have hemp₁ : ∀ {P P' : AddSubmonoid M} (hPP : P ≤ P') (w : MPrime (Multiplicative P'))
        (y : MPrime (Multiplicative P)), ¬ w.carrier.Nonempty → ¬ y.carrier.Nonempty →
        comap (AddMonoidHom.toMultiplicative (AddSubmonoid.inclusion hPP)) w = y :=
      fun hPP w y hw hy => carrier_eq_of_empty (comap_empty hPP w hw) hy
    rcases i with _ | α <;> rcases j with _ | β
    · exact ⟨none, 𝟙 _, 𝟙 _, y, comap_incl_id 𝓝 _ le_rfl _,
        (comap_incl_id 𝓝 _ le_rfl _).trans (carrier_eq_of_empty (not_nonempty_j₀ y) (not_nonempty_j₀ y'))⟩
    · have hy' : ¬ y'.carrier.Nonempty := by
        intro hne
        have h' : (none : Pt 𝓝) = jα β y' := h
        rw [jα_of_nonempty hne] at h'
        exact Option.some_ne_none _ h'.symm
      exact ⟨none, 𝟙 _, WidePushoutShape.Hom.init β, y, comap_incl_id 𝓝 _ le_rfl _,
        hemp₁ (𝓝.le β) y y' (not_nonempty_j₀ y) hy'⟩
    · have hy : ¬ y.carrier.Nonempty := by
        intro hne
        have h' : jα α y = (none : Pt 𝓝) := h
        rw [jα_of_nonempty hne] at h'
        exact Option.some_ne_none _ h'
      exact ⟨none, WidePushoutShape.Hom.init α, 𝟙 _, y', hemp₁ (𝓝.le α) y' y (not_nonempty_j₀ y') hy,
        comap_incl_id 𝓝 _ le_rfl _⟩
    · have h' : jα α y = jα β y' := h
      by_cases hαβ : α = β
      · subst hαβ
        have e : y = y' := jα_injective α h'
        subst e
        exact ⟨some α, 𝟙 _, 𝟙 _, y, comap_incl_id 𝓝 _ le_rfl _, comap_incl_id 𝓝 _ le_rfl _⟩
      · have hy : ¬ y.carrier.Nonempty := by
          intro hne
          rw [jα_of_nonempty hne] at h'
          by_cases hne' : y'.carrier.Nonempty
          · rw [jα_of_nonempty hne'] at h'
            exact hαβ (congrArg (fun x => x.1.1) (Option.some.inj h'))
          · rw [jα_of_empty hne'] at h'
            exact Option.some_ne_none _ h'
        have hy' : ¬ y'.carrier.Nonempty := by
          intro hne
          rw [jα_of_empty hy, jα_of_nonempty hne] at h'
          exact Option.some_ne_none _ h'.symm
        have hb : ¬ (botPrime (Multiplicative 𝓝.Z.toAddSubmonoid)).carrier.Nonempty :=
          fun ⟨_, hx⟩ => hx
        exact ⟨none, WidePushoutShape.Hom.init α, WidePushoutShape.Hom.init β, botPrime _,
          hemp₁ (𝓝.le α) _ y hb hy, hemp₁ (𝓝.le β) _ y' hb hy'⟩

/-- The identification of the diagram of `nAtlas` with the diagram of Proposition 3.1. -/
def nDiagIso : 𝓝.diag ≅ (nAtlas 𝓝).diag :=
  NatIso.ofComponents (fun j => by
    cases j with
    | none => exact Iso.refl _
    | some α => exact Iso.refl _) (by
    rintro (_ | α) (_ | β) f
    · cases f
      have e1 := 𝓝.diag.map_id (@none A)
      have e2 := (nAtlas 𝓝).diag.map_id (@none A)
      exact (Category.comp_id _).trans (e1.trans (e2.symm.trans (Category.id_comp _).symm))
    · cases f
      change 𝓝.gpMap β ≫ 𝟙 _ = 𝟙 _ ≫ AZmap (AddSubmonoid.inclusion (𝓝.le β))
      simp [MagnetFamily.gpMap]
    · cases f
    · cases f
      have e1 := 𝓝.diag.map_id (some α)
      have e2 := (nAtlas 𝓝).diag.map_id (some α)
      exact (Category.comp_id _).trans (e1.trans (e2.symm.trans (Category.id_comp _).symm)))

/-- **Proposition 3.2**: there exists a scheme over `F₁`, `𝒩`, such that `𝒩 ⊗_{F₁} ℤ = 𝔸(𝒩)`. -/
theorem prop32 : IsMonoscheme (NSpace 𝓝) ∧ IsF1BaseChange (NSpace 𝓝) 𝓝.AN := by
  have h0 : @HasColimit (nAtlas 𝓝).J (nAtlas 𝓝).cat Scheme.{u} _ 𝓝.diag := 𝓝.prop31
  have h1 : HasColimit (nAtlas 𝓝).diag := hasColimit_of_iso (nDiagIso 𝓝).symm
  exact ⟨isMonoscheme_NSpace, nAtlas 𝓝, colimit.cocone _, ⟨colimit.isColimit _⟩,
    ⟨(@HasColimit.isoOfNatIso (nAtlas 𝓝).J (nAtlas 𝓝).cat Scheme.{u} _ 𝓝.diag (nAtlas 𝓝).diag h0 h1
      (nDiagIso 𝓝)).symm⟩⟩

end Family

end

end AlgMag.XP.F1

#print axioms AlgMag.XP.F1.prop32
