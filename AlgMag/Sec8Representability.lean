/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Finsupp.Encodable
import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEffectiveDescent
import AlgMag.GeneralBase
import AlgMag.GeneralBaseCor
import AlgMag.Sec2Monoids
import AlgMag.Sec4Limits
import AlgMag.Sec6FPR

/-!
# Representability of attractors

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §8.

## Main results

* `AlgMag.prop81FG`: **Proposition 8.1** for `M` finitely generated (`AlgMag.Prop81StatementFG`).
* `AlgMag.prop81FG_of_scheme`: **Theorem 8.3 (vii)** for a subgroup: `X` a scheme gives `X^Z` a scheme.
* `AlgMag.attractorFixedEquivOfCover`, `AlgMag.extSieve_mem`: **Proposition 3.35** for a sheaf:
  `D(M) → D(Z)` is an fppf cover for `M` finitely generated, whence `X^Z(T) ≃ X^{D(M/Z)}(T)`.
* `AlgMag.overAct`: the action of `D(M)` on a stable open of the chart, extended from the site to all
  schemes over `S`, since `D(M)_V` belongs to the site.
* `AlgMag.exists_closed_fixed`: the fixed locus of the chart `U`, a disjoint union of stable
  `S`-affine opens, is a closed subscheme (Corollary 3.22, Theorem 3.20 for the pieces).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u v

namespace AlgMag

section General

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommGroup M] {F : Cᵒᵖ ⥤ Type u}

/-- A point of `D(M)` is trivial on `Z`: it is a point of `D(M/Z) ⊆ D(M)`. -/
def TrivialOn (Z : AddSubgroup M) {T : Cᵒᵖ} (h : APt 𝒪 M T) : Prop :=
  APt.toMagnet Z.toAddSubmonoid h = 1

/-- The points of `D(M)` trivial on `Z` are exactly those of `D(M/Z)`. -/
lemma exists_quotient_of_trivialOn {Z : AddSubgroup M} {T : Cᵒᵖ} {h : APt 𝒪 M T}
    (hh : TrivialOn Z h) : ∃ k : APt 𝒪 (M ⧸ Z) T,
      k.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z)) = h := by
  have hz : ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := fun z hz => by
    have := DFunLike.congr_fun hh (Multiplicative.ofAdd (⟨z, hz⟩ : Z.toAddSubmonoid))
    simpa using this
  let f : M →+ Additive (𝒪.obj T) :=
    { toFun := fun m => Additive.ofMul (h (Multiplicative.ofAdd m))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add] }
  let g : M ⧸ Z →+ Additive (𝒪.obj T) := QuotientAddGroup.lift Z f fun z hzz => by
    change Additive.ofMul (h (Multiplicative.ofAdd z)) = 0
    rw [hz z hzz]; rfl
  refine ⟨{ toFun := fun m => Additive.toMul (g (Multiplicative.toAdd m))
            map_one' := by simp
            map_mul' := fun a b => by simp }, ?_⟩
  exact MonoidHom.ext fun m => rfl

/-- Pointwise form of `x ∈ X^{D(M/Z)}`: `x` is fixed by the points of `D(M)` trivial on `Z`. -/
lemma mem_fixedPoints_quotient_iff {act : AAction 𝒪 M F} {Z : AddSubgroup M} {T : Cᵒᵖ}
    {x : F.obj T} : x ∈ (fixedPoints (quotientAction act Z)).obj T ↔
      ∀ {T' : Cᵒᵖ} (s : T ⟶ T') (h : APt 𝒪 M T'), TrivialOn Z h →
        act.smul h (F.map s x) = F.map s x := by
  constructor
  · intro hx T' s h hh
    obtain ⟨k, rfl⟩ := exists_quotient_of_trivialOn hh
    exact hx s k
  · intro hx T' s k
    refine hx s _ ?_
    refine MonoidHom.ext fun n => ?_
    have hn : QuotientAddGroup.mk' Z ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (Multiplicative.toAdd n).2
    change k (Multiplicative.ofAdd (QuotientAddGroup.mk' Z ((Multiplicative.toAdd n :
      Z.toAddSubmonoid) : M))) = 1
    rw [hn]
    exact map_one k

variable (𝒪) in
/-- The sieve of `T` of the morphisms along which `a ∈ D(Z)(T)` extends to a point of `D(M)`. -/
def extSieve (Z : AddSubgroup M) {T : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)) : Sieve T where
  arrows {W} s := ∃ h : APt 𝒪 M (op W), APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a
  downward_closed {W W' s} := by
    rintro ⟨h, hh⟩ g
    refine ⟨APt.res g.op h, ?_⟩
    rw [APt.toMagnet_res, hh, op_comp, APt.res_comp]

lemma trivialOn_div {Z : AddSubgroup M} {T : Cᵒᵖ} {h h' : APt 𝒪 M T}
    (e : APt.toMagnet Z.toAddSubmonoid h = APt.toMagnet Z.toAddSubmonoid h') :
    ∃ k : APt 𝒪 M T, TrivialOn Z k ∧ h = k * h' := by
  refine ⟨h * h'.comp (invMonoidHom (α := Multiplicative M)), ?_, ?_⟩
  · refine MonoidHom.ext fun n => ?_
    have e' := DFunLike.congr_fun e n
    change h (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M)) =
      h' (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M)) at e'
    change h (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M)) *
      h' (Multiplicative.ofAdd ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M))⁻¹ = 1
    rw [e', ← map_mul, mul_inv_cancel, map_one]
  · refine MonoidHom.ext fun m => ?_
    change h m = h m * h' m⁻¹ * h' m
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

section Glue

variable {J : GrothendieckTopology C} {act : AAction 𝒪 M F} {Z : AddSubgroup M}

/-- A fixed point is moved in the same way by all extensions of a point of `D(Z)`. -/
lemma smul_eq_of_fixed {T : C} {x : F.obj (op T)}
    (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T)) {T' : C} (t : T' ⟶ T)
    {h h' : APt 𝒪 M (op T')}
    (e : APt.toMagnet Z.toAddSubmonoid h = APt.toMagnet Z.toAddSubmonoid h') :
    act.smul h (F.map t.op x) = act.smul h' (F.map t.op x) := by
  obtain ⟨k, hk, rfl⟩ := trivialOn_div e
  rw [mul_comm k h', act.mul_smul, mem_fixedPoints_quotient_iff.mp hx t.op k hk]

/-- The value of the attractor point attached to a fixed point `x`, at `a ∈ D(Z)(T')`. -/
theorem existsUnique_glue (hF : Presieve.IsSheaf J F)
    (hcov : ∀ {T : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)), extSieve 𝒪 Z a ∈ J T)
    {T : C} {x : F.obj (op T)} (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T))
    {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')) :
    ∃! y : F.obj (op T'), ∀ {T'' : C} (s : T'' ⟶ T') (h : APt 𝒪 M (op T'')),
      APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
        F.map s.op y = act.smul h (F.map (s ≫ t).op x) := by
  have sh := hF _ (hcov a)
  let fam : Presieve.FamilyOfElements F (extSieve 𝒪 Z a).arrows := fun _ s hs =>
    act.smul hs.choose (F.map (s ≫ t).op x)
  have hc : fam.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ comm
    change F.map g₁.op (act.smul _ _) = F.map g₂.op (act.smul _ _)
    rw [act.map_smul, act.map_smul, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
    have e1 : g₁ ≫ f₁ ≫ t = g₂ ≫ f₂ ≫ t := by
      rw [← Category.assoc, comm, Category.assoc]
    rw [e1]
    apply smul_eq_of_fixed hx
    rw [APt.toMagnet_res, APt.toMagnet_res, h₁.choose_spec, h₂.choose_spec, ← APt.res_comp,
      ← APt.res_comp, ← op_comp, ← op_comp, comm]
  have key : ∀ {T'' : C} (s : T'' ⟶ T') (hs : (extSieve 𝒪 Z a).arrows s)
      (h : APt 𝒪 M (op T'')), APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
        fam s hs = act.smul h (F.map (s ≫ t).op x) := by
    intro T'' s hs h e
    exact smul_eq_of_fixed hx _ (hs.choose_spec.trans e.symm)
  refine ⟨sh.amalgamate fam hc, ?_, ?_⟩
  · intro T'' s h e
    rw [show F.map s.op (sh.amalgamate fam hc) = fam s ⟨h, e⟩ from sh.valid_glue hc s ⟨h, e⟩]
    exact key s ⟨h, e⟩ h e
  · intro y hy
    refine sh.isSeparatedFor.ext fun Y s hs => ?_
    rw [show F.map s.op (sh.amalgamate fam hc) = fam s hs from sh.valid_glue hc s hs]
    exact hy s hs.choose hs.choose_spec

/-- A point of `X^Z` is computed from its underlying point. -/
lemma AttractorPt.app_eq_smul_toPoint {T : C} (φ : AttractorPt act Z.toAddSubmonoid T)
    {T' : C} (t : T' ⟶ T) (h : APt 𝒪 M (op T')) :
    φ.app t (APt.toMagnet Z.toAddSubmonoid h) = act.smul h (F.map t.op φ.toPoint) := by
  have e := φ.equivariant t h 1
  rw [mul_one] at e
  rw [e]
  congr 1
  have hnat := φ.naturality t (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := Z.toAddSubmonoid) t.op 1 = 1 := by
    ext p; simp
  rw [Category.comp_id, hone] at hnat
  exact hnat

/-- The attractor point attached to a fixed point. -/
noncomputable def attOfFixed (hF : Presieve.IsSheaf J F)
    (hcov : ∀ {T : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)), extSieve 𝒪 Z a ∈ J T) {T : C}
    {x : F.obj (op T)} (hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T)) :
    AttractorPt act Z.toAddSubmonoid T where
  app t a := (existsUnique_glue hF hcov hx t a).choose
  naturality := by
    intro T' T'' s t a
    refine (existsUnique_glue hF hcov hx (s ≫ t) (APt.res s.op a)).unique
      (existsUnique_glue hF hcov hx (s ≫ t) (APt.res s.op a)).choose_spec.1 ?_
    intro W r h e
    rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc]
    refine (existsUnique_glue hF hcov hx t a).choose_spec.1 (r ≫ s) h ?_
    rw [e, ← APt.res_comp, ← op_comp]
  equivariant := by
    intro T' t h a
    refine (existsUnique_glue hF hcov hx t _).unique
      (existsUnique_glue hF hcov hx t _).choose_spec.1 ?_
    intro W r k e
    have sh := hF _ (J.pullback_stable r (hcov a))
    refine sh.isSeparatedFor.ext fun W' q hq => ?_
    obtain ⟨b, hb⟩ := hq
    have hb' : APt.toMagnet Z.toAddSubmonoid b = APt.res (q ≫ r).op a := hb
    have hg := (existsUnique_glue hF hcov hx t a).choose_spec.1 (q ≫ r) b hb'
    rw [act.map_smul, act.map_smul, ← Functor.map_comp_apply (f := r.op), ← op_comp, hg,
      ← act.mul_smul, act.map_smul, ← Functor.map_comp_apply, ← op_comp, Category.assoc]
    have hA : q ≫ r ≫ t = (q ≫ r) ≫ t := by simp
    rw [hA]
    refine smul_eq_of_fixed hx _ ?_
    rw [APt.toMagnet_res, e, ← APt.res_comp, ← op_comp]
    refine MonoidHom.ext fun n => ?_
    have := DFunLike.congr_fun hb' n
    simp only [APt.res_apply, MonoidHom.mul_apply, map_mul, APt.toMagnet_apply] at this ⊢
    rw [this]
    simp only [op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **Proposition 3.35**, for a sheaf `F`, on a site where every point of `D(Z)` extends locally to
a point of `D(M)`: the underlying point is a bijection `X^Z(T) ≃ X^{D(M/Z)}(T)`. -/
noncomputable def attractorFixedEquivOfCover (hF : Presieve.IsSheaf J F)
    (hcov : ∀ {T : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)), extSieve 𝒪 Z a ∈ J T) (T : C) :
    (fixedPoints (quotientAction act Z)).obj (op T) ≃ AttractorPt act Z.toAddSubmonoid T where
  toFun x := attOfFixed hF hcov x.2
  invFun φ := ⟨φ.toPoint, φ.toPoint_mem_fixedPoints⟩
  left_inv x := by
    refine Subtype.ext ?_
    have h := (existsUnique_glue hF hcov x.2 (𝟙 T) 1).choose_spec.1 (𝟙 T) 1 (by
      ext p; simp [APt.toMagnet])
    have e : F.map (𝟙 T).op (attOfFixed hF hcov x.2).toPoint = _ := h
    simpa [act.one_smul] using e
  right_inv φ := by
    have key : ∀ {T' : C} (t : T' ⟶ T) (a : APt 𝒪 Z.toAddSubmonoid (op T')),
        (attOfFixed hF hcov (act := act) (Z := Z) φ.toPoint_mem_fixedPoints).app t a =
          φ.app t a := by
      intro T' t a
      refine ((existsUnique_glue hF hcov φ.toPoint_mem_fixedPoints t a).unique
        (existsUnique_glue hF hcov φ.toPoint_mem_fixedPoints t a).choose_spec.1 ?_)
      intro W s h e
      rw [← φ.naturality, ← e, AttractorPt.app_eq_smul_toPoint]
    refine AttractorPt.ext ?_
    funext T' t a
    exact key t a

/-- The bijection of **Proposition 3.35** is natural. -/
lemma attractorFixedEquivOfCover_naturality (hF : Presieve.IsSheaf J F)
    (hcov : ∀ {T : C} (a : APt 𝒪 Z.toAddSubmonoid (op T)), extSieve 𝒪 Z a ∈ J T) {T T' : C}
    (s : T' ⟶ T) (x : (fixedPoints (quotientAction act Z)).toFunctor.obj (op T)) :
    attractorFixedEquivOfCover (act := act) hF hcov T'
        ((fixedPoints (quotientAction act Z)).toFunctor.map s.op x) =
      (attractorFixedEquivOfCover hF hcov T x).baseChange s := by
  apply (attractorFixedEquivOfCover (act := act) hF hcov T').symm.injective
  refine (Equiv.symm_apply_apply _ _).trans (Subtype.ext ?_)
  change F.map s.op x.1 = ((attractorFixedEquivOfCover hF hcov T x).baseChange s).toPoint
  have h1 : ((attractorFixedEquivOfCover (act := act) hF hcov T x)).toPoint = x.1 :=
    congrArg Subtype.val ((attractorFixedEquivOfCover (act := act) hF hcov T).symm_apply_apply x)
  have hnat := (attractorFixedEquivOfCover (act := act) hF hcov T x).naturality s (𝟙 T) 1
  have hone : APt.res (𝒪 := 𝒪) (P := Z.toAddSubmonoid) s.op 1 = 1 := by
    ext p; simp
  rw [hone, Category.comp_id] at hnat
  change _ = AttractorPt.app (attractorFixedEquivOfCover (act := act) hF hcov T x) (𝟙 T' ≫ s) 1
  rw [Category.id_comp, hnat, ← h1]
  rfl

end Glue

end General

section Ring

variable {M : Type*} [AddCommGroup M] (Z : AddSubgroup M) (R : Type*) [CommRing R]

/-- A subgroup acts freely on the group: cosets have representatives. -/
theorem isFreeAlong_subtype : IsFreeAlong (Z.toAddSubmonoid.subtype) := by
  refine ⟨Set.range fun q : M ⧸ Z => q.out, ?_, ?_⟩
  · rintro ⟨z, ⟨_, q, rfl⟩⟩ ⟨z', ⟨_, q', rfl⟩⟩ h
    have h' : (z : M) + q.out = z' + q'.out := h
    have hq : q = q' := by
      have := congrArg (QuotientAddGroup.mk' Z) h'
      simpa [map_add, (QuotientAddGroup.eq_zero_iff (z : M)).2 z.2,
        (QuotientAddGroup.eq_zero_iff (z' : M)).2 z'.2] using this
    subst hq
    have hz : z = z' := Subtype.ext (add_right_cancel h')
    subst hz
    rfl
  · intro m
    refine ⟨⟨⟨m - (m : M ⧸ Z).out, ?_⟩, ⟨_, (m : M ⧸ Z), rfl⟩⟩, by simp⟩
    refine (QuotientAddGroup.eq_zero_iff _).1 ?_
    simp

/-- The coefficients on `Z`, a retraction of `R[Z] → R[M]` as `R[Z]`-modules. -/
noncomputable def resZ : AddMonoidAlgebra R M →+ AddMonoidAlgebra R Z.toAddSubmonoid where
  toFun b := .ofCoeff (Finsupp.comapDomain Z.toAddSubmonoid.subtype b.coeff
    Subtype.val_injective.injOn)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

lemma resZ_coeff (b : AddMonoidAlgebra R M) (z : Z.toAddSubmonoid) :
    (resZ Z R b).coeff z = b.coeff (z : M) := rfl

lemma resZ_mapDomain (a : AddMonoidAlgebra R Z.toAddSubmonoid) :
    resZ Z R (AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype a) = a := by
  ext z
  rw [resZ_coeff]
  exact Finsupp.mapDomain_apply Subtype.val_injective a.coeff z

lemma resZ_mul (a : AddMonoidAlgebra R Z.toAddSubmonoid) (b : AddMonoidAlgebra R M) :
    resZ Z R (AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype a * b) =
      a * resZ Z R b := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_mul, hx, hy]
  | single z d =>
    ext w
    obtain ⟨w', rfl⟩ : ∃ w', w = z + w' := ⟨⟨-(z : M) + w, Z.add_mem (Z.neg_mem z.2) w.2⟩, Subtype.ext (by simp)⟩
    have hmd : AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype
        (AddMonoidAlgebra.single z d) = AddMonoidAlgebra.single (z : M) d := by
      simp [AddMonoidAlgebra.mapDomain_single]
    rw [resZ_coeff, hmd, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := (w' : M))
        (H := fun m' _ => by simp),
      AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (m₂ := w')
        (H := fun m' _ => ⟨fun h => Subtype.ext (add_left_cancel (congrArg Subtype.val h)),
          fun h => by rw [h]⟩), resZ_coeff]

/-- `Spec R[M] → Spec R[Z]` is surjective. -/
theorem comap_mapDomain_surjective :
    Function.Surjective (PrimeSpectrum.comap
      (AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype)) := by
  intro p
  have := p.2
  obtain ⟨Q, hQ, hQp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime
    (f := AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype) p.asIdeal).1 (by
      refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
      rw [Ideal.mem_comap] at hx
      have key : ∀ y ∈ Ideal.map (AddMonoidAlgebra.mapDomainRingHom R Z.toAddSubmonoid.subtype)
          p.asIdeal, ∀ b, resZ Z R (b * y) ∈ p.asIdeal := by
        intro y hy
        refine Submodule.span_induction (p := fun y _ => ∀ b, resZ Z R (b * y) ∈ p.asIdeal)
          ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨c, hc, rfl⟩ b
          rw [mul_comm, resZ_mul]
          exact p.asIdeal.mul_mem_right _ hc
        · intro b; simp
        · intro y y' _ _ hy hy' b
          rw [mul_add, map_add]
          exact p.asIdeal.add_mem (hy b) (hy' b)
        · intro c y _ hy b
          rw [smul_eq_mul, ← mul_assoc]
          exact hy _
      have := key _ hx 1
      rw [one_mul] at this
      rwa [resZ_mapDomain] at this)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

end Ring

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [AddGroup.FG M]

local notation "SCH" => BigFppfOver.toScheme B S hS

instance instFGZ (Z : AddSubgroup M) : AddMonoid.FG Z.toAddSubmonoid := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hfg : (AddSubgroup.toIntSubmodule Z).FG := IsNoetherian.noetherian _
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule Z) := Module.Finite.iff_fg.mpr hfg
  have h2 : AddGroup.FG (AddSubgroup.toIntSubmodule Z) := Module.Finite.iff_addGroup_fg.mp this
  have h3 : AddMonoid.FG (AddSubgroup.toIntSubmodule Z) := AddGroup.fg_iff_addMonoid_fg.mp h2
  exact h3

instance instFGM : AddMonoid.FG M := AddGroup.fg_iff_addMonoid_fg.mp inferInstance

lemma finitePresentation_subtype (Z : AddSubgroup M) :
    (AddMonoidAlgebra.mapDomainRingHom ℤ Z.toAddSubmonoid.subtype).FinitePresentation := by
  refine RingHom.FinitePresentation.of_comp_finiteType
    (algebraMap ℤ (AddMonoidAlgebra ℤ Z.toAddSubmonoid)) ?_ ?_
  · have : (AddMonoidAlgebra.mapDomainRingHom ℤ Z.toAddSubmonoid.subtype).comp
        (algebraMap ℤ (AddMonoidAlgebra ℤ Z.toAddSubmonoid)) =
          algebraMap ℤ (AddMonoidAlgebra ℤ M) := RingHom.ext_int _ _
    rw [this, RingHom.finitePresentation_algebraMap]
    exact finitePresentation ℤ M
  · rw [RingHom.finiteType_algebraMap]
    infer_instance

lemma contains_AZ (hS : B.Contains S) : B.Contains (GB.AZ M) := by
  have : Countable M := by
    have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ M
    exact hf.countable
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS ?_
  have hc : Countable (AddMonoidAlgebra ℤ M) := AddMonoidAlgebra.coeff_injective.countable
  refine (Cardinal.mk_le_aleph0 (α := AddMonoidAlgebra ℤ M)).trans ?_
  exact (Scheme.aleph0_le_size S).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)

/-- **Every point of `D(Z)` extends fppf locally to a point of `D(M)`**: `D(M) → D(Z)` is surjective,
flat and of finite presentation, for `M` finitely generated. -/
theorem extSieve_mem (Z : AddSubgroup M) {T : BigFppfOver B S hS}
    (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) :
    extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T := by
  let φ := Z.toAddSubmonoid.subtype
  let f : (SCH).obj T ⟶ GB.AZ Z.toAddSubmonoid := (GB.ptsZ _).symm a
  let W : Scheme.{u} := pullback f (GB.AZmap φ)
  have hW : B.Contains W := lt_of_le_of_lt (Scheme.size_pullback_le _ _)
    (max_lt T.left.2 (contains_AZ hS))
  let T'' : BigFppfOver B S hS := siteObject B S hS hW (pullback.fst f (GB.AZmap φ) ≫ structMap T)
  let q : T'' ⟶ T := Over.homMk (ObjectProperty.homMk (pullback.fst f (GB.AZmap φ))) rfl
  have hfl : Flat (GB.AZmap φ) := GB.flat_AZmap φ (flat_of_isFreeAlong ℤ (isFreeAlong_subtype Z))
  have hlf : LocallyOfFinitePresentation (GB.AZmap φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (finitePresentation_subtype Z)
  have hsu : Surjective (GB.AZmap φ) := ⟨comap_mapDomain_surjective Z ℤ⟩
  have hqf : Flat ((SCH).map q) := inferInstanceAs (Flat (pullback.fst f (GB.AZmap φ)))
  have hqp : LocallyOfFinitePresentation ((SCH).map q) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst f (GB.AZmap φ)))
  have hqs : Surjective ((SCH).map q) := inferInstanceAs (Surjective (pullback.fst f (GB.AZmap φ)))
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS q hqs hqf hqp)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  refine ⟨GB.ptsZ _ (pullback.snd f (GB.AZmap φ)), ?_⟩
  have e := GB.ptsZ_AZmap φ (pullback.snd f (GB.AZmap φ))
  rw [← pullback.condition, GB.ptsZ_comp] at e
  have hf : GB.ptsZ _ f = a := (GB.ptsZ _).apply_symm_apply a
  rw [hf] at e
  exact e.symm

end Site

namespace MonAff

variable {P : Type u} [AddCommMonoid P] {T : Scheme.{u}}

/-- Pull back a point of `𝔸(P)` along a morphism of schemes. -/
def pull {X Y : Scheme.{u}} (k : X ⟶ Y) (a : Multiplicative P →* Γ(Y, ⊤)) :
    Multiplicative P →* Γ(X, ⊤) :=
  (k.appTop.hom : Γ(Y, ⊤) →+* Γ(X, ⊤)).toMonoidHom.comp a

lemma comp_homOf {X Y : Scheme.{u}} (k : X ⟶ Y) (f : Y ⟶ T) (a : Multiplicative P →* Γ(Y, ⊤)) :
    k ≫ homOf f a = homOf (k ≫ f) (pull k a) := by
  refine hom_ext' ?_ fun p => ?_
  · simp
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOf_coord, homOf_coord]
    rfl

lemma pull_comp {X Y W : Scheme.{u}} (k : X ⟶ Y) (l : Y ⟶ W) (a : Multiplicative P →* Γ(W, ⊤)) :
    pull (k ≫ l) a = pull k (pull l a) := by
  refine MonoidHom.ext fun p => ?_
  change (k ≫ l).appTop (a p) = k.appTop (l.appTop (a p))
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

lemma homOf_one_comp {X Y : Scheme.{u}} (k : X ⟶ Y) :
    (homOf k 1 : X ⟶ MonAff P Y) = k ≫ homOf (𝟙 Y) 1 := by
  rw [comp_homOf, Category.comp_id]
  congr 1
  exact MonoidHom.ext fun p => by simp [pull]

lemma pull_of_comp_eq {X Y W : Scheme.{u}} {k : X ⟶ Y} {l : Y ⟶ W} {r : X ⟶ W} (e : k ≫ l = r)
    (a : Multiplicative P →* Γ(W, ⊤)) : pull k (pull l a) = pull r a := by
  subst e
  exact (pull_comp k l a).symm

lemma pull_homOf_coord {X : Scheme.{u}} (f : X ⟶ T) (a : Multiplicative P →* Γ(X, ⊤)) :
    pull (homOf f a) (coord P T) = a :=
  MonoidHom.ext fun p => homOf_coord f a p

lemma comp_appTop_homOf {X Y : Scheme.{u}} (k : X ⟶ Y) (f : Y ⟶ T)
    (a : Multiplicative P →* Γ(Y, ⊤)) : pull (k ≫ homOf f a) (coord P T) = pull k a := by
  refine MonoidHom.ext fun p => ?_
  change (k ≫ homOf f a).appTop (coord P T p) = k.appTop (a p)
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOf_coord]

end MonAff

section OverAction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (hM : B.Contains (Spec (ZMon M))) {U : BigFppfOver B S hS}
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}

/-- The stable open `V` as an object of the site. -/
noncomputable def openObj (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    BigFppfOver B S hS :=
  siteObject B S hS (Scheme.size_lt_of_isOpenImmersion V.ι U.left.2) (V.ι ≫ structMap U)

/-- The inclusion of the stable open. -/
noncomputable def openJ (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openObj V ⟶ U :=
  Over.homMk (ObjectProperty.homMk V.ι) rfl

/-- The inclusion of the stable open, as a morphism of schemes. -/
noncomputable abbrev iV (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).obj (openObj V) ⟶ (BigFppfOver.toScheme B S hS).obj U :=
  (BigFppfOver.toScheme B S hS).map (openJ V)

instance (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : IsOpenImmersion (iV V) :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- The classifying morphism of a point of `D(M)`. -/
noncomputable def lft {T T' : BigFppfOver B S hS} (t : T' ⟶ T)
    (a : APt (fppfO B S hS) M (op T')) : T' ⟶ monAffObj M hM T :=
  Over.homMk (ObjectProperty.homMk (MonAff.homOf ((SCH).map t) a)) (by
    apply B.inclusion.map_injective
    have hw : (SCH).map t ≫ structMap T = structMap T' := congrArg (B.inclusion.map) (Over.w t)
    refine Eq.trans ?_ hw
    refine Eq.trans ?_ (MonAff.homOf_π_assoc _ a (structMap T))
    rfl)

/-- The projection `D(M)_T → T`. -/
noncomputable def prj (T : BigFppfOver B S hS) : monAffObj M hM T ⟶ T :=
  Over.homMk (ObjectProperty.homMk (MonAff.π M _)) rfl

/-- The universal point of `D(M)` over `D(M)_T`. -/
noncomputable def cor (T : BigFppfOver B S hS) : APt (fppfO B S hS) M (op (monAffObj M hM T)) :=
  MonAff.coord M _

lemma lft_prj {T T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS) M (op T')) :
    lft hM t a ≫ prj hM T = t := by
  apply (SCH).map_injective
  rw [Functor.map_comp]
  exact MonAff.homOf_π _ _

lemma res_lft {T T' : BigFppfOver B S hS} (t : T' ⟶ T) (a : APt (fppfO B S hS) M (op T')) :
    APt.res (lft hM t a).op (cor hM T) = a :=
  MonoidHom.ext fun p => MonAff.homOf_coord _ _ _

/-- The action on points of the representable presheaf `U`, with explicit source. -/
def smulS (actU : AAction (fppfO B S hS) M (yoneda.obj U)) {T : BigFppfOver B S hS}
    (h : APt (fppfO B S hS) M (op T)) (t : T ⟶ U) : T ⟶ U :=
  actU.smul (U := op T) h t

lemma smulS_one {T : BigFppfOver B S hS} (t : T ⟶ U) : smulS actU 1 t = t :=
  actU.one_smul (U := op T) t

lemma smulS_mul {T : BigFppfOver B S hS} (g h : APt (fppfO B S hS) M (op T)) (t : T ⟶ U) :
    smulS actU (g * h) t = smulS actU g (smulS actU h t) :=
  actU.mul_smul (U := op T) g h t

lemma comp_smulS {T T' : BigFppfOver B S hS} (k : T' ⟶ T) (h : APt (fppfO B S hS) M (op T))
    (t : T ⟶ U) : k ≫ smulS actU h t = smulS actU (APt.res k.op h) (k ≫ t) :=
  actU.map_smul (U := op T) (V := op T') k.op h t

/-- A point of `D(M)` on an object of the site, as a map to its global sections. -/
abbrev ptS {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T)) :
    Multiplicative M →* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := h

/-- The acted point on `D(M)_V` stays in `V`. -/
lemma range_smul_cor (hst : IsStableOpen actU V) :
    Set.range ((SCH).map (smulS actU (cor hM (openObj V)) (prj hM (openObj V) ≫ openJ V))) ⊆
      Set.range (iV V) := by
  have hr : Set.range (iV V) = (V : Set _) := Scheme.Opens.range_ι V
  rw [hr]
  refine hst (prj hM (openObj V) ≫ openJ V) (cor hM (openObj V)) ?_
  rintro _ ⟨y, rfl⟩
  have : (SCH).map (prj hM (openObj V) ≫ openJ V) y =
      (iV V) ((SCH).map (prj hM (openObj V)) y) := by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
  rw [this]
  exact ((SCH).map (prj hM (openObj V)) y).2

/-- The action morphism `D(M)_V → V`. -/
noncomputable def actMorS (hst : IsStableOpen actU V) :
    MonAff M ((SCH).obj (openObj V)) ⟶ (SCH).obj (openObj V) :=
  IsOpenImmersion.lift (iV V) _ (range_smul_cor hM hst)

lemma actMorS_ι (hst : IsStableOpen actU V) :
    actMorS hM hst ≫ iV V =
      (SCH).map (smulS actU (cor hM (openObj V)) (prj hM (openObj V) ≫ openJ V)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- A value of the action from the action morphism. -/
lemma smul_eq_actMor (hst : IsStableOpen actU V) {T : BigFppfOver B S hS}
    (t : T ⟶ openObj V) (h : APt (fppfO B S hS) M (op T)) :
    (SCH).map (smulS actU h (t ≫ openJ V)) =
      MonAff.homOf ((SCH).map t) (ptS h) ≫ actMorS hM hst ≫ iV V := by
  have e' : lft hM t h ≫ smulS actU (cor hM (openObj V)) (prj hM (openObj V) ≫ openJ V) =
      smulS actU h (t ≫ openJ V) := by
    rw [comp_smulS, res_lft, ← Category.assoc, lft_prj]
  rw [← e', Functor.map_comp]
  exact congrArg (fun k => MonAff.homOf ((SCH).map t) (ptS h) ≫ k) (actMorS_ι hM hst).symm

lemma homOf_id_one (hst : IsStableOpen actU V) :
    MonAff.homOf (𝟙 ((SCH).obj (openObj V))) 1 ≫ actMorS hM hst = 𝟙 ((SCH).obj (openObj V)) := by
  have h0 := smul_eq_actMor hM hst (𝟙 (openObj V)) 1
  have e1 : (SCH).map (smulS actU 1 (𝟙 (openObj V) ≫ openJ V)) = iV V := by
    rw [smulS_one, Category.id_comp]
  rw [e1, CategoryTheory.Functor.map_id] at h0
  apply (cancel_mono (iV V)).1
  exact (Category.assoc _ _ _).trans (h0.symm.trans (Category.id_comp _).symm)

lemma actMorS_w (hst : IsStableOpen actU V) :
    actMorS hM hst ≫ iV V ≫ structMap U = MonAff.π M _ ≫ iV V ≫ structMap U := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ structMap U) (actMorS_ι hM hst)).trans ?_
  have h1 : (SCH).map (smulS actU (cor hM (openObj V)) (prj hM (openObj V) ≫ openJ V)) ≫
      structMap U = structMap (monAffObj M hM (openObj V)) :=
    congrArg (B.inclusion.map) (Over.w _)
  exact h1

lemma actMorS_assoc (hst : IsStableOpen actU V) {T : Scheme.{u}} (x : T ⟶ ((SCH).obj (openObj V)))
    (g h : Multiplicative M →* Γ(T, ⊤)) :
    MonAff.homOf (MonAff.homOf x h ≫ actMorS hM hst) g ≫ actMorS hM hst =
      MonAff.homOf x (g * h) ≫ actMorS hM hst := by
  let O := openObj V
  let P₁ := monAffObj M hM O
  let P₂ := monAffObj M hM P₁
  let m : P₁ ⟶ O := Over.homMk (ObjectProperty.homMk (actMorS hM hst)) (by
    apply B.inclusion.map_injective
    exact (actMorS_w hM hst).trans (by rfl))
  have hm : (SCH).map m = actMorS hM hst := rfl
  let c₁ : APt (fppfO B S hS) M (op P₁) := cor hM O
  let π₁ : P₁ ⟶ O := prj hM O
  have hmj : m ≫ openJ V = smulS actU c₁ (π₁ ≫ openJ V) := by
    apply (SCH).map_injective
    rw [Functor.map_comp, hm]
    exact actMorS_ι hM hst
  let c₂ : APt (fppfO B S hS) M (op P₂) := cor hM P₁
  let π₂ : P₂ ⟶ P₁ := prj hM P₁
  let c' : APt (fppfO B S hS) M (op P₂) := APt.res π₂.op c₁
  have key0 : smulS actU c₂ ((π₂ ≫ m) ≫ openJ V) =
      smulS actU (c₂ * c') ((π₂ ≫ π₁) ≫ openJ V) := by
    have e1 : (π₂ ≫ m) ≫ openJ V = smulS actU c' ((π₂ ≫ π₁) ≫ openJ V) := by
      rw [Category.assoc, hmj, comp_smulS, Category.assoc]
    rw [e1, smulS_mul]
  have key := congrArg (SCH).map key0
  rw [smul_eq_actMor hM hst, smul_eq_actMor hM hst] at key
  -- pull back along the classifying morphism
  let w : T ⟶ (SCH).obj P₂ := MonAff.homOf (MonAff.homOf x h) g
  have hwπ : w ≫ (SCH).map π₂ = MonAff.homOf x h := MonAff.homOf_π _ _
  have hwc : MonAff.pull w (ptS c₂) = g := MonAff.pull_homOf_coord _ _
  have hwc' : MonAff.pull w (ptS c') = h :=
    (MonAff.pull_of_comp_eq hwπ (MonAff.coord M _)).trans (MonAff.pull_homOf_coord x h)
  have a1 : w ≫ (SCH).map (π₂ ≫ m) = MonAff.homOf x h ≫ actMorS hM hst := by
    rw [Functor.map_comp, ← Category.assoc, hwπ, hm]
    rfl
  have a2 : w ≫ (SCH).map (π₂ ≫ π₁) = x := by
    rw [Functor.map_comp, ← Category.assoc, hwπ]
    exact MonAff.homOf_π _ _
  have a3 : MonAff.pull w (ptS (c₂ * c')) = g * h := by
    refine MonoidHom.ext fun p => ?_
    have e1 := DFunLike.congr_fun hwc p
    have e2 := DFunLike.congr_fun hwc' p
    change w.appTop (ptS c₂ p * ptS c' p) = g p * h p
    rw [map_mul]
    exact congrArg₂ _ e1 e2
  have ek1 : w ≫ MonAff.homOf ((SCH).map (π₂ ≫ m)) (ptS c₂) =
      MonAff.homOf (MonAff.homOf x h ≫ actMorS hM hst) g := by
    rw [MonAff.comp_homOf, a1, hwc]
  have ek2 : w ≫ MonAff.homOf ((SCH).map (π₂ ≫ π₁)) (ptS (c₂ * c')) =
      MonAff.homOf x (g * h) := by
    rw [MonAff.comp_homOf, a2, a3]
  have key' := congrArg (fun k => w ≫ k) key
  apply (cancel_mono (iV V)).1
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => k ≫ actMorS hM hst ≫ iV V) ek1).symm.trans ?_
  refine (Category.assoc _ _ _).trans (Eq.trans key' ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ actMorS hM hst ≫ iV V) ek2).trans ?_
  exact (Category.assoc _ _ _).symm

/-- `V`, with its structure morphism, as a scheme over `S`. -/
noncomputable abbrev openOver (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : Over S :=
  Over.mk (iV V ≫ structMap U)

/-- A point of `D(M)` on a scheme over `S`, as a map to its global sections. -/
abbrev ptO {T : Over S} (h : APt (GB.overO S) M (op T)) : Multiplicative M →* Γ(T.left, ⊤) := h

/-- The action on points of `V`, on all schemes over `S`. -/
noncomputable def overSmul (hst : IsStableOpen actU V) {T : Over S}
    (h : APt (GB.overO S) M (op T)) (x : T ⟶ openOver V) : T ⟶ openOver V :=
  Over.homMk (MonAff.homOf x.left (ptO h) ≫ actMorS hM hst) (by
    have hx := Over.w x
    change _ ≫ actMorS hM hst ≫ iV V ≫ structMap U = _
    refine (congrArg (fun k => MonAff.homOf x.left (ptO h) ≫ k) (actMorS_w hM hst)).trans ?_
    exact (MonAff.homOf_π_assoc _ _ _).trans hx)

/-- **The action of `D(M)` on a stable open, on all schemes over `S`.** On the site the action is
only given on objects of bounded size; since `D(M)_V` is an object of the site, it is given by a
morphism of schemes, which acts on all points. -/
noncomputable def overAct (hst : IsStableOpen actU V) :
    AAction (GB.overO S) M (yoneda.obj (openOver V)) where
  smul {T} h x := overSmul hM hst (T := unop T) h x
  one_smul {T} x := by
    refine Over.OverMorphism.ext ?_
    have hL : (MonAff.homOf (Over.Hom.left x) 1 ≫ actMorS hM hst) = Over.Hom.left x := by
      refine (congrArg (fun k => k ≫ actMorS hM hst)
        (MonAff.homOf_one_comp (Over.Hom.left x))).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact (congrArg (fun k => Over.Hom.left x ≫ k) (homOf_id_one hM hst)).trans
        (Category.comp_id _)
    exact hL
  mul_smul {T} g h x := by
    refine Over.OverMorphism.ext ?_
    exact (actMorS_assoc hM hst _ g h).symm
  map_smul {T T'} f h x := by
    refine Over.OverMorphism.ext ?_
    change f.unop.left ≫ MonAff.homOf (Over.Hom.left x) _ ≫ actMorS hM hst =
      MonAff.homOf (f.unop.left ≫ Over.Hom.left x) _ ≫ actMorS hM hst
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun k => k ≫ actMorS hM hst) (MonAff.comp_homOf _ _ _)

end OverAction

/-- `R[P] → Γ(𝔸(P)_T)` is injective for `T` affine. -/
theorem MonAff.evalRing_injective (P : Type u) [AddCommMonoid P] (T : Scheme.{u}) [IsAffine T] :
    Function.Injective (MonAff.evalRing P T) := by
  have hA : IsAffine (MonAff P T) := .of_isIso (MonAff.isoOfIsAffine P T).hom
  have h1 : IsIso ((MonAff P T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MonAff.evalRing P T))) :=
    inferInstanceAs (IsIso (MonAff.isoOfIsAffine P T).hom)
  have h2 : IsIso (Spec.map (CommRingCat.ofHom (MonAff.evalRing P T))) :=
    IsIso.of_isIso_comp_left (MonAff P T).toSpecΓ _
  have h3 : IsIso (CommRingCat.ofHom (MonAff.evalRing P T)) := by
    have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (MonAff.evalRing P T)).op) := h2
    have := isIso_of_reflects_iso (CommRingCat.ofHom (MonAff.evalRing P T)).op Scheme.Spec
    exact isIso_of_op _
  exact ((ConcreteCategory.isIso_iff_bijective _).1 h3).1

section Fixed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (hM : B.Contains (Spec (ZMon M))) {U : BigFppfOver B S hS}
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
  {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  (hst : IsStableOpen actU V)

/-- An object of the site as a scheme over `S`. -/
noncomputable abbrev ov (T : BigFppfOver B S hS) : Over S := Over.mk (structMap T)

/-- A morphism of the site, as a morphism over `S`. -/
noncomputable def ovHom {T T' : BigFppfOver B S hS} (s : T' ⟶ T) : ov T' ⟶ ov T :=
  Over.homMk ((SCH).map s) (congrArg B.inclusion.map (Over.w s))

/-- A morphism `T → V` of the site, as a morphism over `S`. -/
noncomputable def ovMap {T : BigFppfOver B S hS} (t : T ⟶ openObj V) : ov T ⟶ openOver V :=
  Over.homMk ((SCH).map t) (congrArg B.inclusion.map (Over.w t))

include hst in
/-- A point of `V` on the site fixed by `D(M/Z)` is fixed for the action on all schemes over `S`. -/
theorem overSmul_eq_of_fixed {Z : AddSubgroup M} (hQ : B.Contains (Spec (ZMon (M ⧸ Z))))
    {T : BigFppfOver B S hS} (t : T ⟶ openObj V)
    (hfix : (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T))
    {W : Over S} (f : W ⟶ ov T) (h : APt (GB.overO S) M (op W)) (hh : TrivialOn Z h) :
    overSmul hM hst h (f ≫ ovMap t) = f ≫ ovMap t := by
  obtain ⟨k, rfl⟩ := exists_quotient_of_trivialOn hh
  let Qo := monAffObj (M ⧸ Z) hQ T
  let π : Qo ⟶ T := prj hQ T
  let t₁ : Qo ⟶ openObj V := π ≫ t
  let k₀ : Multiplicative (M ⧸ Z) →* Γ((SCH).obj Qo, ⊤) := cor hQ T
  let h₀ : APt (fppfO B S hS) M (op Qo) :=
    k₀.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z))
  have hfx : smulS actU h₀ (t₁ ≫ openJ V) = t₁ ≫ openJ V := by
    have e : t₁ ≫ openJ V = π ≫ t ≫ openJ V := Category.assoc _ _ _
    rw [e]
    exact hfix π.op (cor hQ T)
  have e0 := smul_eq_actMor hM hst t₁ h₀
  rw [hfx, Functor.map_comp] at e0
  have e1 : MonAff.homOf ((SCH).map t₁) (ptS h₀) ≫ actMorS hM hst = (SCH).map t₁ := by
    apply (cancel_mono (iV V)).1
    exact (Category.assoc _ _ _).trans e0.symm
  let y : W.left ⟶ (SCH).obj Qo := MonAff.homOf f.left (show Multiplicative (M ⧸ Z) →* Γ(W.left, ⊤) from k)
  have hyπ : y ≫ (SCH).map π = f.left := MonAff.homOf_π _ _
  have hyt : y ≫ (SCH).map t₁ = f.left ≫ (SCH).map t := by
    rw [Functor.map_comp, ← Category.assoc, hyπ]
  have hyk : MonAff.pull y (ptS h₀) = ptO (k.comp (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Z))) := by
    refine MonoidHom.ext fun p => ?_
    exact MonAff.homOf_coord (P := M ⧸ Z) f.left _ (AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk' Z) p)
  refine Over.OverMorphism.ext ?_
  have e2 := congrArg (fun q => y ≫ q) e1
  refine Eq.trans ?_ (e2.trans hyt)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (fun q => q ≫ actMorS hM hst) ?_
  refine Eq.trans ?_ (MonAff.comp_homOf y ((SCH).map t₁) (ptS h₀)).symm
  rw [hyt, hyk]
  rfl

include hst in
/-- A point of `V` on the site fixed for the action on all schemes is fixed on the site. -/
theorem fixed_of_overSmul_eq {Z : AddSubgroup M} {T : BigFppfOver B S hS} (t : T ⟶ openObj V)
    (H : ∀ {W : BigFppfOver B S hS} (s : W ⟶ T) (h : APt (fppfO B S hS) M (op W)), TrivialOn Z h →
      overSmul hM hst (T := ov W) h (ovHom s ≫ ovMap t) = ovHom s ≫ ovMap t) :
    (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T) := by
  refine mem_fixedPoints_quotient_iff.mpr ?_
  intro T' s h hh
  have e := smul_eq_actMor hM hst (s.unop ≫ t) h
  have e' := congrArg (fun q => (Over.Hom.left q) ≫ iV V) (H s.unop h hh)
  apply (SCH).map_injective
  have e3 : (s.unop ≫ t ≫ openJ V) = (s.unop ≫ t) ≫ openJ V := (Category.assoc _ _ _).symm
  change (SCH).map (smulS actU h (s.unop ≫ t ≫ openJ V)) = (SCH).map (s.unop ≫ t ≫ openJ V)
  rw [e3, e, Functor.map_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ e'
  refine congrArg (fun q => q ≫ iV V) ?_
  refine congrArg (fun q => q ≫ actMorS hM hst) ?_
  congr 1

section Kills

open Magnetism

attribute [local instance] GB.gradedAlgebraOf

variable [IsAffineHom (openOver V).hom]

include hst in
/-- Fixed points kill the homogeneous elements of degree outside `Z`, affine case. -/
theorem ptX_eq_zero_of_affine {Z : AddSubgroup M} (hQ : B.Contains (Spec (ZMon (M ⧸ Z))))
    {U₀ : S.Opens} (hU₀ : IsAffineOpen U₀) {T : BigFppfOver B S hS} (t : T ⟶ openObj V)
    (hfix : (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T))
    {W : Over S} [IsAffine W.left] (hW : GB.LiesOver W U₀) (f : W ⟶ ov T) {m : M} (hm : m ∉ Z)
    {a : GB.Aalg (openOver V) U₀}
    (ha : a ∈ GB.gradingOf hU₀ (overAct hM hst) m) :
    GB.ptX (openOver V) hU₀ W hW (f ≫ ovMap t) a = 0 := by
  let Q := M ⧸ Z
  let Wq : Over S := Over.mk (MonAff.π Q W.left ≫ W.hom)
  let pr : Wq ⟶ W := Over.homMk (MonAff.π Q W.left) rfl
  have hWq : GB.LiesOver Wq U₀ := hW.of_hom pr
  let k : Multiplicative Q →* Γ(Wq.left, ⊤) := MonAff.coord Q W.left
  let h : APt (GB.overO S) M (op Wq) := k.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z))
  have htr : TrivialOn Z h := by
    refine MonoidHom.ext fun n => ?_
    have hn : QuotientAddGroup.mk' Z ((Multiplicative.toAdd n : Z.toAddSubmonoid) : M) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (Multiplicative.toAdd n).2
    change k (Multiplicative.ofAdd (QuotientAddGroup.mk' Z ((Multiplicative.toAdd n :
      Z.toAddSubmonoid) : M))) = 1
    rw [hn]
    exact map_one k
  have hfx := overSmul_eq_of_fixed hM hst hQ t hfix (pr ≫ f) h htr
  have hs := GB.ptX_smul_of_mem hU₀ (overAct hM hst) hWq h ((pr ≫ f) ≫ ovMap t) ha
  have hs' : (overAct hM hst).smul (U := op Wq) h ((pr ≫ f) ≫ ovMap t) = (pr ≫ f) ≫ ovMap t := hfx
  rw [hs'] at hs
  have hpb : GB.ptX (openOver V) hU₀ Wq hWq ((pr ≫ f) ≫ ovMap t) a =
      (pr.left.appTop).hom (GB.ptX (openOver V) hU₀ W hW (f ≫ ovMap t) a) := by
    rw [Category.assoc, GB.ptX_comp (openOver V) hU₀ hW hWq]
    rfl
  rw [hpb] at hs
  set v : Γ(W.left, ⊤) := GB.ptX (openOver V) hU₀ W hW (f ≫ ovMap t) a with hv
  have hsing : MonAff.evalRing Q W.left (AddMonoidAlgebra.single (QuotientAddGroup.mk m : Q) v) =
      MonAff.evalRing Q W.left (AddMonoidAlgebra.single 0 v) := by
    have e1 : (AddMonoidAlgebra.single (QuotientAddGroup.mk m : Q) v) =
        AddMonoidAlgebra.single (QuotientAddGroup.mk m : Q) 1 * AddMonoidAlgebra.single 0 v := by
      rw [AddMonoidAlgebra.single_mul_single, add_zero, one_mul]
    rw [e1, map_mul, MonAff.evalRing_single_one, MonAff.evalRing_single_zero]
    exact hs.symm
  have hinj := MonAff.evalRing_injective Q W.left hsing
  have hne : (QuotientAddGroup.mk m : Q) ≠ 0 := fun e => hm ((QuotientAddGroup.eq_zero_iff m).1 e)
  have hc := congrArg (fun x => AddMonoidAlgebra.coeff x (QuotientAddGroup.mk m : Q)) hinj
  have r : v = 0 := by
    simpa [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne.symm] using hc
  exact r

include hst in
/-- **Proposition 3.35, closed part, on a stable `S`-affine open.** A point of `V` on the site which
is fixed by `D(M/Z)` underlies a point of the attractor `V^Z` on all schemes. -/
theorem exists_att_of_fixed {Z : AddSubgroup M} (hQ : B.Contains (Spec (ZMon (M ⧸ Z))))
    {T : BigFppfOver B S hS} (t : T ⟶ openObj V)
    (hfix : (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T)) :
    ∃ φ : AttractorPt (overAct hM hst) Z.toAddSubmonoid (ov T), φ.toPoint = ovMap t := by
  refine GB.exists_att_of_local (overAct hM hst) (ovMap t) ?_
  intro W f U₀ hW
  refine (GB.exists_att_iff_kills (overAct hM hst) U₀.2 hW _).2 ?_
  intro a ha
  refine Submodule.span_induction (p := fun a _ =>
    GB.ptX (openOver V) U₀.2 W hW (f ≫ ovMap t) a = 0) ?_ ?_ ?_ ?_ ha
  · intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
    obtain ⟨m, hm, hx⟩ := hx
    refine GB.section_eq_zero_of_cover _ fun i => ?_
    have hW' := hW.of_hom (GB.coverHom W i)
    have e := ptX_eq_zero_of_affine hM hst hQ U₀.2 t hfix hW' (GB.coverHom W i ≫ f) hm hx
    rw [Category.assoc, GB.ptX_comp (openOver V) U₀.2 hW hW'] at e
    exact e
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul, map_mul, hx, mul_zero]

include hst in
/-- A point of `V` underlying a point of `V^Z` is fixed. -/
theorem fixed_of_exists_att {Z : AddSubgroup M} {T : BigFppfOver B S hS} (t : T ⟶ openObj V)
    (φ : AttractorPt (overAct hM hst) Z.toAddSubmonoid (ov T)) (hφ : φ.toPoint = ovMap t) :
    (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T) := by
  refine fixed_of_overSmul_eq hM hst t ?_
  intro W s h hh
  have := mem_fixedPoints_quotient_iff.mp (AttractorPt.toPoint_mem_fixedPoints φ)
    (T' := op (ov W)) (ovHom s).op h hh
  rw [hφ] at this
  exact this

end Kills

end Fixed

section Closed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M]

local notation "SCH" => BigFppfOver.toScheme B S hS

variable (hM : B.Contains (Spec (ZMon M))) {U : BigFppfOver B S hS}
  {actU : AAction (fppfO B S hS) M (yoneda.obj U)}

include hM in
/-- **Corollary 3.22 for a stable `S`-affine open**, with Proposition 3.35: the fixed locus of a
stable `S`-affine open `V` is a closed subscheme of `V`. -/
theorem exists_closed_fixed_open {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (hst : IsStableOpen actU V) (haff : IsAffineHom (openOver V).hom) {Z : AddSubgroup M}
    (hQ : B.Contains (Spec (ZMon (M ⧸ Z)))) :
    ∃ (Zs : Scheme.{u}) (i : Zs ⟶ (SCH).obj (openObj V)), IsClosedImmersion i ∧
      ∀ {T : BigFppfOver B S hS} (t : T ⟶ openObj V),
        (∃ z : (SCH).obj T ⟶ Zs, z ≫ i = (SCH).map t) ↔
          (t ≫ openJ V) ∈ (fixedPoints (quotientAction actU Z)).obj (op T) := by
  let act := overAct hM hst
  refine ⟨(GB.Zatt act Z.toAddSubmonoid).left, (GB.iAtt act Z.toAddSubmonoid).left,
    inferInstance, fun {T} t => ⟨?_, fun hfix => ?_⟩⟩
  · rintro ⟨z, hz⟩
    have hw : z ≫ (GB.Zatt act Z.toAddSubmonoid).hom = structMap T := by
      have h1 := Over.w (GB.iAtt act Z.toAddSubmonoid)
      refine (congrArg (fun q => z ≫ q) h1.symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun q => q ≫ (openOver V).hom) hz).trans ?_
      exact Over.w (ovMap t)
    let z' : ov T ⟶ GB.Zatt act Z.toAddSubmonoid := Over.homMk z hw
    obtain ⟨φ, hφ⟩ := (GB.exists_lift_iff act Z.toAddSubmonoid (ovMap t)).1
      ⟨z', Over.OverMorphism.ext hz⟩
    intro T' s' h'
    exact fixed_of_exists_att hM hst t φ hφ s' h'
  · obtain ⟨φ, hφ⟩ := exists_att_of_fixed hM hst hQ t hfix
    obtain ⟨z, hz⟩ := (GB.exists_lift_iff act Z.toAddSubmonoid (ovMap t)).2 ⟨φ, hφ⟩
    exact ⟨z.left, congrArg Over.Hom.left hz⟩

/-- Lift a morphism of the site with image in the open `V`. -/
lemma exists_lift_open {V : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    {P : BigFppfOver B S hS} (r : P ⟶ U) (hr : ∀ p, (SCH).map r p ∈ V) :
    ∃ t : P ⟶ openObj V, t ≫ openJ V = r := by
  have hrr : Set.range ((SCH).map r) ⊆ Set.range (iV V) := by
    have e : Set.range (iV V) = (V : Set _) := Scheme.Opens.range_ι V
    rw [e]
    rintro _ ⟨p, rfl⟩
    exact hr p
  have fac := IsOpenImmersion.lift_fac (iV V) ((SCH).map r) hrr
  refine ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift (iV V) ((SCH).map r) hrr)) ?_, ?_⟩
  · apply B.inclusion.map_injective
    have hw : (SCH).map r ≫ structMap U = structMap P := congrArg B.inclusion.map (Over.w r)
    refine Eq.trans ?_ hw
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ structMap U) fac)
  · apply (SCH).map_injective
    rw [Functor.map_comp]
    exact fac

include hM in
/-- **The fixed locus of the chart is closed.** If `U` is a disjoint union of `D(M)_S`-stable
`S`-affine opens, the fixed points of `D(M/Z)` in `U` are a closed subscheme of `U`
(Corollary 3.22 for the pieces, with Proposition 3.35). -/
theorem exists_closed_fixed (hd : HasAffineDecomposition actU) {Z : AddSubgroup M}
    (hQ : B.Contains (Spec (ZMon (M ⧸ Z)))) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ U), IsClosedImmersion ((SCH).map j) ∧
      ∀ {T : BigFppfOver B S hS} (y : T ⟶ U), (∃ c : T ⟶ W, c ≫ j = y) ↔
        y ∈ (fixedPoints (quotientAction actU Z)).obj (op T) := by
  obtain ⟨A, V, hV⟩ := hd
  have hone := fun a => exists_closed_fixed_open hM (hV.stable a)
    (show IsAffineHom (openOver (V a)).hom from hV.isAffineHom a) hQ
  choose Zs i hi hfx using hone
  let σ := fun a => Sigma.ι Zs a
  let f : ∐ Zs ⟶ (SCH).obj U := Sigma.desc fun a => i a ≫ iV (V a)
  have hσf : ∀ a, σ a ≫ f = i a ≫ iV (V a) := fun a => Sigma.ι_desc _ _
  have hmemV : ∀ a (q : Zs a), f (σ a q) ∈ V a := by
    intro a q
    have e : f (σ a q) = iV (V a) (i a q) := by
      rw [← Scheme.Hom.comp_apply, hσf, Scheme.Hom.comp_apply]
    rw [e]
    exact (i a q).2
  have hrange : ∀ a, Set.range (σ a) = SetLike.coe (f ⁻¹ᵁ V a) := by
    intro a
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact hmemV a q
    · intro hx
      obtain ⟨b, q, rfl⟩ := (sigmaOpenCover Zs).exists_eq x
      have hb : f (σ b q) ∈ V b := hmemV b q
      by_cases hab : a = b
      · subst hab
        exact ⟨q, rfl⟩
      · exact absurd (show f (σ b q) ∈ (V a ⊓ V b : ((SCH).obj U).Opens) from ⟨hx, hb⟩)
          (by rw [disjoint_iff.1 (hV.disjoint hab)]; simp)
  have hclosed : IsClosedImmersion f := by
    refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) (f := f) V
      hV.iSup_eq_top).2 fun a => ?_
    let e : Zs a ≅ (f ⁻¹ᵁ V a).toScheme := IsOpenImmersion.isoOfRangeEq (σ a) (f ⁻¹ᵁ V a).ι (by
      rw [hrange a, Scheme.Opens.range_ι])
    have he : e.hom ≫ (f ⁻¹ᵁ V a).ι = σ a := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hres : e.hom ≫ (f ∣_ V a) = i a := by
      apply (cancel_mono (V a).ι).1
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he]
      exact hσf a
    let i' : Zs a ⟶ (V a).toScheme := i a
    have hi' : IsClosedImmersion i' := hi a
    have h2 : (f ∣_ V a) = e.inv ≫ i' := (Iso.eq_inv_comp e).2 hres
    rw [h2]
    infer_instance
  have hWc : B.Contains (∐ Zs) := Scheme.size_lt_of_isClosedImmersion f U.left.2
  let W : BigFppfOver B S hS := siteObject B S hS hWc (f ≫ structMap U)
  let j : W ⟶ U := Over.homMk (ObjectProperty.homMk f) rfl
  have hj : (SCH).map j = f := rfl
  refine ⟨W, j, hclosed, fun {T} y => ⟨?_, fun hy => ?_⟩⟩
  · -- a point of the closed subscheme is fixed: test on the opens over the pieces
    rintro ⟨c, rfl⟩
    refine mem_fixedPoints_quotient_iff.mpr ?_
    intro T' s h hh
    let T'' := unop T'
    let c'' : T'' ⟶ W := s.unop ≫ c
    let y'' : T'' ⟶ U := s.unop ≫ c ≫ j
    have hy'' : y'' = c'' ≫ j := (Category.assoc _ _ _).symm
    change smulS actU h y'' = y''
    apply (SCH).map_injective
    let O : A → ((SCH).obj T'').Opens := fun a => (SCH).map y'' ⁻¹ᵁ V a
    have hO : TopologicalSpace.IsOpenCover O := by
      change iSup O = ⊤
      rw [show iSup O = (SCH).map y'' ⁻¹ᵁ iSup V from (Scheme.Hom.preimage_iSup _ _).symm,
        hV.iSup_eq_top]
      rfl
    refine Scheme.Cover.hom_ext ((SCH).obj T'' |>.openCoverOfIsOpenCover O hO) _ _ fun a => ?_
    change (O a).ι ≫ _ = (O a).ι ≫ _
    let P := openObj (O a)
    let pJ : P ⟶ T'' := openJ (O a)
    obtain ⟨t, ht⟩ := exists_lift_open (V := V a) (pJ ≫ y'') (fun p => by
      have e : (SCH).map (pJ ≫ y'') p = (SCH).map y'' ((O a).ι p) := by
        rw [Functor.map_comp, Scheme.Hom.comp_apply]
        rfl
      rw [e]
      exact p.2)
    have hrng : Set.range ((SCH).map (pJ ≫ c'')) ⊆ Set.range (σ a) := by
      rw [hrange a]
      rintro _ ⟨p, rfl⟩
      change f ((SCH).map (pJ ≫ c'') p) ∈ V a
      have hk : (SCH).map (pJ ≫ y'') = (SCH).map (pJ ≫ c'') ≫ f := by
        rw [hy'', ← Category.assoc]
        exact Functor.map_comp _ _ _
      have e : f ((SCH).map (pJ ≫ c'') p) = (SCH).map (pJ ≫ y'') p := by
        rw [hk, Scheme.Hom.comp_apply]
      rw [e, ← ht, Functor.map_comp, Scheme.Hom.comp_apply]
      exact ((SCH).map t p).2
    let z := IsOpenImmersion.lift (σ a) ((SCH).map (pJ ≫ c'')) hrng
    have hz : z ≫ σ a = (SCH).map (pJ ≫ c'') := IsOpenImmersion.lift_fac _ _ _
    have hzi : z ≫ i a = (SCH).map t := by
      apply (cancel_mono (iV (V a))).1
      rw [Category.assoc, ← hσf a, ← Category.assoc, hz, ← hj, ← Functor.map_comp, Category.assoc,
        ← hy'', ← ht, Functor.map_comp]
    have hfix : (t ≫ openJ (V a)) ∈ (fixedPoints (quotientAction actU Z)).obj (op P) :=
      fun {T₁} s₁ h₁ => (hfx a t).1 ⟨z, hzi⟩ s₁ h₁
    have htr : TrivialOn Z (APt.res pJ.op h) := by
      have h1 : APt.toMagnet Z.toAddSubmonoid (APt.res pJ.op h) =
          APt.res pJ.op (APt.toMagnet Z.toAddSubmonoid h) := APt.toMagnet_res _ _ _
      refine h1.trans ?_
      rw [show APt.toMagnet Z.toAddSubmonoid h = 1 from hh]
      ext p; simp
    have hf2 := mem_fixedPoints_quotient_iff.mp hfix (𝟙 (op P)) (APt.res pJ.op h) htr
    have hf3 : smulS actU (APt.res pJ.op h) (t ≫ openJ (V a)) = t ≫ openJ (V a) := by
      have e : (yoneda.obj U).map (𝟙 (op P)) (t ≫ openJ (V a)) = t ≫ openJ (V a) := by
        simp
      rw [e] at hf2
      exact hf2
    have hf4 : pJ ≫ smulS actU h y'' = pJ ≫ y'' := by
      rw [comp_smulS, ← ht, hf3]
    have hf5 := congrArg (SCH).map hf4
    rw [Functor.map_comp, Functor.map_comp] at hf5
    exact hf5
  · -- a fixed point factors through the closed subscheme: glue over the pieces
    let O : A → ((SCH).obj T).Opens := fun a => (SCH).map y ⁻¹ᵁ V a
    have hO : TopologicalSpace.IsOpenCover O := by
      change iSup O = ⊤
      rw [show iSup O = (SCH).map y ⁻¹ᵁ iSup V from (Scheme.Hom.preimage_iSup _ _).symm,
        hV.iSup_eq_top]
      rfl
    have hlift : ∀ a, ∃ z : (O a).toScheme ⟶ ∐ Zs, z ≫ f = (O a).ι ≫ (SCH).map y := by
      intro a
      let P := openObj (O a)
      let pJ : P ⟶ T := openJ (O a)
      obtain ⟨t, ht⟩ := exists_lift_open (V := V a) (pJ ≫ y) (fun p => by
        have e : (SCH).map (pJ ≫ y) p = (SCH).map y ((O a).ι p) := by
          rw [Functor.map_comp, Scheme.Hom.comp_apply]
          rfl
        rw [e]
        exact p.2)
      have hfix : (t ≫ openJ (V a)) ∈ (fixedPoints (quotientAction actU Z)).obj (op P) := by
        rw [ht]
        exact (fixedPoints (quotientAction actU Z)).map pJ.op hy
      obtain ⟨z, hz⟩ := (hfx a t).2 hfix
      have hmap := congrArg (SCH).map ht
      rw [Functor.map_comp, Functor.map_comp] at hmap
      refine ⟨z ≫ σ a, (Category.assoc _ _ _).trans ?_⟩
      refine (congrArg (fun q => z ≫ q) (hσf a)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun q => q ≫ iV (V a)) hz).trans ?_
      exact hmap
    choose z hz using hlift
    let 𝒰 := ((SCH).obj T).openCoverOfIsOpenCover O hO
    have : Mono f := inferInstance
    let c₀ : (SCH).obj T ⟶ ∐ Zs := 𝒰.glueMorphisms z (fun a b => by
      apply (cancel_mono f).1
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun q => pullback.fst (𝒰.f a) (𝒰.f b) ≫ q) (hz a)).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (fun q => pullback.snd (𝒰.f a) (𝒰.f b) ≫ q) (hz b)).symm
      refine (Category.assoc _ _ _).symm.trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      exact congrArg (fun q => q ≫ (SCH).map y) pullback.condition)
    have hc₀ : c₀ ≫ f = (SCH).map y := by
      refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (fun q => q ≫ f) (Scheme.Cover.ι_glueMorphisms 𝒰 z _ a)).trans (hz a)
    let c : T ⟶ W := Over.homMk (ObjectProperty.homMk c₀) (by
      apply B.inclusion.map_injective
      have hw : (SCH).map y ≫ structMap U = structMap T := congrArg B.inclusion.map (Over.w y)
      refine Eq.trans ?_ hw
      rw [← hc₀]
      exact (Category.assoc _ _ _).symm)
    refine ⟨c, ?_⟩
    apply (SCH).map_injective
    rw [Functor.map_comp]
    exact hc₀

end Closed

section Final

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- `Spec ℤ[M]` is below any cutoff if `M` is countable. -/
theorem contains_zmon_countable (hS : B.Contains S) (M : Type u) [AddCommMonoid M] [Countable M] :
    B.Contains (Spec (ZMon M)) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hS ?_
  have hc : Countable (AddMonoidAlgebra (ULift.{u} ℤ) M) :=
    AddMonoidAlgebra.coeff_injective.countable
  refine (Cardinal.mk_le_aleph0 (α := AddMonoidAlgebra (ULift.{u} ℤ) M)).trans ?_
  exact (Scheme.aleph0_le_size S).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)

variable {M : Type w} [AddCommGroup M]

/-- The fixed points of `D(M/Z)` form a sheaf. -/
theorem isSheaf_fixedPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (act : AAction (fppfO B S hS) M X)
    (Z : AddSubgroup M) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (fixedPoints (quotientAction act Z)).toFunctor := by
  have hX' := (isSheaf_iff_isSheaf_of_type _ _).mp hX
  refine (isSheaf_iff_isSheaf_of_type _ _).mpr ((Subfunctor.isSheaf_iff _ hX').mpr ?_)
  intro T x hx T₁ s h
  have hc := (BigFppfOver.topology B S hS).pullback_stable s.unop hx
  refine (hX' _ hc).isSeparatedFor.ext fun W q hq => ?_
  have hq2 := hq (T' := op W) (𝟙 _) (APt.res q.op h)
  rw [(quotientAction act Z).map_smul]
  have ey : X.map q.op (X.map s x) = X.map (𝟙 (op W)) (X.map (q ≫ s.unop).op x) := by
    rw [CategoryTheory.Functor.map_id, op_comp, Functor.map_comp_apply]
    rfl
  rw [ey]
  exact hq2

/-- Every point of `D(Z)` extends fppf locally to `D(M)`, for `M` in any universe, through a
copy `M'` of `M` in the universe of the site. -/
theorem extSieve_mem_of_equiv {M' : Type u} [AddCommGroup M'] [AddGroup.FG M'] (e : M' ≃+ M)
    (Z : AddSubgroup M) {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) :
    extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T := by
  let Z' : AddSubgroup M' := Z.comap e.toAddMonoidHom
  let ζ : Z'.toAddSubmonoid →+ Z.toAddSubmonoid :=
    { toFun := fun x => ⟨e x, x.2⟩
      map_zero' := Subtype.ext (map_zero e)
      map_add' := fun x y => Subtype.ext (map_add e _ _) }
  let a' : APt (fppfO B S hS) Z'.toAddSubmonoid (op T) :=
    a.comp (AddMonoidHom.toMultiplicative ζ)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ (extSieve_mem Z' a')
  rintro W s ⟨h', hh'⟩
  refine ⟨h'.comp (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom), ?_⟩
  refine MonoidHom.ext fun n => ?_
  let n₀ : Z.toAddSubmonoid := Multiplicative.toAdd n
  let n' : Z'.toAddSubmonoid := ⟨e.symm n₀, by
    change e (e.symm n₀) ∈ Z
    rw [e.apply_symm_apply]
    exact n₀.2⟩
  have hz : ζ n' = n₀ := Subtype.ext (e.apply_symm_apply _)
  have := DFunLike.congr_fun hh' (Multiplicative.ofAdd n')
  change h' (Multiplicative.ofAdd (e.symm n₀)) =
    ((fppfO B S hS).map s.op).hom (a (Multiplicative.ofAdd (ζ n'))) at this
  rw [hz] at this
  exact this

/-- **The fixed locus of the chart is closed**, for `M` in any universe. -/
theorem exists_closed_fixed_of_equiv {M' : Type u} [AddCommGroup M'] [AddGroup.FG M'] (e : M' ≃+ M)
    {U : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
    (hd : HasAffineDecomposition actU) (Z : AddSubgroup M) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ U), IsClosedImmersion ((SCH).map j) ∧
      ∀ {T : BigFppfOver B S hS} (y : T ⟶ U), (∃ c : T ⟶ W, c ≫ j = y) ↔
        y ∈ (fixedPoints (quotientAction actU Z)).obj (op T) := by
  let Z' : AddSubgroup M' := Z.comap e.toAddMonoidHom
  let actU' : AAction (fppfO B S hS) M' (yoneda.obj U) := actU.comap e.symm.toAddMonoidHom
  have hcM : Countable M' := by
    have : Module.Finite ℤ M' := Module.Finite.iff_addGroup_fg.mpr inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ M'
    exact hf.countable
  have hcQ : Countable (M' ⧸ Z') := Quotient.countable
  have hM := contains_zmon_countable (B := B) hS M'
  have hQ := contains_zmon_countable (B := B) hS (M' ⧸ Z')
  obtain ⟨A, V, hV⟩ := hd
  have hd' : HasAffineDecomposition actU' :=
    ⟨A, V, hV.disjoint, hV.iSup_eq_top, fun a {T} t h hr => hV.stable a t _ hr, hV.isAffineHom⟩
  obtain ⟨W, j, hj, hiff⟩ := exists_closed_fixed hM hd' hQ
  refine ⟨W, j, hj, fun {T} y => (hiff y).trans ?_⟩
  rw [mem_fixedPoints_quotient_iff, mem_fixedPoints_quotient_iff]
  constructor
  · intro H T₁ s h hh
    have htr : TrivialOn Z' (h.comp (AddMonoidHom.toMultiplicative e.toAddMonoidHom)) := by
      refine MonoidHom.ext fun n => ?_
      exact DFunLike.congr_fun hh
        (Multiplicative.ofAdd (⟨e (Multiplicative.toAdd n : Z'.toAddSubmonoid),
          (Multiplicative.toAdd n).2⟩ : Z.toAddSubmonoid))
    have := H s _ htr
    have e2 : ((h.comp (AddMonoidHom.toMultiplicative e.toAddMonoidHom)).comp
        (AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom)) = h :=
      MonoidHom.ext fun m => congrArg h (congrArg Multiplicative.ofAdd (e.apply_symm_apply _))
    change actU.smul _ _ = _ at this
    rwa [e2] at this
  · intro H T₁ s h hh
    refine H s _ ?_
    refine MonoidHom.ext fun n => ?_
    let n₀ : Z.toAddSubmonoid := Multiplicative.toAdd n
    exact DFunLike.congr_fun hh (Multiplicative.ofAdd (⟨e.symm n₀, by
      change e (e.symm n₀) ∈ Z
      rw [e.apply_symm_apply]
      exact n₀.2⟩ : Z'.toAddSubmonoid))

/-- The inclusion of the fixed points of the chart is a closed immersion, tested after every
representable base change. -/
theorem presheaf_fixed_ι {U W : BigFppfOver B S hS} {actU : AAction (fppfO B S hS) M (yoneda.obj U)}
    {Z : AddSubgroup M} (j : W ⟶ U) (hj : IsClosedImmersion ((SCH).map j))
    (hiff : ∀ {T : BigFppfOver B S hS} (y : T ⟶ U), (∃ c : T ⟶ W, c ≫ j = y) ↔
      y ∈ (fixedPoints (quotientAction actU Z)).obj (op T)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH)))
      (fixedPoints (quotientAction actU Z)).ι := by
  let κ : yoneda.obj W ⟶ (fixedPoints (quotientAction actU Z)).toFunctor :=
    { app := fun T => ↾ fun c => ⟨(c : unop T ⟶ W) ≫ j, (hiff _).1 ⟨c, rfl⟩⟩
      naturality := fun T T' s => by
        ext c
        exact Subtype.ext (Category.assoc _ _ _) }
  have : Mono ((SCH).map j) := inferInstance
  have hκ : IsIso κ := by
    refine (NatTrans.isIso_iff_isIso_app κ).2 fun T => ?_
    refine (isIso_iff_bijective _).2 ⟨fun c c' h => ?_, fun y => ?_⟩
    · apply (SCH).map_injective
      apply (cancel_mono ((SCH).map j)).1
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun q => (SCH).map (Subtype.val q)) h
    · obtain ⟨c, hc⟩ := (hiff (T := unop T) y.1).2 y.2
      exact ⟨c, Subtype.ext hc⟩
  have hw : κ ≫ (fixedPoints (quotientAction actU Z)).ι = yoneda.map j := by
    ext T c
    rfl
  have hP : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (SCH))) (yoneda.map j) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ j).2 hj
  have hpb : IsPullback (inv κ) (fixedPoints (quotientAction actU Z)).ι (yoneda.map j) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, hw]⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hP

end Final

/-- **Proposition 8.1** (`M` finitely generated). Let `Z ⊆ M` be a subgroup and let `X` be an
algebraic space over `S` with an action of `D(M)_S`. If `X` has a `Z`-FPR atlas, then the attractor
`X^Z`, which identifies with the fixed space `X^{D(M/Z)}` (Proposition 3.35), is representable by a
closed subspace of `X`. -/
theorem prop81FG : Prop81StatementFG.{w, u} := by
  intro B S hS M _ _ X hX actX Z ⟨U, actU, g, hg⟩
  have hcM : Countable M := by
    have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ M
    exact hf.countable
  have hsm : Small.{u} M := Countable.toSmall M
  let e : Shrink.{u} M ≃+ M := Shrink.addEquiv
  have hfg : AddGroup.FG (Shrink.{u} M) := AddGroup.fg_of_surjective
    (f := e.symm.toAddMonoidHom) e.symm.surjective
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) X :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hX.isSheaf
  have hcov : ∀ {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)),
      extSieve (fppfO B S hS) Z a ∈ BigFppfOver.topology B S hS T :=
    fun a => extSieve_mem_of_equiv e Z a
  let Y := (fixedPoints (quotientAction actX Z)).toFunctor
  let i : Y ⟶ X := (fixedPoints (quotientAction actX Z)).ι
  have hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y := isSheaf_fixedPoints hX.isSheaf actX Z
  obtain ⟨W, j, hj, hiff⟩ := exists_closed_fixed_of_equiv e hg.atlas.decomposition Z
  have hι := presheaf_fixed_ι j hj hiff
  have hpb : IsPullback (fixedMap (IsEquivariant.comap (actU := actU) (actX := actX) (f := g)
        hg.atlas.equivariant (QuotientAddGroup.mk' Z)))
      (fixedPoints (quotientAction actU Z)).ι i g := hg.isZFPR
  have hsq : IsPullback hpb.isoPullback.inv (pullback.snd i g)
      (fixedPoints (quotientAction actU Z)).ι (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hV := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hι
  have hres := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS) hYs hX
    hg.atlas.surjective hg.atlas.etale hV
  refine ⟨Y, i, ⟨fun T => attractorFixedEquivOfCover hsh hcov T, fun s z =>
    attractorFixedEquivOfCover_naturality hsh hcov s z⟩, hres.1, hres.2, fun T y => ?_⟩
  exact (congrArg Subtype.val
    ((attractorFixedEquivOfCover (act := actX) hsh hcov T).symm_apply_apply y)).symm

/-- **Theorem 8.3 (vii)** for a subgroup `Z` (where Proposition 5.1 is not needed), with
**Proposition 8.1**: if `X` is a scheme with a `Z`-FPR atlas, for `M` finitely generated, then `X^Z`
is a closed subscheme of `X`. -/
theorem prop81FG_of_scheme {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type w}
    [AddCommGroup M] [AddGroup.FG M] {T : BigFppfOver B S hS}
    (hX : IsAlgebraicSpace B S hS (yoneda.obj T)) (act : AAction (fppfO B S hS) M (yoneda.obj T))
    (Z : AddSubgroup M) (hat : ExistsZFPRAtlas act Z) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ T) (r : RepresentsAttractor act Z.toAddSubmonoid (yoneda.obj W)),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      ∀ (T' : BigFppfOver B S hS) (y : T' ⟶ W), y ≫ j = (r.equiv T' y).toPoint := by
  obtain ⟨Y, i, r, -, hp, hpt⟩ := prop81FG.{w, u} B S hS M (yoneda.obj T) hX act Z hat
  let R := hp.rep
  let W := R.pullback (𝟙 (yoneda.obj T))
  let j : W ⟶ T := R.snd (𝟙 _)
  let φ : yoneda.obj W ⟶ Y := R.fst (𝟙 _)
  have hpb := R.isPullback (𝟙 (yoneda.obj T))
  have hφ : φ ≫ i = yoneda.map j := by simpa using hpb.w
  have hφiso : IsIso φ := hpb.isIso_fst_of_isIso
  have hbij : ∀ T' : (BigFppfOver B S hS)ᵒᵖ, Function.Bijective (φ.app T') := fun T' =>
    (isIso_iff_bijective _).1 inferInstance
  refine ⟨W, j, ⟨fun T' => (Equiv.ofBijective _ (hbij (op T'))).trans (r.equiv T'), fun s z => ?_⟩,
    hp.property_snd _, fun T' y => ?_⟩
  · refine (congrArg (r.equiv _) ?_).trans (r.naturality s _)
    exact NatTrans.naturality_apply φ s.op z
  · exact (congrArg (fun q => q.app (op T') y) hφ).symm.trans (hpt T' (φ.app _ y))

end AlgMag

#print axioms AlgMag.prop81FG
#print axioms AlgMag.prop81FG_of_scheme
#print axioms AlgMag.attractorFixedEquivOfCover
#print axioms AlgMag.extSieve_mem
#print axioms AlgMag.exists_closed_fixed
