/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.SpacesLimitFinal
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# Theorem A.1, case (ii): working on the site of a stage

Mayeux, *Algebraic Magnetism*, proof of Theorem A.1.

The hypothesis of the case with torsion does not hold on `Spec ℤ`, so the argument of case (i) runs on
the site of the stage.

* `exists_stage_torsion`, `torsionResidue_of_injective`: the torsion hypothesis passes from `R` to its
  subrings.
* `closed_of_site_stage`, `isFPR_of_site_stage`, `fp_of_closed_noetherian`: an action on `Y` over an object
  `T₀` of the site, invariant over `T₀`, gives the conclusions of Theorem A.1 when the hypotheses
  hold on `T₀`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.LimStage

open LimAct Space

noncomputable section

/-! ### The torsion hypothesis at a stage -/

section Torsion

variable {M : Type u} [AddCommGroup M]

/-- A prime `l`, nilpotent on `S`, whose powers kill the torsion of `M`, gives `TorsionResidue`. -/
theorem torsionResidue_of_nilpotent (S : Scheme.{u}) (l : ℕ) (hl : l.Prime)
    (hn : IsNilpotent ((l : ℕ) : Γ(S, ⊤)))
    (hN : ∀ m : M, IsOfFinAddOrder m → ∃ N : ℕ, l ^ N • m = 0) : TorsionResidue M S := by
  intro s q hq m hm
  have h0 : ((l : ℕ) : S.residueField s) = 0 := by
    have := hn.map (S.evaluation ⊤ s trivial).hom
    rw [map_natCast] at this
    exact this.eq_zero
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (S.residueField s) l := (CharP.charP_iff_prime_eq_zero hl).2 h0
  have hq' : q = l := hq.eq (ExpChar.prime hl)
  subst hq'
  exact hN m hm

private lemma cast_zero_of_expChar {K : Type*} [AddMonoidWithOne K] [Nontrivial K] {q : ℕ}
    (hp : q.Prime) (h : ExpChar K q) : ((q : ℕ) : K) = 0 := by
  cases h with
  | zero => exact absurd hp Nat.not_prime_one
  | prime _ => exact CharP.cast_eq_zero K q

/-- Two powers of different exponential characteristics cannot kill a nonzero element. -/
private lemma eq_of_kills {q q₀ a b : ℕ} (hq : q.Prime ∨ q = 1) (hq₀ : q₀.Prime) {m : M} (hm : m ≠ 0)
    (h : q ^ a • m = 0) (h₀ : q₀ ^ b • m = 0) : q = q₀ := by
  by_contra hne
  have hc : Nat.Coprime (q ^ a) (q₀ ^ b) := by
    refine Nat.Coprime.pow _ _ ?_
    rcases hq with hq | rfl
    · exact (Nat.coprime_primes hq hq₀).2 hne
    · exact Nat.coprime_one_left _
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h) (addOrderOf_dvd_of_nsmul_eq_zero h₀)
  rw [hc.gcd_eq_one, Nat.dvd_one, AddMonoid.addOrderOf_eq_one_iff] at h1
  exact hm h1

/-- **The torsion hypothesis of Theorem A.2 (ii) passes to a subring.** For `φ : A → R` an injective ring
homomorphism, `TorsionResidue M (Spec R)` implies `TorsionResidue M (Spec A)`: if `M` has nonzero torsion,
all residue characteristics of `R` are one prime `l`, so `l` is nilpotent in `R`, hence in `A`. -/
theorem torsionResidue_of_injective {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R)
    (hφ : Function.Injective φ) (h : TorsionResidue M (Spec (.of R))) :
    TorsionResidue M (Spec (.of A)) := by
  intro s q hq m hm
  by_cases hm0 : m = 0
  · exact ⟨0, by simp [hm0]⟩
  haveI : Nontrivial A := PrimeSpectrum.nontrivial (R := A) s
  haveI : Nontrivial R := hφ.nontrivial
  obtain ⟨x₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  let s₀ : Spec (.of R) := x₀
  obtain ⟨q₀, hq₀⟩ := ExpChar.exists ((Spec (.of R)).residueField s₀)
  obtain ⟨N₀, hN₀⟩ := h s₀ q₀ hq₀ m hm
  have hq₀1 : q₀ ≠ 1 := by
    rintro rfl
    simp only [one_pow, one_smul] at hN₀
    exact hm0 hN₀
  have hq₀p : q₀.Prime := (@expChar_is_prime_or_one _ _ q₀ hq₀).resolve_right hq₀1
  have hmem : ∀ P : PrimeSpectrum R, ((q₀ : ℕ) : R) ∈ P.asIdeal := by
    intro P
    let x : Spec (.of R) := P
    obtain ⟨q', hq'⟩ := ExpChar.exists ((Spec (.of R)).residueField x)
    obtain ⟨N', hN'⟩ := h x q' hq' m hm
    have e : q' = q₀ := eq_of_kills (@expChar_is_prime_or_one _ _ q' hq') hq₀p hm0 hN' hN₀
    subst e
    have h0 : ((q' : ℕ) : (Spec (.of R)).residueField x) = 0 := cast_zero_of_expChar hq₀p hq'
    have h1 : ((Spec (.of R)).evaluation ⊤ x trivial).hom
        ((Scheme.ΓSpecIso (.of R)).inv ((q' : ℕ) : R)) = 0 := by
      rw [map_natCast, map_natCast]
      exact h0
    have h2 := ((Spec (.of R)).evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) x trivial _).1 h1
    rw [basicOpen_eq_of_affine] at h2
    exact not_not.1 fun hc => h2 hc
  have hnil : IsNilpotent ((q₀ : ℕ) : R) := by
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro I hI
    exact hmem ⟨I, hI⟩
  obtain ⟨K, hK⟩ := hnil
  have hA : IsNilpotent ((q₀ : ℕ) : A) := ⟨K, hφ (by simpa using hK)⟩
  have hnΓ : IsNilpotent ((q₀ : ℕ) : Γ(Spec (.of A), ⊤)) := by
    have := hA.map ((Scheme.ΓSpecIso (.of A)).inv).hom
    rwa [map_natCast] at this
  exact torsionResidue_of_nilpotent (M := M) _ q₀ hq₀p hnΓ (fun m' hm' => h s₀ q₀ hq₀ m' hm')
    s q hq m hm

/-- **Stage form.** Under `TorsionResidue M (Spec R)`, the hypothesis holds on all stages `Spec ℤ[i]`. -/
theorem exists_stage_torsion {R : Type u} [CommRing R] (h : TorsionResidue M (Spec (.of R))) :
    ∃ i₀ : Finset R, ∀ i : Finset R, i₀ ⊆ i →
      TorsionResidue M (Spec (.of (Algebra.adjoin ℤ (i : Set R)))) :=
  ⟨∅, fun i _ => torsionResidue_of_injective
    (Algebra.adjoin ℤ (i : Set R)).val.toRingHom Subtype.val_injective h⟩

end Torsion

/-! ### Descent of the action to the site of an object -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {M : Type u} [AddCommGroup M]
variable (T₀ : BigFppfOver B S hS) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre of `p : Y → h_{T₀}` over the identity: `Y` as a presheaf on the site of `T₀`. -/
abbrev Fib (p : Y ⟶ yoneda.obj T₀) : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ ⥤ Type u :=
  OverShriek.fibreOfSection T₀.hom p (𝟙 (yoneda.obj T₀))

/-- `Λ` of the fibre. -/
abbrev Lam {F G : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ ⥤ Type u} (k : F ⟶ G) :=
  (OverShriek.relocalizePresheafFunctor T₀.hom).map k

variable {T₀} (p : Y ⟶ yoneda.obj T₀)

/-- The comparison `Λ (Fib p) → Y`. -/
abbrev cmp : (OverShriek.relocalizePresheafFunctor T₀.hom).obj (Fib T₀ p) ⟶ Y :=
  OverShriek.relocalizeFibreOfSectionMap T₀.hom p (𝟙 (yoneda.obj T₀))

instance isIso_cmp : IsIso (cmp p) :=
  @IsPullback.isIso_fst_of_isIso _ _ _ _ _ _ _ _ _ _
    (OverShriek.isPullback_relocalizeFibreOfSectionMap T₀.hom p (𝟙 (yoneda.obj T₀))) (IsIso.id _)

theorem isAlgebraicSpace_fib (hY : IsAlgebraicSpace B S hS Y) :
    IsAlgebraicSpace B T₀.left.1 T₀.left.2 (Fib T₀ p) :=
  isAlgebraicSpace_fibreOfSection B S hS T₀ p (𝟙 _)
    (isAlgebraicSpace_of_iso B S hS (asIso (pullback.snd (𝟙 (yoneda.obj T₀)) p)).symm hY)

variable {p}

/-- Every point of `Y` is a point of the fibre, over the factorization it carries. -/
lemma exists_fib {W : BigFppfOver B S hS} (x : Y.obj (op W)) :
    ∃ (ψ : W.left ⟶ T₀.left) (hψ : ψ ≫ T₀.hom = W.hom) (s : (Fib T₀ p).obj (op (Over.mk ψ))),
      Y.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1 = x := by
  let v : W ⟶ T₀ := p.app (op W) x
  have hv : v.left ≫ T₀.hom = W.hom := Over.w v
  refine ⟨v.left, hv, ⟨Y.map (OverShriek.overMapMkIso T₀.hom hv).inv.op x, ?_⟩,
    OverShriek.map_overMapMkIso_hom_inv T₀.hom Y hv x⟩
  refine (NatTrans.naturality_apply p (OverShriek.overMapMkIso T₀.hom hv).inv.op x).trans ?_
  exact Over.OverMorphism.ext (Category.id_comp v.left)

variable {act : AAction (fppfO B S hS) M Y}

/-- A point of `D(M)` over the site of `T₀` is a point of `D(M)` over the site of `S`. -/
def cv {U : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ} (h : APt (fppfO B T₀.left.1 T₀.left.2) M U) :
    APt (fppfO B S hS) M (op ((Over.map T₀.hom).obj U.unop)) := h

lemma cv_one {U : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ} :
    cv (1 : APt (fppfO B T₀.left.1 T₀.left.2) M U) = 1 := MonoidHom.ext fun _ => rfl

lemma cv_mul {U : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ}
    (g h : APt (fppfO B T₀.left.1 T₀.left.2) M U) : cv (g * h) = cv g * cv h :=
  MonoidHom.ext fun _ => rfl

lemma cv_res {U V : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ} (f : U ⟶ V)
    (h : APt (fppfO B T₀.left.1 T₀.left.2) M U) :
    cv (APt.res f h) = APt.res ((Over.map T₀.hom).map f.unop).op (cv h) :=
  MonoidHom.ext fun _ => rfl

/-- The action on the fibre. -/
def descAct (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x) :
    AAction (fppfO B T₀.left.1 T₀.left.2) M (Fib T₀ p) where
  smul {U} h s := ⟨act.smul (cv h) s.1, (hinv _ _).trans s.2⟩
  one_smul x := Subtype.ext (by rw [cv_one]; exact act.one_smul x.1)
  mul_smul g h x := Subtype.ext (by rw [cv_mul]; exact act.mul_smul (cv g) (cv h) x.1)
  map_smul f h x := Subtype.ext (by
    rw [cv_res]; exact act.map_smul ((Over.map T₀.hom).map f.unop).op (cv h) x.1)

variable (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T),
  p.app T (act.smul h x) = p.app T x)

/-- A point of the fibre is fixed iff it is fixed as a point of `Y`. -/
lemma mem_fix_iff {T' : (BigFppfOver B T₀.left.1 T₀.left.2)ᵒᵖ} (x : (Fib T₀ p).obj T') :
    x ∈ (fixedPoints (descAct act hinv)).obj T' ↔
      x.1 ∈ (fixedPoints act).obj (op ((Over.map T₀.hom).obj T'.unop)) := by
  constructor
  · intro hx T₂ s h
    let W := T₂.unop
    let ψ : W.left ⟶ T'.unop.left := s.unop.left
    let U' : Over T₀.left := Over.mk (ψ ≫ T'.unop.hom)
    let g : U' ⟶ T'.unop := Over.homMk ψ rfl
    have hψ : (ψ ≫ T'.unop.hom) ≫ T₀.hom = W.hom := by
      have := Over.w s.unop
      simpa [Category.assoc] using this
    let e := OverShriek.overMapMkIso T₀.hom hψ
    have hs : s = ((Over.map T₀.hom).map g).op ≫ e.hom.op := by
      refine Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_)
      simp [e, g, ψ]
    let h' : APt (fppfO B S hS) M (op ((Over.map T₀.hom).obj U')) := APt.res e.inv.op h
    have key : act.smul h' (Y.map ((Over.map T₀.hom).map g).op x.1) =
        Y.map ((Over.map T₀.hom).map g).op x.1 :=
      congrArg Subtype.val (hx g.op (show APt (fppfO B T₀.left.1 T₀.left.2) M (op U') from h'))
    have hh : APt.res e.hom.op h' = h := by
      rw [← APt.res_comp, ← op_comp, e.hom_inv_id]
      simp
    rw [hs, Functor.map_comp_apply, ← hh, ← act.map_smul, key]
  · intro hx T₂ s h
    exact Subtype.ext (hx ((Over.map T₀.hom).map s.unop).op (cv h))

include hinv in
/-- `Y^{D(M)}` is the extension of the fixed points of the fibre. -/
theorem closed_of_fib
    (h₀ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B T₀.left.1 T₀.left.2))) (fixedPoints (descAct act hinv)).ι) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (fixedPoints act).ι := by
  let ι₀ := (fixedPoints (descAct act hinv)).ι
  have hΛ := presheaf_relocalizeMap B T₀.left.1 S T₀.left.2 hS T₀.hom
    (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ι₀ h₀
  have hrange : Subfunctor.range (Lam T₀ ι₀ ≫ cmp p) ≤ fixedPoints act := by
    rintro W _ ⟨⟨⟨ψ, s⟩, hx⟩, rfl⟩
    have hs : s.1.1 ∈ (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
      (mem_fix_iff hinv s.1).1 (by exact s.2)
    have h9 : Y.map (OverShriek.overMapMkIso T₀.hom (W := W.unop) hx).hom.op s.1.1 ∈
        (fixedPoints act).obj W := (fixedPoints act).map _ hs
    exact @h9
  let d := Subfunctor.lift (Lam T₀ ι₀ ≫ cmp p) hrange
  have hd : IsIso d := by
    refine (NatTrans.isIso_iff_isIso_app _).2 fun W => ?_
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
    · rintro ⟨⟨ψ, s⟩, hx⟩ ⟨⟨ψ', s'⟩, hx'⟩ hdd
      have h1 : (Lam T₀ ι₀ ≫ cmp p).app W ⟨⟨ψ, s⟩, hx⟩ = (Lam T₀ ι₀ ≫ cmp p).app W ⟨⟨ψ', s'⟩, hx'⟩ :=
        congrArg Subtype.val hdd
      have hinj : Function.Injective ((cmp p).app W) :=
        ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
      have h2 := hinj h1
      have h3 := congrArg Subtype.val h2
      obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.1 h3
      have h5 : s = s' := Subtype.ext (eq_of_heq h4)
      subst h5
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨ψ, hψ, s, rfl⟩ := exists_fib (p := p) y
      have hs1 : s.1 ∈ (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) := by
        have : Y.map (OverShriek.overMapMkIso T₀.hom hψ).inv.op
            (Y.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1) ∈
            (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
          (fixedPoints act).map (OverShriek.overMapMkIso T₀.hom hψ).inv.op hy
        rwa [OverShriek.map_overMapMkIso_inv_hom] at this
      refine ⟨⟨⟨ψ, ⟨s, (mem_fix_iff hinv s).2 hs1⟩⟩, hψ⟩, ?_⟩
      exact Subtype.ext rfl
  have e : (fixedPoints act).ι = inv d ≫ Lam T₀ ι₀ ≫ cmp p := by
    rw [IsIso.eq_inv_comp]
    exact Subfunctor.lift_ι _ _
  have hst : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : MorphismProperty.RespectsIso (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [e]
  exact (MorphismProperty.cancel_left_of_respectsIso _ (inv d) _).2
    ((MorphismProperty.cancel_right_of_respectsIso _ _ (cmp p)).2 hΛ)

abbrev EtP (S' : Scheme.{u}) (h' : B.Contains S') :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S' h'))

lemma respects_etP (S' : Scheme.{u}) (h' : B.Contains S') :
    MorphismProperty.RespectsIso (EtP (B := B) S' h') :=
  have : (EtP (B := B) S' h').IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  MorphismProperty.IsStableUnderBaseChange.respectsIso

omit [AddCommGroup M] in
/-- Charts of the fibre are of finite type over `T₀`. -/
theorem charts_fib (p : Y ⟶ yoneda.obj T₀) (hC : ChartsOfFiniteType Y) :
    ChartsOfFiniteType (Fib T₀ p) := by
  intro V φ he
  have h1 := (presheaf_relocalizeChart_iff B T₀.left.1 S T₀.left.2 hS T₀.hom
    (@Etale.{u} : MorphismProperty Scheme.{u}) φ).2 he
  have := respects_etP (B := B) S hS
  have h2 : EtP (B := B) S hS (relocalizeChart B T₀.left.1 S T₀.left.2 hS T₀.hom φ ≫ cmp p) :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).2 h1
  have h3 := hC _ _ h2
  exact LocallyOfFiniteType.of_comp (g := T₀.hom.hom) h3

/-- **Theorem A.1, closedness, on the site of `T₀`.** -/
theorem closed_of_site_stage [AddGroup.FG M] [IsLocallyNoetherian T₀.left.1]
    (p : Y ⟶ yoneda.obj T₀) (hY : IsAlgebraicSpace B S hS Y) (hC : ChartsOfFiniteType Y)
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x)
    (hT : TorsionResidue M T₀.left.1) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)))
        (fixedPoints act).ι :=
  closed_of_fib hinv (AppA3.thmA1_closed (isAlgebraicSpace_fib p hY) (charts_fib p hC) _ hT)

/-- **Theorem A.1, fixed point reflection, on the site of `T₀`.** -/
theorem isFPR_of_site_stage [AddGroup.FG M] [IsLocallyNoetherian T₀.left.1]
    (p : Y ⟶ yoneda.obj T₀) (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hCU : ChartsOfFiniteType U) {actU : AAction (fppfO B S hS) M U} {u' : U ⟶ Y}
    (hu : IsEquivariant actU act u') (het : EtP (B := B) S hS u')
    (hT : TorsionResidue M T₀.left.1) : IsFPR hu := by
  have hinvU : ∀ {T} (h : APt (fppfO B S hS) M T) (x : U.obj T),
      (u' ≫ p).app T (actU.smul h x) = (u' ≫ p).app T x := fun {T} h x => by
    change p.app T (u'.app T (actU.smul h x)) = p.app T (u'.app T x)
    rw [hu h x, hinv]
  let u₀ : Fib T₀ (u' ≫ p) ⟶ Fib T₀ p :=
    { app := fun W => ↾fun s => ⟨u'.app _ s.1, s.2⟩
      naturality := fun W W' g => tex fun s => Subtype.ext (by
        change u'.app _ (U.map ((Over.map T₀.hom).map g.unop).op s.1) =
          Y.map ((Over.map T₀.hom).map g.unop).op (u'.app _ s.1)
        exact NatTrans.naturality_apply u' ((Over.map T₀.hom).map g.unop).op s.1) }
  have hu₀ : IsEquivariant (descAct actU hinvU) (descAct act hinv) u₀ :=
    fun h x => Subtype.ext (hu (cv h) x.1)
  have hcomm : Lam T₀ u₀ ≫ cmp p = cmp (u' ≫ p) ≫ u' := by
    refine pex fun W x => ?_
    obtain ⟨⟨ψ, s⟩, hx⟩ := x
    exact (NatTrans.naturality_apply u' (OverShriek.overMapMkIso T₀.hom hx).hom.op s.1).symm
  have := respects_etP (B := B) S hS
  have hΛ : EtP (B := B) S hS (Lam T₀ u₀) := by
    refine (MorphismProperty.cancel_right_of_respectsIso _ _ (cmp p)).1 ?_
    rw [hcomm]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 het
  have het₀ := presheaf_relocalizeMap_of B T₀.left.1 S T₀.left.2 hS T₀.hom
    (@Etale.{u} : MorphismProperty Scheme.{u}) u₀ hΛ
  have hfpr := AppA3.thmA1_isFPR (isAlgebraicSpace_fib (u' ≫ p) hU) (charts_fib (u' ≫ p) hCU)
    hT hu₀ het₀
  refine (isFPR_iff hu).2 fun T x hx => ?_
  obtain ⟨ψ, hψ, s, rfl⟩ := exists_fib (p := u' ≫ p) (W := T.unop) x
  have hx' : u'.app _ s.1 ∈ (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) := by
    have h1 : Y.map (OverShriek.overMapMkIso T₀.hom hψ).inv.op
        (u'.app _ (U.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1)) ∈
        (fixedPoints act).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
      (fixedPoints act).map (OverShriek.overMapMkIso T₀.hom hψ).inv.op hx
    have e : Y.map (OverShriek.overMapMkIso T₀.hom hψ).inv.op
        (u'.app _ (U.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1)) = u'.app _ s.1 := by
      rw [NatTrans.naturality_apply u' (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1,
        OverShriek.map_overMapMkIso_inv_hom]
    rw [← e]
    exact @h1
  have h2 : s ∈ (fixedPoints (descAct actU hinvU)).obj (op (Over.mk ψ)) :=
    (isFPR_iff hu₀).1 hfpr _ s ((mem_fix_iff hinv (u₀.app _ s)).2 hx')
  have h3 : s.1 ∈ (fixedPoints actU).obj (op ((Over.map T₀.hom).obj (Over.mk ψ))) :=
    (mem_fix_iff hinvU s).1 h2
  have h4 : U.map (OverShriek.overMapMkIso T₀.hom hψ).hom.op s.1 ∈ (fixedPoints actU).obj T :=
    (fixedPoints actU).map _ h3
  exact @h4

/-- **Theorem A.1, "of finite presentation".** A closed immersion into `Y`, with `Y` over the locally
noetherian `T₀` with charts of finite type, is of finite presentation. -/
theorem fp_of_closed_noetherian [IsLocallyNoetherian T₀.left.1]
    (p : Y ⟶ yoneda.obj T₀) (hY : IsAlgebraicSpace B S hS Y) (hC : ChartsOfFiniteType Y)
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : Z ⟶ Y) (hi : Space.IsClosedImmersion B S hS i) :
    Space.IsFinitePresentation B S hS i := by
  refine ⟨?_, isQuasiCompact_of_isClosedImmersion' B S hS hi,
    isQuasiSeparated_of_isClosedImmersion B S hS hi⟩
  refine holdsOnEveryEtaleChart_of_surjectiveChart B S hS _
    LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget ?_
  obtain ⟨V, b, hbSurj, hbEt⟩ := hY.exists_atlas
  refine ⟨_, V, hi.rep.fst b, b, hi.rep.snd b,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hi.rep.isPullback b).flip hbEt, hbEt,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hi.rep.isPullback b).flip hbSurj, ((hi.rep.isPullback b).w).symm, ?_⟩
  have hl : LocallyOfFiniteType V.hom.hom := hC V b hbEt
  let v : V ⟶ T₀ := yoneda.preimage (b ≫ p)
  have hv : v.left.hom ≫ T₀.hom.hom = V.hom.hom := congrArg (fun f => f.hom) (Over.w v)
  have hl' : LocallyOfFiniteType v.left.hom := by
    rw [← hv] at hl
    exact LocallyOfFiniteType.of_comp (g := T₀.hom.hom) hl
  have hN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := T₀.left.1) v.left.hom
  have hc : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (hi.rep.snd b)) :=
    hi.property_snd b
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance

/-- **Theorem A.1**: the fixed points are a closed immersion of finite presentation. -/
theorem fixedPoints_fp_of_site_stage [AddGroup.FG M] [IsLocallyNoetherian T₀.left.1]
    (p : Y ⟶ yoneda.obj T₀) (hY : IsAlgebraicSpace B S hS Y) (hC : ChartsOfFiniteType Y)
    (act : AAction (fppfO B S hS) M Y)
    (hinv : ∀ {T} (h : APt (fppfO B S hS) M T) (x : Y.obj T), p.app T (act.smul h x) = p.app T x)
    (hT : TorsionResidue M T₀.left.1) :
    Space.IsFinitePresentation B S hS (fixedPoints act).ι :=
  fp_of_closed_noetherian p hY hC _ (closed_of_site_stage p hY hC act hinv hT)

end Site

end

end AlgMag.LimStage

#print axioms AlgMag.LimStage.exists_stage_torsion
#print axioms AlgMag.LimStage.closed_of_site_stage
#print axioms AlgMag.LimStage.isFPR_of_site_stage
#print axioms AlgMag.LimStage.fixedPoints_fp_of_site_stage
