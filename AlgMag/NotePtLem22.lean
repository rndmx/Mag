/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.NotePtLem21
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection

/-!
# Existence of strongly-FPR atlases: Lemma 2.2 over `|X|`

Mayeux, *Existence of strongly-FPR atlases* (no journal version), Lemma 2.2.

`AlgMag.NotePt.lem22_points`: as `x` ranges over `|X|`, `Y_x` takes finitely many values. As printed: `V → X` is étale surjective
with `V` affine, the stabilizer group `𝔊_V ⊆ D(M)_V` has fibre `G_x` at `v ↦ x`
(`AlgMag.NotePt.stabY_eq_charSet_map`, `AlgMag.NotePt.stabY_eq_charAt`), and the noetherian induction is
`AlgMag.StronglyFPRNote.lem22`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgMag.NotePt

open AlgMag.StronglyFPR AlgMag.StronglyFPRNote AlgMag.StronglyFPRNote.SubgroupIdeal

noncomputable section

section Ring

variable {M : Type*} [AddCommGroup M]

/-- `Y` of a subgroup over a field does not change under field extension. -/
theorem charSet_map_field {K L : Type*} [Field K] [Field L] (ι : K →+* L) {J : Ideal (AddMonoidAlgebra K M)}
    (h : IsSubgroupIdeal J) : charSet (J.map (baseMap ι M)) = charSet J := by
  have e : J = spanY K (charSet J) := le_antisymm (le_span h) (by
    rw [spanY, Ideal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hm)
  have e2 : J.map (baseMap ι M) = spanY L (charSet J) := by
    conv_lhs => rw [e]
    exact map_spanY ι _
  rw [e2]
  ext m
  constructor
  · intro hm
    exact mem_of_chi_mem (charSub J) hm
  · intro hm
    exact Ideal.subset_span ⟨m, hm, rfl⟩

/-- The fibre at a point of `Spec R`, computed in any field with that kernel, is `charAt`. -/
theorem charSet_map_eq_charAt {R L : Type*} [CommRing R] [Field L] (ψ : R →+* L) (hp : (RingHom.ker ψ).IsPrime)
    {I : Ideal (AddMonoidAlgebra R M)} (h : IsSubgroupIdeal I) :
    charSet (I.map (baseMap ψ M)) = charAt I ⟨RingHom.ker ψ, hp⟩ := by
  let p : Ideal R := RingHom.ker ψ
  haveI : p.IsPrime := hp
  let ι : p.ResidueField →+* L := Ideal.ResidueField.lift p ψ le_rfl (fun x hx => by
    change IsUnit (ψ x)
    exact isUnit_iff_ne_zero.2 hx)
  have hc : (baseMap ι M).comp (baseMap (algebraMap R p.ResidueField) M) = baseMap ψ M := by
    refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · simp [ι, Ideal.ResidueField.lift_algebraMap]
    · simp
  have e : I.map (baseMap ψ M) = (I.map (baseMap (algebraMap R p.ResidueField) M)).map (baseMap ι M) := by
    rw [Ideal.map_map, hc]
  rw [e]
  exact charSet_map_field ι (IsSubgroupIdeal.map _ h)

end Ring

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

section Fibre

variable {V P : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  {act : AAction (fppfO B S hS) M X} {x : X.obj (op V)}

lemma specRing_comp {T : BigFppfOver B S hS} (t : T ⟶ P) (s : P ⟶ V) (k : APt (fppfO B S hS) M (op T)) :
    (specRing t k).comp (baseMap ((SCH).map s).appTop.hom M) = specRing (t ≫ s) k := by
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
  · simp only [RingHom.comp_apply, baseMap_single, specRing_single, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  · simp only [RingHom.comp_apply, baseMap_single, specRing_single, map_one]

/-- The stabilizer group of `x ∈ X(V)` has fibre `G` at the field-valued point `s : P → V`: `I_P = I ⊗ κ` is the ideal
of the stabilizer of `s^* x`, whence `Y_{s^* x} = {m | χ^m - 1 ∈ I_P}`. -/
theorem stabY_eq_charSet_map (D : StabIdeal act x) (s : P ⟶ V) (hP : IsField Γ((SCH).obj P, ⊤)) :
    (stabY act (X.map s.op x) : Set M) = charSet (D.I.map (baseMap ((SCH).map s).appTop.hom M)) := by
  let ψ := ((SCH).map s).appTop.hom
  let J := D.I.map (baseMap ψ M)
  have hJ : IsSubgroupIdeal J := IsSubgroupIdeal.map ψ D.isSubgroupIdeal
  have hmap : ∀ {T : BigFppfOver B S hS} (t : T ⟶ P), X.map t.op (X.map s.op x) = X.map (t ≫ s).op x := by
    intro T t
    rw [op_comp, Functor.map_comp_apply]
  apply Set.Subset.antisymm
  · intro m hm
    let _ : Field Γ((SCH).obj P, ⊤) := hP.toField
    let Y : AddSubgroup M := charSub J
    have hne : Nontrivial Γ((SCH).obj P, ⊤) := ⟨hP.exists_pair_ne⟩
    refine (show m ∈ Y from ?_)
    refine specPt_quot_eq_one (V := P) Y m ?_
    let k : APt (fppfO B S hS) M (op (specObj (M ⧸ Y) P)) :=
      (specPt (M ⧸ Y) P).comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Y))
    refine hm (specPr (M ⧸ Y) P) k ?_
    rw [hmap]
    refine D.fix_of_kills _ k fun y hy => ?_
    rw [← specRing_comp]
    have h1 : baseMap ψ M y ∈ spanY Γ((SCH).obj P, ⊤) (Y : Set M) :=
      le_span hJ (Ideal.mem_map_of_mem _ hy)
    have hle : spanY Γ((SCH).obj P, ⊤) (Y : Set M) ≤ RingHom.ker (specRing (specPr (M ⧸ Y) P) k) := by
      rw [spanY, Ideal.span_le]
      rintro _ ⟨n, hn, rfl⟩
      refine (specRing_chi_sub _ k n).2 ?_
      have h0 : QuotientAddGroup.mk' Y n = 0 := (QuotientAddGroup.eq_zero_iff n).2 hn
      change (specPt (M ⧸ Y) P) (Multiplicative.ofAdd (QuotientAddGroup.mk' Y n)) = 1
      rw [h0]
      exact map_one (specPt (M ⧸ Y) P)
    exact hle h1
  · intro m hm T t k hk
    rw [hmap] at hk
    have hle : J ≤ RingHom.ker (specRing t k) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      have e := congrArg (fun φ => φ y) (specRing_comp t s k)
      change specRing t k (baseMap ψ M y) = 0
      exact e.trans (D.kills _ k hk hy)
    exact (specRing_chi_sub t k m).1 (hle hm)

/-- `Y_v` is the fibre of the stabilizer group: `Y_{s^* x} = charAt I v`, for `v` the image of `s`. -/
theorem stabY_eq_charAt (D : StabIdeal act x) (s : P ⟶ V) (hP : IsField Γ((SCH).obj P, ⊤))
    (hp : (RingHom.ker ((SCH).map s).appTop.hom).IsPrime) :
    (stabY act (X.map s.op x) : Set M) = charAt D.I ⟨RingHom.ker ((SCH).map s).appTop.hom, hp⟩ := by
  rw [stabY_eq_charSet_map D s hP]
  let _ : Field Γ((SCH).obj P, ⊤) := hP.toField
  exact charSet_map_eq_charAt _ hp D.isSubgroupIdeal

end Fibre

/-- `X` of finite type over `S` affine is quasi-compact. -/
theorem qc_of_finiteType [IsAffine S] (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X)) : Space.IsQuasiCompactSpace B S hS X := by
  let T1 : BigFppfOver B S hS := Over.mk (𝟙 _)
  have hT : IsTerminal (yoneda.obj T1) := (Over.mkIdTerminal).isTerminalObj yoneda _
  haveI : IsAffine ((SCH).obj T1) := inferInstanceAs (IsAffine S)
  have hq : Space.IsQuasiCompactSpace B S hS (yoneda.obj T1) :=
    Space.isQuasiCompact_yoneda_of_compact B S hS T1 inferInstance
  have h := hft.2 (yoneda.obj T1) (isAlgebraicSpace_yoneda B S hS _) hq (terminal.from _)
  haveI : IsIso (terminal.from (yoneda.obj T1)) :=
    ⟨hT.from _, hT.hom_ext _ _, terminal.hom_ext _ _⟩
  have hpb : IsAlgebraicSpace B S hS (pullback (terminal.from (yoneda.obj T1)) (terminal.from X)) :=
    Space.isAlgebraicSpace_of_iso B S hS (asIso (pullback.snd _ _)).symm hX
  exact Space.IsQuasiCompactSpace.of_isSurjective B S hS hpb hX
    (Space.pointsMap_surjective_of_isIso B S hS (pullback.snd _ _)) h

/-- **Lemma 2.2.** `S` affine of finite type over `ℤ`, `X` separated of finite type over `S`, `M` finitely generated: as `x`
ranges over `|X|`, `Y_x` takes finitely many values. -/
theorem lem22_points [AddGroup.FG M] [IsAffine S] (hSft : LocallyOfFiniteType (terminal.from S))
    (hX : IsAlgebraicSpace B S hS X) (hsep : Space.IsSeparatedOver B S hS X)
    (hft : Space.IsFiniteType B S hS (terminal.from X)) (act : AAction (fppfO B S hS) M X) :
    (Set.range (stabPt act hsep)).Finite := by
  obtain ⟨V, φ, hV, hsurj, hE⟩ := (Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X hX).1
    (qc_of_finiteType hX hft)
  have he := Space.presheaf_etale_of_isEtale B S hS hE
  haveI := hV
  haveI : IsNoetherianRing Γ((SCH).obj V, ⊤) := isNoetherianRing_chart hSft hft he
  let x : X.obj (op V) := φ.app (op V) (𝟙 V)
  obtain ⟨D⟩ := nonempty_stabIdeal act hsep x
  have hfin := finite_range D.I D.isSubgroupIdeal
  let c : AddSubgroup M → Set M := fun Y => (Y : Set M)
  have hinj : Function.Injective c := fun A A' h => SetLike.coe_injective h
  refine Set.Finite.of_finite_image (f := c) (hfin.subset ?_) hinj.injOn
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  obtain ⟨v, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS φ hsurj w
  induction v using Quot.ind with
  | mk r =>
  let s : r.siteObject ⟶ V := r.value
  have hP := fvp_isField r
  have hpr : (RingHom.ker ((SCH).map s).appTop.hom).IsPrime := by
    let _ : Field Γ((SCH).obj r.siteObject, ⊤) := hP.toField
    exact RingHom.ker_isPrime _
  refine ⟨⟨_, hpr⟩, ?_⟩
  have e : φ.app (op r.siteObject) r.value = X.map s.op x := by
    have := NatTrans.naturality_apply φ s.op (𝟙 V)
    refine Eq.trans ?_ this
    congr 1
  have h2 : stabPt act hsep (Space.pointsMap B S hS _ φ (r.class B S hS _)) =
      stabY act (X.map s.op x) := by
    rw [Space.pointsMap_class, stabPt_class]
    exact congrArg _ e
  change _ = c _
  simp only [c]
  rw [h2]
  exact (stabY_eq_charAt D s hP hpr).symm

end

end AlgMag.NotePt

#print axioms AlgMag.NotePt.stabY_eq_charAt
#print axioms AlgMag.NotePt.lem22_points
