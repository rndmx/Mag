/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec6FPR
import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# Zariski locally linearizable actions

Mayeux, *Algebraic Magnetism*, Semigroup Forum 113 (2026) 126–201, §7.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u v

namespace AlgMag

section General

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
variable {M : Type*} [AddCommGroup M] {U X : Cᵒᵖ ⥤ Type u}
  {actU : AAction 𝒪 M U} {actX : AAction 𝒪 M X} {f : U ⟶ X}

/-- **Fact 7.1**, the assertion of its proof: an equivariant monomorphism of functors is `Z`-FPR for
every subgroup `Z`, i.e. `U^{D(M/Z)} = X^{D(M/Z)} ×_X U`. In particular this applies to
equivariant open immersions. -/
theorem isZFPR_of_mono (hf : IsEquivariant actU actX f) [Mono f] (Z : AddSubgroup M) :
    IsZFPR hf Z := by
  refine (isFPR_iff (hf.comap (QuotientAddGroup.mk' Z))).mpr fun T x hx T' s h => ?_
  have hinj : Function.Injective (f.app T') :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance T')
  apply hinj
  have e := hf.comap (QuotientAddGroup.mk' Z) h (U.map s x)
  refine e.trans ?_
  rw [NatTrans.naturality_apply]
  exact hx s h

/-- **Fact 7.1.** Every `D(M)_S`-equivariant monomorphism, so every equivariant open immersion, is
strongly-FPR. -/
theorem isStronglyFPR_of_mono (hf : IsEquivariant actU actX f) [Mono f] : IsStronglyFPR hf :=
  fun Z => isZFPR_of_mono hf Z

end General

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type w} [AddCommGroup M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Definition 7.2.** The action of `D(M)_S` on `X` is Zariski locally linearizable (a Sumihiro
action): `X` is covered by `S`-affine open `D(M)_S`-stable subspaces `j a : U a → X`. The stable open
subspaces are given by equivariant open immersions from `S`-affine schemes; covering means that the
pulled back open subschemes cover every `T` over `X`. -/
structure ZariskiLocallyLinearizable (actX : AAction (fppfO B S hS) M X) (A : Type u)
    (U : A → BigFppfOver B S hS) where
  /-- The action on each open subspace. -/
  act : ∀ a, AAction (fppfO B S hS) M (yoneda.obj (U a))
  /-- The inclusion in `X`. -/
  j : ∀ a, yoneda.obj (U a) ⟶ X
  equivariant : ∀ a, IsEquivariant (act a) actX (j a)
  isOpen : ∀ a, (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (j a)
  isAffineHom : ∀ a, IsAffineHom (structMap (U a))
  covers : ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X) (t : (BigFppfOver.toScheme B S hS).obj T),
    ∃ a, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((isOpen a).rep.snd x))

omit [AddCommGroup M] in
lemma fixed_restrict [AddCommMonoid M] {U O W : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
    {f : yoneda.obj U ⟶ X} (hf : IsEquivariant actU actX f) (i : O ⟶ W) (c : W ⟶ U)
    (k : APt (fppfO B S hS) M (op W)) (hfix : actX.smul k (f.app (op W) c) = f.app (op W) c) :
    f.app (op O) (actU.smul (APt.res i.op k) (i ≫ c)) = f.app (op O) (i ≫ c) := by
  have e : f.app (op O) (i ≫ c) = X.map i.op (f.app (op W) c) :=
    NatTrans.naturality_apply f i.op c
  rw [hf, e, ← actX.map_smul, hfix]

/-- The FPR part of **Fact 7.3**, including the step left implicit in the paper's proof: `f : U → X`
is not a monomorphism, but `U` is a disjoint union of stable opens on which `f` is injective on
points. Then `f` is strongly-FPR. -/
theorem isStronglyFPR_of_decomposition {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
    {f : yoneda.obj U ⟶ X} (hf : IsEquivariant actU actX f) {A : Type u}
    {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens} (hV : IsAffineDecomposition actU V)
    (hinj : ∀ (a : A) {T : BigFppfOver B S hS} (t t' : T ⟶ U),
      Set.range ((BigFppfOver.toScheme B S hS).map t) ⊆ V a →
      Set.range ((BigFppfOver.toScheme B S hS).map t') ⊆ V a →
      f.app (op T) t = f.app (op T) t' → t = t') :
    IsStronglyFPR hf := by
  intro Z
  refine (isFPR_iff (hf.comap (QuotientAddGroup.mk' Z))).mpr fun T x hx T' s h => ?_
  let W := unop T'
  let c : W ⟶ U := (yoneda.obj U).map s x
  let k := h.comp (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' Z))
  change actU.smul k c = c
  let toS := BigFppfOver.toScheme B S hS
  have hfix : actX.smul k (f.app T' c) = f.app T' c := by
    have := hx s h
    rw [← NatTrans.naturality_apply] at this
    exact this
  -- the opens of `W` over which we compare
  let Wa : A → (toS.obj W).Opens := fun a => toS.map c ⁻¹ᵁ V a
  have hcov : ⨆ a, Wa a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hV.iSup_eq_top]
    rfl
  have hsize : ∀ a, B.Contains ((Wa a : (toS.obj W).Opens) : Scheme.{u}) := fun a =>
    lt_of_le_of_lt (Scheme.size_coe_opens_le _ _) W.left.2
  let obj : A → BigFppfOver B S hS := fun a =>
    siteObject B S hS (hsize a) ((Wa a).ι ≫ structMap W)
  let inc : ∀ a, obj a ⟶ W := fun a => Over.homMk (ObjectProperty.homMk (Wa a).ι) rfl
  have hloc : ∀ a, inc a ≫ actU.smul k c = inc a ≫ c := by
    intro a
    have hr : Set.range (toS.map (inc a ≫ c)) ⊆ V a := by
      rintro _ ⟨y, rfl⟩
      have hy : toS.map c ((Wa a).ι y) ∈ V a := y.2
      exact hy
    have hsm : inc a ≫ actU.smul k c =
        actU.smul (APt.res (inc a).op k) (inc a ≫ c) := actU.map_smul (inc a).op k c
    rw [hsm]
    refine hinj a _ _ (hV.stable a (inc a ≫ c) _ hr) hr ?_
    exact fixed_restrict hf (inc a) c k hfix
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine (Scheme.openCoverOfIsOpenCover (toS.obj W) Wa hcov).hom_ext _ _ fun a => ?_
  exact congrArg toS.map (hloc a)

/-- **Fact 7.3**, FPR part, for the disjoint union of a Sumihiro cover: an equivariant atlas
`f : U → X`, with `U` the disjoint union of opens on which `f` is injective on points, is a
strongly-FPR equivariant atlas. The existence of `U`, with its action and the atlas property, is the
remaining content of Fact 7.3 (not proved here). -/
theorem isStronglyFPRAtlas_of_decomposition {U : BigFppfOver B S hS}
    {actU : AAction (fppfO B S hS) M (yoneda.obj U)} {actX : AAction (fppfO B S hS) M X}
    {f : yoneda.obj U ⟶ X} (hatlas : IsEquivariantAtlas actU actX f) {A : Type u}
    {V : A → ((BigFppfOver.toScheme B S hS).obj U).Opens} (hV : IsAffineDecomposition actU V)
    (hinj : ∀ (a : A) {T : BigFppfOver B S hS} (t t' : T ⟶ U),
      Set.range ((BigFppfOver.toScheme B S hS).map t) ⊆ V a →
      Set.range ((BigFppfOver.toScheme B S hS).map t') ⊆ V a →
      f.app (op T) t = f.app (op T) t' → t = t') :
    IsStronglyFPRAtlas actU actX f :=
  ⟨hatlas, isStronglyFPR_of_decomposition hatlas.equivariant hV hinj⟩

end Site

end AlgMag

#print axioms AlgMag.isStronglyFPR_of_mono
#print axioms AlgMag.isStronglyFPRAtlas_of_decomposition
