/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.XProductsF1
import AlgMag.XProductsGlue

/-!
# X-products of attractors: the scheme `𝒩` over `F₁` (first part of Proposition 3.2)

Mayeux, *Algebraic magnetism: X-products of attractors via F₁-geometry*, §3.

The printed proof glues the `spec N_α` along the open subspace `spec N^gp`, a point. All `N_α` lie in the
group `Z`, so the glued sheaf has an explicit model: a section is a locally constant `Z`-valued function
with values in the stalks `N_{α,𝔭} ⊆ Z`.

## Main results

* `AlgMag.XP.F1.Pt`, `AlgMag.XP.F1.NSpace`: the monoidal space `𝒩`.
* `AlgMag.XP.F1.Chart.toN`, `AlgMag.XP.F1.Chart.isOpenImmersion`: `spec P → 𝒩` is an open immersion for
  `P = N_α` and `P = N^gp`.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option linter.unusedSectionVars false

namespace AlgMag.XP.F1

noncomputable section

variable {M : Type u} [AddCommGroup M]

section Comparison

variable {Z : AddSubgroup M} {P : AddSubmonoid M} (hP : P ≤ Z.toAddSubmonoid)

/-- `P → Z`, multiplicatively. -/
def incl : Multiplicative P →* Multiplicative Z :=
  AddMonoidHom.toMultiplicative
    { toFun := fun p => (⟨p.1, hP p.2⟩ : Z)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

lemma incl_injective : Function.Injective (incl hP) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (congrArg (fun x : Multiplicative Z => ((Multiplicative.toAdd x : Z) : M)) h)

/-- `Q_𝔭 → Z`, for `Q = P ⊆ Z`. -/
noncomputable def locToZ (p : specTop (Multiplicative P)) :
    Loc (Multiplicative P) p →* Multiplicative Z :=
  (Localization.monoidOf (MPrime.compl (Q := Multiplicative P) p)).lift (g := incl hP)
    fun _ => Group.isUnit _

lemma locToZ_mk (p : specTop (Multiplicative P)) (a f : Multiplicative P)
    (hf : f ∈ MPrime.compl (Q := Multiplicative P) p) :
    locToZ hP p (Localization.mk a ⟨f, hf⟩) = incl hP a * (incl hP f)⁻¹ := by
  rw [Localization.mk_eq_monoidOf_mk', locToZ, Submonoid.LocalizationMap.lift_mk'_spec]
  change incl hP a = incl hP f * (incl hP a * (incl hP f)⁻¹)
  rw [mul_comm (incl hP a), mul_inv_cancel_left]

lemma locToZ_injective (p : specTop (Multiplicative P)) : Function.Injective (locToZ hP p) := by
  intro x y
  induction x using Localization.induction_on with
  | H x =>
  induction y using Localization.induction_on with
  | H y =>
  obtain ⟨a, f⟩ := x
  obtain ⟨b, g⟩ := y
  intro h
  change locToZ hP p (Localization.mk a f) = locToZ hP p (Localization.mk b g) at h
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  rw [locToZ_mk, locToZ_mk, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul,
    ← map_mul, ← map_mul] at h
  have h' := incl_injective hP h
  refine Localization.mk_eq_mk_iff.2 (Localization.r_of_eq ?_)
  change g * a = f * b
  rw [mul_comm g, mul_comm f]
  exact h'

/-- The image of `Q_𝔭` in `Z`. -/
def locRange (p : specTop (Multiplicative P)) : Submonoid (Multiplicative Z) where
  carrier := Set.range (locToZ hP p)
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ _ _⟩

end Comparison

variable {A : Type u} (𝓝 : MagnetFamily M A)

/-- The points of `𝒩`: the generic point (`none`), common to all `spec N_α`, and the nonempty primes of
the `N_α`. -/
def Pt : Type u :=
  Option { x : Σ α, MPrime (Multiplicative (𝓝.N α)) // x.2.carrier.Nonempty }

variable {𝓝}

/-- `spec N_α → 𝒩`, on points. -/
noncomputable def jα (α : A) (p : MPrime (Multiplicative (𝓝.N α))) : Pt 𝓝 :=
  open Classical in if h : p.carrier.Nonempty then some ⟨⟨α, p⟩, h⟩ else none

/-- `spec N^gp → 𝒩`, on points. -/
def j₀ (_ : MPrime (Multiplicative 𝓝.Z.toAddSubmonoid)) : Pt 𝓝 := none

/-- The topology of `𝒩`: the gluing topology, coinduced by the `spec N_α`. -/
noncomputable instance : TopologicalSpace (Pt 𝓝) := ⨆ α : A, TopologicalSpace.coinduced (jα α) inferInstance

/-- The space underlying `𝒩`. -/
noncomputable def PtTop (𝓝 : MagnetFamily M A) : TopCat.{u} := TopCat.of (Pt 𝓝)

lemma isOpen_Pt_iff {U : Set (Pt 𝓝)} : IsOpen U ↔ ∀ α : A, IsOpen (jα α ⁻¹' U) := by
  rw [isOpen_iSup_iff]
  rfl

lemma continuous_jα (α : A) : Continuous (jα (𝓝 := 𝓝) α) :=
  continuous_iSup_rng continuous_coinduced_rng

lemma jα_of_nonempty {α : A} {p : MPrime (Multiplicative (𝓝.N α))} (h : p.carrier.Nonempty) :
    jα α p = some ⟨⟨α, p⟩, h⟩ := dif_pos h

lemma jα_of_empty {α : A} {p : MPrime (Multiplicative (𝓝.N α))} (h : ¬ p.carrier.Nonempty) :
    jα α p = none := dif_neg h

lemma carrier_eq_of_empty {Q : Type u} [CommMonoid Q] {p q : MPrime Q} (h : ¬ p.carrier.Nonempty)
    (h' : ¬ q.carrier.Nonempty) : p = q := by
  refine MPrime.ext ?_
  rw [Set.not_nonempty_iff_eq_empty.mp h, Set.not_nonempty_iff_eq_empty.mp h']

lemma jα_injective (α : A) : Function.Injective (jα (𝓝 := 𝓝) α) := by
  intro p q h
  by_cases hp : p.carrier.Nonempty <;> by_cases hq : q.carrier.Nonempty
  · rw [jα_of_nonempty hp, jα_of_nonempty hq] at h
    have h2 := congrArg Subtype.val (Option.some.inj h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  · rw [jα_of_nonempty hp, jα_of_empty hq] at h
    exact (Option.some_ne_none _ h).elim
  · rw [jα_of_empty hp, jα_of_nonempty hq] at h
    exact (Option.some_ne_none _ h.symm).elim
  · exact carrier_eq_of_empty hp hq

/-- The empty prime. -/
def botPrime (Q : Type u) [CommMonoid Q] : MPrime Q where
  carrier := ∅
  ideal _ _ h := h
  one_notMem h := h
  prime h := h.elim

/-- Every nonempty open of `spec Q` contains the empty prime. -/
lemma botPrime_mem {Q : Type u} [CommMonoid Q] {V : Set (MPrime Q)} (hV : IsOpen V) (hne : V.Nonempty) :
    botPrime Q ∈ V := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨_, ⟨f, rfl⟩, hxf, hle⟩ := isTopologicalBasis_basicSet.exists_subset_of_mem_open hx hV
  exact hle (fun h => h)

/-- The empty prime is an open point of `spec P`, for `P` finitely generated. -/
lemma isOpen_setOf_empty {P : AddSubmonoid M} (hP : P.FG) :
    IsOpen {p : MPrime (Multiplicative P) | ¬ p.carrier.Nonempty} := by
  classical
  obtain ⟨G, hG⟩ := hP
  have hGP : ∀ g ∈ G, g ∈ P := fun g hg => hG ▸ AddSubmonoid.subset_closure hg
  let s : Multiplicative P := Multiplicative.ofAdd ⟨∑ g ∈ G, g, P.sum_mem hGP⟩
  have key : ∀ (p : MPrime (Multiplicative P)) (a : M) (ha : a ∈ P),
      Multiplicative.ofAdd (⟨a, ha⟩ : P) ∈ p.carrier →
        ∃ g, ∃ hg : g ∈ G, Multiplicative.ofAdd (⟨g, hGP g hg⟩ : P) ∈ p.carrier := by
    intro p a ha
    have ha' : a ∈ AddSubmonoid.closure (G : Set M) := by rw [hG]; exact ha
    induction ha' using AddSubmonoid.closure_induction with
    | mem x hx => exact fun h => ⟨x, hx, h⟩
    | zero => exact fun h => (p.one_notMem h).elim
    | add x y hx hy ihx ihy =>
      intro h
      have hxP : x ∈ P := by rw [← hG]; exact hx
      have hyP : y ∈ P := by rw [← hG]; exact hy
      have e : Multiplicative.ofAdd (⟨x + y, ha⟩ : P) =
          Multiplicative.ofAdd (⟨x, hxP⟩ : P) * Multiplicative.ofAdd (⟨y, hyP⟩ : P) := rfl
      rw [e] at h
      exact (p.prime h).elim (ihx hxP) (ihy hyP)
  have hset : {p : MPrime (Multiplicative P) | ¬ p.carrier.Nonempty} = basicSet _ s := by
    ext p
    constructor
    · intro hp hs
      exact hp ⟨s, hs⟩
    · rintro hs ⟨a, ha⟩
      obtain ⟨g, hg, hgp⟩ := key p (Multiplicative.toAdd a : P).1 (Multiplicative.toAdd a : P).2 ha
      apply hs
      have e : s = Multiplicative.ofAdd (⟨∑ x ∈ G.erase g, x,
          P.sum_mem fun x hx => hGP x (Finset.mem_of_mem_erase hx)⟩ : P) *
          Multiplicative.ofAdd (⟨g, hGP g hg⟩ : P) := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        change ∑ x ∈ G, x = ∑ x ∈ G.erase g, x + g
        rw [add_comm, Finset.add_sum_erase G (fun x => x) hg]
      rw [e]
      exact p.ideal _ hgp
  rw [hset]
  exact isOpen_basicSet s

/-- In a group, the only prime is the empty one. -/
lemma not_nonempty_of_group {Q : Type u} [CommMonoid Q] (hQ : ∀ a : Q, ∃ b, b * a = 1) (p : MPrime Q) :
    ¬ p.carrier.Nonempty := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hQ a
  exact p.one_notMem (hb ▸ p.ideal b ha)

lemma not_nonempty_j₀ (p : MPrime (Multiplicative 𝓝.Z.toAddSubmonoid)) : ¬ p.carrier.Nonempty :=
  not_nonempty_of_group (fun a => ⟨Multiplicative.ofAdd
    ⟨-((Multiplicative.toAdd a : 𝓝.Z.toAddSubmonoid) : M), 𝓝.Z.neg_mem (Multiplicative.toAdd a).2⟩,
    by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact neg_add_cancel _⟩) p

/-- `{none}` is open in `𝒩`. -/
lemma isOpen_singleton_none : IsOpen ({none} : Set (Pt 𝓝)) := by
  rw [isOpen_Pt_iff]
  intro α
  have : jα α ⁻¹' ({none} : Set (Pt 𝓝)) = {p | ¬ p.carrier.Nonempty} := by
    ext p
    by_cases h : p.carrier.Nonempty
    · constructor
      · intro h'
        exact absurd (show jα α p = none from h') (by rw [jα_of_nonempty h]; exact Option.some_ne_none _)
      · intro h'
        exact (h' h).elim
    · exact ⟨fun _ => h, fun _ => jα_of_empty h⟩
  rw [this]
  exact isOpen_setOf_empty (𝓝.fg α)

lemma isOpenMap_jα (α : A) : IsOpenMap (jα (𝓝 := 𝓝) α) := by
  classical
  intro V hV
  rw [isOpen_Pt_iff]
  intro β
  by_cases hβ : β = α
  · subst hβ
    rwa [Set.preimage_image_eq _ (jα_injective β)]
  · by_cases hne : V.Nonempty
    · have : jα β ⁻¹' (jα α '' V) = {p | ¬ p.carrier.Nonempty} := by
        ext p
        constructor
        · rintro ⟨q, -, hq⟩ h
          rw [jα_of_nonempty h] at hq
          by_cases hq' : q.carrier.Nonempty
          · rw [jα_of_nonempty hq'] at hq
            exact hβ (congrArg (fun x => x.1.1) (Option.some.inj hq)).symm
          · rw [jα_of_empty hq'] at hq
            exact Option.some_ne_none _ hq.symm
        · intro h
          have hb : ¬ (botPrime (Multiplicative (𝓝.N α))).carrier.Nonempty := fun ⟨_, hx⟩ => hx
          refine ⟨botPrime _, botPrime_mem hV hne, ?_⟩
          rw [jα_of_empty h, jα_of_empty hb]
      rw [this]
      exact isOpen_setOf_empty (𝓝.fg β)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- The open embedding `spec N_α → 𝒩`, on spaces. -/
lemma isOpenEmbedding_jα (α : A) : Topology.IsOpenEmbedding (jα (𝓝 := 𝓝) α) :=
  .of_continuous_injective_isOpenMap (continuous_jα α) (jα_injective α) (isOpenMap_jα α)

/-- The open embedding `spec N^gp → 𝒩`, on spaces. -/
lemma isOpenEmbedding_j₀ : Topology.IsOpenEmbedding (j₀ (𝓝 := 𝓝)) := by
  refine .of_continuous_injective_isOpenMap continuous_const (fun p q _ =>
    carrier_eq_of_empty (not_nonempty_j₀ p) (not_nonempty_j₀ q)) ?_
  intro V _
  by_cases hne : V.Nonempty
  · have : j₀ '' V = ({none} : Set (Pt 𝓝)) := by
      ext x
      constructor
      · rintro ⟨_, _, rfl⟩
        rfl
      · rintro rfl
        obtain ⟨y, hy⟩ := hne
        exact ⟨y, hy, rfl⟩
    rw [this]
    exact isOpen_singleton_none
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

variable (𝓝) in
/-- The stalk of `𝒩` at a point, a submonoid of `Z`. -/
noncomputable def stk : Pt 𝓝 → Submonoid (Multiplicative 𝓝.Z)
  | none => ⊤
  | some x => locRange (𝓝.le x.1.1) x.1.2

/-- The stalk at the generic point of `spec P` is all of `Z`. -/
lemma mrange_locToZ_of_empty {α : A} (p : MPrime (Multiplicative (𝓝.N α)))
    (hp : ¬ p.carrier.Nonempty) : locRange (𝓝.le α) p = ⊤ := by
  refine top_le_iff.mp fun z _ => ?_
  obtain ⟨s, hs, hk⟩ := exists_denominator (𝓝.fg α)
  have hz : ((Multiplicative.toAdd z : 𝓝.Z) : M) ∈ AddSubgroup.closure (𝓝.N α : Set M) := by
    rw [𝓝.gp α]
    exact (Multiplicative.toAdd z).2
  obtain ⟨k, hk'⟩ := hk _ hz
  let a : Multiplicative (𝓝.N α) := Multiplicative.ofAdd ⟨_, hk'⟩
  let f : Multiplicative (𝓝.N α) := Multiplicative.ofAdd ⟨k • s, (𝓝.N α).nsmul_mem hs k⟩
  have hf : f ∈ MPrime.compl (Q := Multiplicative (𝓝.N α)) p := fun h => hp ⟨f, h⟩
  refine ⟨Localization.mk a ⟨f, hf⟩, ?_⟩
  refine (locToZ_mk _ p a f hf).trans ?_
  apply mul_inv_eq_of_eq_mul
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rfl

lemma stk_jα (α : A) (p : MPrime (Multiplicative (𝓝.N α))) :
    stk 𝓝 (jα α p) = locRange (𝓝.le α) p := by
  by_cases h : p.carrier.Nonempty
  · rw [jα_of_nonempty h]
    rfl
  · rw [jα_of_empty h, mrange_locToZ_of_empty p h]
    rfl

lemma stk_j₀ (p : MPrime (Multiplicative 𝓝.Z.toAddSubmonoid)) :
    stk 𝓝 (j₀ p) = locRange (le_refl 𝓝.Z.toAddSubmonoid) p := by
  refine (top_le_iff.mp fun z _ => ?_).symm
  have hf : (1 : Multiplicative 𝓝.Z.toAddSubmonoid) ∈
      MPrime.compl (Q := Multiplicative 𝓝.Z.toAddSubmonoid) p := p.one_notMem
  refine ⟨Localization.mk (Multiplicative.ofAdd (⟨(Multiplicative.toAdd z : 𝓝.Z).1,
    (Multiplicative.toAdd z).2⟩ : 𝓝.Z.toAddSubmonoid)) ⟨1, hf⟩, ?_⟩
  refine (locToZ_mk _ p _ _ hf).trans ?_
  rw [map_one, inv_one, mul_one]
  rfl

variable (𝓝) in
/-- Sections of `𝒩`, locally: a constant `z ∈ Z` lying in all the stalks. -/
def nPrelocal : TopCat.PrelocalPredicate (fun _ : PtTop 𝓝 => Multiplicative 𝓝.Z) where
  pred {U} s := ∃ z, ∀ x : U, s x = z ∧ z ∈ stk 𝓝 x.1
  res := by
    rintro V U i s ⟨z, h⟩
    exact ⟨z, fun x => h (i x)⟩

variable (𝓝) in
/-- The local predicate defining the sections of `𝒩`. -/
def nLocal : TopCat.LocalPredicate (fun _ : PtTop 𝓝 => Multiplicative 𝓝.Z) := (nPrelocal 𝓝).sheafify

variable (𝓝) in
/-- The sections of `𝒩` over `U`. -/
def nSections (U : Opens (PtTop 𝓝)) : Submonoid (U → Multiplicative 𝓝.Z) where
  carrier := {s | (nLocal 𝓝).pred s}
  one_mem' := fun x => ⟨U, x.2, 𝟙 U, 1, fun y => ⟨rfl, (stk 𝓝 y.1).one_mem⟩⟩
  mul_mem' := by
    intro s t hs ht x
    obtain ⟨V, hV, i, z, h⟩ := hs x
    obtain ⟨W, hW, j, w, k⟩ := ht x
    refine ⟨V ⊓ W, ⟨hV, hW⟩, Opens.infLELeft V W ≫ i, z * w, fun y => ⟨?_, ?_⟩⟩
    · exact congrArg₂ (· * ·) (h ⟨y.1, y.2.1⟩).1 (k ⟨y.1, y.2.2⟩).1
    · exact (stk 𝓝 y.1).mul_mem (h ⟨y.1, y.2.1⟩).2 (k ⟨y.1, y.2.2⟩).2

lemma nSections_mem_stk {U : Opens (PtTop 𝓝)} (s : nSections 𝓝 U) (x : U) : s.1 x ∈ stk 𝓝 x.1 := by
  obtain ⟨V, hV, i, z, h⟩ := s.2 x
  have := h ⟨x.1, hV⟩
  have e : s.1 (i ⟨x.1, hV⟩) = s.1 x := rfl
  have e2 : s.1 x = z := this.1
  rw [e2]
  exact this.2

variable (𝓝) in
/-- The structure presheaf of `𝒩`. -/
def nPresheaf : TopCat.Presheaf CommMonCat.{u} (PtTop 𝓝) where
  obj U := CommMonCat.of (nSections 𝓝 (unop U))
  map {U V} i := CommMonCat.ofHom
    { toFun := fun s => ⟨fun x => s.1 (i.unop x), (nLocal 𝓝).res i.unop _ s.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

variable (𝓝) in
/-- The presheaf in types underlying `nPresheaf`. -/
def nCompForget : nPresheaf 𝓝 ⋙ forget CommMonCat ≅ (TopCat.subsheafToTypes (nLocal 𝓝)).1 :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (𝓝) in
theorem isSheaf_nPresheaf : (nPresheaf 𝓝).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommMonCat) _).mpr
    (TopCat.Presheaf.isSheaf_of_iso (nCompForget 𝓝).symm (TopCat.subsheafToTypes (nLocal 𝓝)).2)

variable (𝓝) in
/-- The monoidal space `𝒩` of **Proposition 3.2**. -/
def NSpace : SheafedSpace CommMonCat.{u} where
  carrier := PtTop 𝓝
  presheaf := nPresheaf 𝓝
  IsSheaf := isSheaf_nPresheaf 𝓝

/-- A chart of `𝒩`: a submonoid `P ⊆ Z` with an open embedding `spec P → 𝒩` compatible with the stalks.
Both `P = N_α` and `P = N^gp` are charts. -/
structure Chart (𝓝 : MagnetFamily M A) (P : AddSubmonoid M) (hP : P ≤ 𝓝.Z.toAddSubmonoid) where
  /-- The map on points. -/
  j : MPrime (Multiplicative P) → Pt 𝓝
  emb : Topology.IsOpenEmbedding j
  stk_eq : ∀ p, stk 𝓝 (j p) = locRange hP p

variable {P : AddSubmonoid M} {hP : P ≤ 𝓝.Z.toAddSubmonoid} (c : Chart 𝓝 P hP)

/-- The topological map of a chart. -/
noncomputable def Chart.base : specTop (Multiplicative P) ⟶ PtTop 𝓝 :=
  TopCat.ofHom ⟨c.j, c.emb.continuous⟩

/-- The value in `Q_𝔭` of a section of `𝒩`. -/
noncomputable def Chart.val {U : Opens (PtTop 𝓝)} (s : nSections 𝓝 U)
    (q : (Opens.map c.base).obj U) : Loc (Multiplicative P) q.1 :=
  Classical.choose (show s.1 ⟨c.j q.1, q.2⟩ ∈ locRange hP q.1 from
    c.stk_eq q.1 ▸ nSections_mem_stk s ⟨c.j q.1, q.2⟩)

lemma Chart.locToZ_val {U : Opens (PtTop 𝓝)} (s : nSections 𝓝 U)
    (q : (Opens.map c.base).obj U) : locToZ hP q.1 (c.val s q) = s.1 ⟨c.j q.1, q.2⟩ :=
  Classical.choose_spec (show s.1 ⟨c.j q.1, q.2⟩ ∈ locRange hP q.1 from
    c.stk_eq q.1 ▸ nSections_mem_stk s ⟨c.j q.1, q.2⟩)

attribute [local irreducible] Chart.val

/-- The value of a section is a locally fraction. -/
lemma Chart.val_mem {U : Opens (PtTop 𝓝)} (s : nSections 𝓝 U) :
    c.val s ∈ sections (Multiplicative P) ((Opens.map c.base).obj U) := by
  intro q
  obtain ⟨V, hV, i, z, h⟩ := s.2 ⟨c.j q.1, q.2⟩
  have hz := h ⟨c.j q.1, hV⟩
  have hmem : z ∈ locRange hP q.1 := c.stk_eq q.1 ▸ hz.2
  obtain ⟨x, hx⟩ := hmem
  induction x using Localization.induction_on with
  | H y =>
  obtain ⟨a, ⟨f, hf⟩⟩ := y
  have hx' : incl hP a * (incl hP f)⁻¹ = z := (locToZ_mk hP q.1 a f hf).symm.trans hx
  let W : Opens (specTop (Multiplicative P)) :=
    (Opens.map c.base).obj V ⊓ ⟨basicSet _ f, isOpen_basicSet f⟩
  have hle : W ≤ (Opens.map c.base).obj U := fun y hy => leOfHom i hy.1
  have hqW : q.1 ∈ W := ⟨hV, hf⟩
  have hfW : ∀ y : W, f ∉ (show MPrime (Multiplicative P) from y.1).carrier := fun y => y.2.2
  have hval : ∀ y : W, c.val s ⟨y.1, hle y.2⟩ = fracAt (Multiplicative P) a f y.1 (hfW y) := by
    intro y
    refine locToZ_injective hP y.1 ?_
    have e1 : locToZ hP y.1 (c.val s ⟨y.1, hle y.2⟩) = s.1 ⟨c.j y.1, hle y.2⟩ :=
      c.locToZ_val s ⟨y.1, hle y.2⟩
    have e2 : locToZ hP y.1 (fracAt (Multiplicative P) a f y.1 (hfW y)) =
        incl hP a * (incl hP f)⁻¹ := locToZ_mk hP y.1 a f (hfW y)
    rw [e1, e2, hx']
    exact (h ⟨c.j y.1, y.2.1⟩).1
  exact ⟨W, hqW, homOfLE hle, isFractionPrelocal_mk (U := W) _ a f hfW hval⟩

/-- The map on sections of a chart. -/
noncomputable def Chart.secMap (U : Opens (PtTop 𝓝)) :
    nSections 𝓝 U →* sections (Multiplicative P) ((Opens.map c.base).obj U) where
  toFun s := ⟨c.val s, c.val_mem s⟩
  map_one' := by
    refine Subtype.ext (funext fun q => locToZ_injective hP q.1 ?_)
    refine (c.locToZ_val 1 q).trans ?_
    exact (map_one (locToZ hP q.1)).symm
  map_mul' s t := by
    refine Subtype.ext (funext fun q => locToZ_injective hP q.1 ?_)
    refine (c.locToZ_val (s * t) q).trans ?_
    refine Eq.trans ?_ (map_mul (locToZ hP q.1) _ _).symm
    exact congrArg₂ (· * ·) (c.locToZ_val s q).symm (c.locToZ_val t q).symm

/-- The morphism of sheafed spaces `spec P → 𝒩`. -/
noncomputable def Chart.toN : spec (Multiplicative P) ⟶ NSpace 𝓝 :=
  InducedCategory.homMk
    { base := c.base
      c :=
        { app := fun U => CommMonCat.ofHom (c.secMap (unop U))
          naturality := fun U V i => by
            ext s
            refine Subtype.ext (funext fun q => locToZ_injective hP q.1 ?_)
            refine (c.locToZ_val ((NSpace 𝓝).presheaf.map i s) q).trans ?_
            exact (c.locToZ_val s ⟨q.1, leOfHom i.unop q.2⟩).symm } }

/-- The bijection on sections over the image of an open of `spec P`. -/
theorem Chart.secMap_bijective (U : Opens (specTop (Multiplicative P))) :
    Function.Bijective (c.secMap ⟨c.j '' U.1, c.emb.isOpenMap _ U.2⟩) := by
  classical
  let W : Opens (PtTop 𝓝) := ⟨c.j '' U.1, c.emb.isOpenMap _ U.2⟩
  have hinj : Function.Injective c.j := c.emb.injective
  constructor
  · intro s s' h
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨q, hq, hx⟩ := x.2
    have hq' : q ∈ (Opens.map c.base).obj W := ⟨q, hq, rfl⟩
    have hv : c.val s ⟨q, hq'⟩ = c.val s' ⟨q, hq'⟩ :=
      congrFun (congrArg Subtype.val h) ⟨q, hq'⟩
    have e1 := c.locToZ_val s ⟨q, hq'⟩
    have e2 := c.locToZ_val s' ⟨q, hq'⟩
    rw [hv] at e1
    have ex : x = ⟨c.j q, hq'⟩ := Subtype.ext hx.symm
    rw [ex]
    exact e1.symm.trans e2
  · intro t
    have hpre : ∀ x : W, ∃ q, ∃ hq : q ∈ (Opens.map c.base).obj W, c.j q = x.1 := by
      intro x
      obtain ⟨q, hq, hx⟩ := x.2
      exact ⟨q, by change c.j q ∈ W; rw [hx]; exact x.2, hx⟩
    choose pre hpre' hpre'' using hpre
    let s₀ : W → Multiplicative 𝓝.Z := fun x => locToZ hP (pre x) (t.1 ⟨pre x, hpre' x⟩)
    have hs₀ : ∀ (q) (hq : q ∈ (Opens.map c.base).obj W),
        s₀ ⟨c.j q, hq⟩ = locToZ hP q (t.1 ⟨q, hq⟩) := by
      intro q hq
      have e : pre ⟨c.j q, hq⟩ = q := hinj (hpre'' _)
      have gen : ∀ (q' : MPrime (Multiplicative P)) (hq' : q' ∈ (Opens.map c.base).obj W),
          q' = q → locToZ hP q' (t.1 ⟨q', hq'⟩) = locToZ hP q (t.1 ⟨q, hq⟩) := by
        rintro q' hq' rfl
        rfl
      exact gen _ _ e
    have hmem : s₀ ∈ nSections 𝓝 W := by
      intro x
      have hx0 : pre x ∈ (Opens.map c.base).obj W := hpre' x
      obtain ⟨V₀, hV₀, i₀, a, f, hf, h⟩ := t.2 ⟨pre x, hx0⟩
      let V : Opens (PtTop 𝓝) := ⟨c.j '' V₀.1, c.emb.isOpenMap _ V₀.2⟩
      have hVW : V ≤ W := by
        rintro _ ⟨y, hy, rfl⟩
        exact leOfHom i₀ hy
      refine ⟨V, ⟨pre x, hV₀, hpre'' x⟩, homOfLE hVW, incl hP a * (incl hP f)⁻¹, ?_⟩
      rintro ⟨_, y, hy, rfl⟩
      have hyW : y ∈ (Opens.map c.base).obj W := leOfHom i₀ hy
      have e1 : t.1 ⟨y, hyW⟩ = fracAt (Multiplicative P) a f y (hf ⟨y, hy⟩) := h ⟨y, hy⟩
      have e2 : locToZ hP y (fracAt (Multiplicative P) a f y (hf ⟨y, hy⟩)) =
          incl hP a * (incl hP f)⁻¹ := locToZ_mk hP y a f (hf ⟨y, hy⟩)
      refine ⟨?_, ?_⟩
      · refine (hs₀ y hyW).trans ?_
        rw [e1, e2]
      · change _ ∈ stk 𝓝 (c.j y)
        rw [c.stk_eq y]
        exact ⟨_, e2⟩
    refine ⟨⟨s₀, hmem⟩, Subtype.ext (funext fun q => locToZ_injective hP q.1 ?_)⟩
    refine (c.locToZ_val ⟨s₀, hmem⟩ q).trans ?_
    exact hs₀ q.1 q.2

/-- **Proposition 3.2**: `spec P → 𝒩` is an open immersion. -/
theorem Chart.isOpenImmersion : SheafedSpace.IsOpenImmersion c.toN := by
  refine ⟨c.emb, fun U => ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact c.secMap_bijective U

/-- The chart `spec N_α → 𝒩`. -/
def chartα (𝓝 : MagnetFamily M A) (α : A) : Chart 𝓝 (𝓝.N α) (𝓝.le α) where
  j := jα α
  emb := isOpenEmbedding_jα α
  stk_eq := stk_jα α

/-- The chart `spec N^gp → 𝒩`. -/
def chart₀ (𝓝 : MagnetFamily M A) : Chart 𝓝 𝓝.Z.toAddSubmonoid le_rfl where
  j := j₀
  emb := isOpenEmbedding_j₀
  stk_eq := stk_j₀

/-- **Proposition 3.2**, first assertion: `𝒩` is a monoscheme, a scheme over `F₁`. -/
theorem isMonoscheme_NSpace [Nonempty A] : IsMonoscheme (NSpace 𝓝) := by
  intro x
  rcases x with _ | ⟨⟨⟨α, p⟩, hp⟩⟩
  · obtain ⟨α⟩ := ‹Nonempty A›
    refine ⟨Multiplicative (𝓝.N α), inferInstance, (chartα 𝓝 α).toN, (chartα 𝓝 α).isOpenImmersion,
      botPrime _, ?_⟩
    exact jα_of_empty fun h => h.elim fun _ hx => hx
  · refine ⟨Multiplicative (𝓝.N α), inferInstance, (chartα 𝓝 α).toN, (chartα 𝓝 α).isOpenImmersion,
      p, ?_⟩
    exact jα_of_nonempty hp

end

end AlgMag.XP.F1
