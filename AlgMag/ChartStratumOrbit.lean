/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.ChartStratumStab
import AlgMag.AppendixA
import AlgMag.Sec8Representability

/-!
# Orbits of a point with generic stabilizer (affine stratum lemma, steps 3 and 4)

`OrbitLocal act p s`: a point of `X` which is fppf locally in the `D(M)`-orbit of `p|_{D(s)}`.
On such a point the stabilizer is the one computed by `exists_generic_stabilizer`
(`smul_eq_iff_of_orbitLocal`). If this holds on all of a sheaf `F`, the action descends to a free
action of `D(Z)` on `F` (`descAction`).
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgMag.StronglyFPR

universe u

namespace AlgMag.ChartStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {M : Type u} [AddCommGroup M] [Countable M] {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

local notation "SCH" => BigFppfOver.toScheme B S hS

/-- Points of `𝔸(N)` are separated for the fppf topology. -/
lemma aPt_eq_of_sieve (N : AddSubmonoid M) {T : BigFppfOver B S hS}
    (R : Sieve T) (hR : R ∈ BigFppfOver.topology B S hS T) (a b : APt (fppfO B S hS) N (op T))
    (h : ∀ ⦃T' : BigFppfOver B S hS⦄ (f : T' ⟶ T), R f → APt.res f.op a = APt.res f.op b) :
    a = b := by
  have hM : B.Contains (Spec (ZMon N)) := contains_zmon_of_countable hS N
  let U := monAffUniversal N hM T
  have hsh := BigFppfOver.isSheaf_yoneda_obj B S hS U.P
  rw [isSheaf_iff_isSheaf_of_type] at hsh
  have key : ∀ (c : APt (fppfO B S hS) N (op T)) ⦃T' : BigFppfOver B S hS⦄ (f : T' ⟶ T),
      f ≫ U.lift (𝟙 T) c = U.lift f (APt.res f.op c) := by
    intro c T' f
    refine U.uniq f _ _ ?_ ?_
    · rw [Category.assoc, U.lift_π, Category.comp_id]
    · rw [op_comp, APt.res_comp, U.res_lift]
  have e : U.lift (𝟙 T) a = U.lift (𝟙 T) b := by
    refine (hsh _ hR).isSeparatedFor.ext ?_
    intro Y f hf
    change f ≫ _ = f ≫ _
    rw [key, key, h f hf]
  rw [← U.res_lift (𝟙 T) a, e, U.res_lift]

section Orbit

variable {V : BigFppfOver B S hS} (act : AAction (fppfO B S hS) M X) (p : X.obj (op V))

/-- `x` is, fppf locally, in the `D(M)`-orbit of `p|_{D(s)}`. -/
def OrbitLocal (s : Γ((SCH).obj V, ⊤)) (T : BigFppfOver B S hS) (x : X.obj (op T)) : Prop :=
  ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃T' : BigFppfOver B S hS⦄ (f : T' ⟶ T), R f →
    ∃ (t : T' ⟶ V) (g : APt (fppfO B S hS) M (op T')),
      IsUnit (((SCH).map t).appTop.hom s) ∧ X.map f.op x = act.smul g (X.map t.op p)

variable {act p}

/-- **Affine stratum lemma, step 3**: on the orbit of `p`, a point of `D(M)` fixes `x` exactly when it is
trivial on `Z`. -/
theorem smul_eq_iff_of_orbitLocal {s : Γ((SCH).obj V, ⊤)} {Z : AddSubgroup M}
    (hX : Presieve.IsSheaf (BigFppfOver.topology B S hS) X)
    (hZ : ∀ (T : BigFppfOver B S hS) (t : T ⟶ V), IsUnit (((SCH).map t).appTop.hom s) →
        ∀ h : APt (fppfO B S hS) M (op T),
          act.smul h (X.map t.op p) = X.map t.op p ↔
            ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1)
    {T : BigFppfOver B S hS} {x : X.obj (op T)} (hx : OrbitLocal act p s T x)
    (h : APt (fppfO B S hS) M (op T)) :
    act.smul h x = x ↔ ∀ z ∈ Z, h (Multiplicative.ofAdd z) = 1 := by
  obtain ⟨R, hR, hc⟩ := hx
  have local_iff : ∀ ⦃T' : BigFppfOver B S hS⦄ (f : T' ⟶ T), R f →
      (act.smul (APt.res f.op h) (X.map f.op x) = X.map f.op x ↔
        ∀ z ∈ Z, APt.res f.op h (Multiplicative.ofAdd z) = 1) := by
    intro T' f hf
    obtain ⟨t, g, hs, e⟩ := hc f hf
    have comm : act.smul (APt.res f.op h) (act.smul g (X.map t.op p)) =
        act.smul g (act.smul (APt.res f.op h) (X.map t.op p)) := by
      rw [← act.mul_smul, mul_comm, act.mul_smul]
    rw [e, comm, ← hZ T' t hs (APt.res f.op h)]
    constructor
    · intro k
      have := congrArg (act.smul (APt.inv g)) k
      have cancel : ∀ y, act.smul (APt.inv g) (act.smul g y) = y := fun y => by
        rw [← act.mul_smul, APt.inv_mul, act.one_smul]
      rwa [cancel, cancel] at this
    · intro k
      rw [k]
  constructor
  · intro e z hz
    have : APt.toMagnet Z.toAddSubmonoid h = 1 := by
      refine aPt_eq_of_sieve _ R hR _ _ fun T' f hf => ?_
      refine MonoidHom.ext fun w => ?_
      have k := (local_iff f hf).mp (by rw [← act.map_smul, e])
      refine (k _ (Multiplicative.toAdd w).2).trans ?_
      simp
    exact DFunLike.congr_fun this (Multiplicative.ofAdd ⟨z, hz⟩)
  · intro e
    refine (hX _ hR).isSeparatedFor.ext ?_
    intro T' f hf
    change X.map f.op _ = X.map f.op _
    rw [act.map_smul]
    refine (local_iff f hf).mpr fun z hz => ?_
    rw [APt.res_apply, e z hz]
    exact map_one _

end Orbit

section Descent

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [AddGroup.FG M] {act : AAction (fppfO B S hS) M F}
  {Z : AddSubgroup M}

/-- `D(Z)` on a sheaf all of whose points are fixed by `D(M/Z)`: the value `a • x`, characterized
by being `h • x` wherever `a` extends to `h`. -/
theorem existsUnique_descSmul (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hfix : ∀ {T : BigFppfOver B S hS} (x : F.obj (op T)) (h : APt (fppfO B S hS) M (op T)),
      TrivialOn Z h → act.smul h x = x)
    {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) (x : F.obj (op T)) :
    ∃! y : F.obj (op T), ∀ {T'' : BigFppfOver B S hS} (s : T'' ⟶ T)
      (h : APt (fppfO B S hS) M (op T'')),
      APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a →
        F.map s.op y = act.smul h (F.map s.op x) := by
  have hx : x ∈ (fixedPoints (quotientAction act Z)).obj (op T) :=
    mem_fixedPoints_quotient_iff.mpr fun {T'} r h hh => by
      obtain ⟨T'', rfl⟩ : ∃ T'' : BigFppfOver B S hS, T' = op T'' := ⟨T'.unop, rfl⟩
      exact hfix _ h hh
  have := existsUnique_glue (J := BigFppfOver.topology B S hS) (act := act) (Z := Z) hF
    (fun a => extSieve_mem Z a) hx (𝟙 T) a
  simpa only [Category.comp_id] using this

/-- The action of `D(Z)`, value at `a` and `x`. -/
noncomputable def descSmul (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hfix : ∀ {T : BigFppfOver B S hS} (x : F.obj (op T)) (h : APt (fppfO B S hS) M (op T)),
      TrivialOn Z h → act.smul h x = x)
    {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) (x : F.obj (op T)) :
    F.obj (op T) :=
  (existsUnique_descSmul hF hfix a x).choose

variable (hF : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    (hfix : ∀ {T : BigFppfOver B S hS} (x : F.obj (op T)) (h : APt (fppfO B S hS) M (op T)),
      TrivialOn Z h → act.smul h x = x)

lemma descSmul_spec {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T))
    (x : F.obj (op T)) {T'' : BigFppfOver B S hS} (s : T'' ⟶ T) (h : APt (fppfO B S hS) M (op T''))
    (e : APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a) :
    F.map s.op (descSmul hF hfix a x) = act.smul h (F.map s.op x) :=
  (existsUnique_descSmul hF hfix a x).choose_spec.1 s h e

lemma descSmul_eq {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T))
    (x y : F.obj (op T))
    (hy : ∀ {T'' : BigFppfOver B S hS} (s : T'' ⟶ T) (h : APt (fppfO B S hS) M (op T'')),
      APt.toMagnet Z.toAddSubmonoid h = APt.res s.op a → F.map s.op y = act.smul h (F.map s.op x)) :
    descSmul hF hfix a x = y :=
  ((existsUnique_descSmul hF hfix a x).choose_spec.2 y (fun {_} s h e => hy s h e)).symm

/-- **Affine stratum lemma, step 4**: the action descends to `D(Z)`. -/
noncomputable def descAction : AAction (fppfO B S hS) Z.toAddSubmonoid F where
  smul {T} a x := descSmul hF hfix (T := T.unop) a x
  one_smul {T} x := by
    refine descSmul_eq hF hfix (T := T.unop) _ _ _ fun s h e => ?_
    refine (hfix _ h ?_).symm
    change APt.toMagnet _ h = 1
    rw [e]
    ext w; simp
  mul_smul {T} g h x := by
    refine descSmul_eq hF hfix (T := T.unop) _ _ _ fun {T''} s k e => ?_
    have mem := extSieve_mem (B := B) (S := S) (hS := hS) Z (APt.res s.op g)
    refine (hF _ mem).isSeparatedFor.ext fun W r hr => ?_
    obtain ⟨k₁, hk₁⟩ := hr
    change F.map r.op _ = F.map r.op _
    rw [← APt.res_comp, ← op_comp] at hk₁
    have hk₂ : APt.toMagnet Z.toAddSubmonoid (APt.res r.op k * APt.inv k₁) =
        APt.res (r ≫ s).op h := by
      have e' : APt.toMagnet Z.toAddSubmonoid (APt.res r.op k) = APt.res (r ≫ s).op (g * h) := by
        rw [APt.toMagnet_res, e, op_comp, APt.res_comp]
      refine MonoidHom.ext fun w => ?_
      have e1 := DFunLike.congr_fun e' w
      have e2 := DFunLike.congr_fun hk₁ w
      have hu : k₁ (Multiplicative.ofAdd ((Multiplicative.toAdd w : Z.toAddSubmonoid) : M)) *
          APt.inv k₁ (Multiplicative.ofAdd ((Multiplicative.toAdd w : Z.toAddSubmonoid) : M)) = 1 := by
        rw [mul_comm]; exact DFunLike.congr_fun (APt.inv_mul k₁) _
      simp only [APt.toMagnet_apply, APt.res_apply, MonoidHom.mul_apply, map_mul] at e1 e2 ⊢
      rw [e1, ← e2, mul_right_comm, hu, one_mul]
    rw [← Functor.map_comp_apply, ← op_comp, act.map_smul, ← Functor.map_comp_apply, ← op_comp,
      descSmul_spec hF hfix _ _ (r ≫ s) k₁ hk₁, descSmul_spec hF hfix _ _ (r ≫ s) _ hk₂,
      ← act.mul_smul]
    congr 1
    rw [mul_comm k₁, mul_assoc, APt.inv_mul, mul_one]
  map_smul {T T'} f h x := by
    refine (descSmul_eq hF hfix (T := T'.unop) _ _ _ fun {T''} s k e => ?_).symm
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact descSmul_spec hF hfix (T := T.unop) h x (s ≫ f.unop) k (by rw [e, ← APt.res_comp]; rfl)

/-- `descAction` on the points that extend. -/
lemma descAction_toMagnet {T : BigFppfOver B S hS} (h : APt (fppfO B S hS) M (op T))
    (x : F.obj (op T)) :
    (descAction hF hfix).smul (APt.toMagnet Z.toAddSubmonoid h) x = act.smul h x := by
  have := descSmul_spec hF hfix (APt.toMagnet Z.toAddSubmonoid h) x (𝟙 T) h (by simp)
  simp at this
  exact this

/-- Freeness of `descAction`, given that the fixers of a point are the points trivial on `Z`. -/
lemma descAction_free (hfree : ∀ {T : BigFppfOver B S hS} (x : F.obj (op T))
      (h : APt (fppfO B S hS) M (op T)), act.smul h x = x → TrivialOn Z h)
    {T : BigFppfOver B S hS} (a : APt (fppfO B S hS) Z.toAddSubmonoid (op T)) (x : F.obj (op T))
    (e : (descAction hF hfix).smul a x = x) : a = 1 := by
  refine aPt_eq_of_sieve _ _ (extSieve_mem (B := B) (S := S) (hS := hS) Z a) _ _ ?_
  rintro T' f ⟨k, hk⟩
  have e2 := congrArg (F.map f.op) e
  rw [(descAction hF hfix).map_smul, ← hk, descAction_toMagnet] at e2
  have := hfree _ _ e2
  rw [← hk]
  refine this.trans ?_
  ext w; simp

end Descent

end AlgMag.ChartStratum
