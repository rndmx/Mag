/-
Copyright (c) 2026 Arnaud Mayeux. All rights reserved.
Released under Apache 2.0 license.
-/
import AlgMag.Sec9General

/-!
# The cocycle argument of Proposition 10.1

Mayeux, *Algebraic Magnetism*, proof of Proposition 10.1, the formal part: the lifts `P` form a torsor
under `F` on flat objects only, `H` is represented by a flat object, and so is `H × H`. From a lift
`a'` over `V` one forms the cocycle `c(g) = g • a'_T - a'_T`; if it is a coboundary of `v` then
`β = a' - v` is invariant. No scheme appears here.
-/

open CategoryTheory Opposite

universe v u

namespace AlgMag.Sec10Printed

open AlgMag.S9

variable {C : Type*} [Category.{v} C] {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}
  {H : Cᵒᵖ ⥤ MonCat.{u}} {F : PMod 𝒪}

/-- The printed torsor of lifts over `V`, on flat objects, with `H` and `H × H` represented by flat
objects. `diff b c` is `b - c`. -/
structure LiftTorsor (A : HModule H F) (V : C) where
  /-- flat objects -/
  Flat : C → Prop
  /-- the lifts, as a presheaf -/
  P : Cᵒᵖ ⥤ Type u
  /-- `g • a = g a g⁻¹` -/
  act : ∀ {T : C}, H.obj (op T) → P.obj (op T) → P.obj (op T)
  act_mul : ∀ {T : C} (g g' : H.obj (op T)) (b : P.obj (op T)), act (g * g') b = act g (act g' b)
  act_map : ∀ {T T' : C} (s : T' ⟶ T) (g : H.obj (op T)) (b : P.obj (op T)),
    P.map s.op (act g b) = act ((H.map s.op).hom g) (P.map s.op b)
  /-- the difference, on flat objects only -/
  diff : ∀ {T : C}, Flat T → P.obj (op T) → P.obj (op T) → F.obj (op T)
  diff_add : ∀ {T : C} (h : Flat T) (b c d : P.obj (op T)), diff h b c + diff h c d = diff h b d
  diff_eq : ∀ {T : C} (h : Flat T) (b c : P.obj (op T)), diff h b c = 0 → b = c
  diff_act : ∀ {T : C} (h : Flat T) (g : H.obj (op T)) (b c : P.obj (op T)),
    diff h (act g b) (act g c) = A.smul g (diff h b c)
  diff_map : ∀ {T T' : C} (h : Flat T) (h' : Flat T') (s : T' ⟶ T) (b c : P.obj (op T)),
    diff h' (P.map s.op b) (P.map s.op c) = F.map s.op (diff h b c)
  /-- the object representing `H` over `V` -/
  G : C
  π : G ⟶ V
  flatG : Flat G
  u : H.obj (op G)
  cls : ∀ {T : C}, (T ⟶ V) → H.obj (op T) → (T ⟶ G)
  cls_π : ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)), cls t g ≫ π = t
  cls_u : ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)), (H.map (cls t g).op).hom u = g
  cls_uniq : ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)) (k : T ⟶ G), k ≫ π = t →
    (H.map k.op).hom u = g → k = cls t g
  /-- the object representing `H × H` over `V` -/
  G₂ : C
  π₂ : G₂ ⟶ V
  flatG₂ : Flat G₂
  u₁ : H.obj (op G₂)
  u₂ : H.obj (op G₂)
  cls₂ : ∀ {T : C}, (T ⟶ V) → H.obj (op T) → H.obj (op T) → (T ⟶ G₂)
  cls₂_π : ∀ {T : C} (t : T ⟶ V) (g g' : H.obj (op T)), cls₂ t g g' ≫ π₂ = t
  cls₂_u₁ : ∀ {T : C} (t : T ⟶ V) (g g' : H.obj (op T)), (H.map (cls₂ t g g').op).hom u₁ = g
  cls₂_u₂ : ∀ {T : C} (t : T ⟶ V) (g g' : H.obj (op T)), (H.map (cls₂ t g g').op).hom u₂ = g'

variable {A : HModule H F} {V : C} (L : LiftTorsor A V) (a : L.P.obj (op V))

namespace LiftTorsor

/-- `a'` on an object over `V`. -/
def on {T : C} (t : T ⟶ V) (b : L.P.obj (op V)) : L.P.obj (op T) := L.P.map t.op b

lemma on_comp {T T' : C} (s : T' ⟶ T) (t : T ⟶ V) (b : L.P.obj (op V)) :
    L.on (s ≫ t) b = L.P.map s.op (L.on t b) := by
  simp [on]

/-- The universal value of the cocycle: `c(u) = u • a'_G - a'_G`. -/
def c₀ : F.obj (op L.G) := L.diff L.flatG (L.act L.u (L.on L.π a)) (L.on L.π a)

/-- The value of `c` on a flat object is the difference, by naturality. -/
lemma c₀_flat {T : C} (hT : L.Flat T) (t : T ⟶ V) (g : H.obj (op T)) :
    F.map (L.cls t g).op (L.c₀ a) = L.diff hT (L.act g (L.on t a)) (L.on t a) := by
  rw [c₀, ← L.diff_map L.flatG hT, L.act_map, L.cls_u, ← on_comp, L.cls_π]

lemma cls_comp {T T' : C} (s : T' ⟶ T) (t : T ⟶ V) (g : H.obj (op T)) :
    s ≫ L.cls t g = L.cls (s ≫ t) ((H.map s.op).hom g) :=
  L.cls_uniq _ _ _ (by rw [Category.assoc, L.cls_π])
    (by rw [op_comp, H.map_comp, MonCat.comp_apply, L.cls_u])

/-- **The cocycle** of the printed proof: `c(g)` is pulled back from the universal point, which lies
on a flat object since `G` is flat. -/
def cocycle : Cochain H F V 1 where
  app {T} t g := F.map (L.cls t (g 0)).op (L.c₀ a)
  naturality {T T'} s t g := by
    rw [← F.map_comp, ← op_comp, cls_comp]

/-- **The cocycle identity** `c(gg') = c(g) + g • c(g')`, checked on the flat `G₂`. -/
theorem cocycle_mem : L.cocycle a ∈ Zn A V 1 := by
  rw [mem_Z1_iff]
  intro T t g g'
  have hG := L.flatG₂
  have key : L.diff hG (L.act (L.u₁ * L.u₂) (L.on L.π₂ a)) (L.on L.π₂ a) =
      L.diff hG (L.act L.u₁ (L.on L.π₂ a)) (L.on L.π₂ a) +
        A.smul L.u₁ (L.diff hG (L.act L.u₂ (L.on L.π₂ a)) (L.on L.π₂ a)) := by
    rw [← L.diff_act, L.act_mul, add_comm, L.diff_add]
  rw [← L.c₀_flat a hG L.π₂ (L.u₁ * L.u₂), ← L.c₀_flat a hG L.π₂ L.u₁,
    ← L.c₀_flat a hG L.π₂ L.u₂] at key
  have key₂ := congrArg (F.map (L.cls₂ t g g').op) key
  rw [map_add, A.map_smul, ← F.map_comp, ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← op_comp,
    L.cls₂_u₁, cls_comp, cls_comp, cls_comp, L.cls₂_π, map_mul, L.cls₂_u₁, L.cls₂_u₂] at key₂
  exact key₂

lemma diff_self {T : C} (h : L.Flat T) (b : L.P.obj (op T)) : L.diff h b b = 0 :=
  left_eq_add.mp (L.diff_add h b b b).symm

/-- **End of the printed proof.** If `c(g) = g • v_T - v_T` and `β = a' - v` exists, then `β` is
invariant under `H` on every object over `V`, flat or not. -/
theorem invariant_of_coboundary (v : F.obj (op V)) (hF : L.Flat V)
    (hv : ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)),
      (L.cocycle a).app t ![g] = A.smul g (F.map t.op v) - F.map t.op v)
    (β : L.P.obj (op V)) (hβ : L.diff hF a β = v) {T : C} (t : T ⟶ V) (g : H.obj (op T)) :
    L.act g (L.on t β) = L.on t β := by
  have hG := L.flatG
  have hvG := hv L.π L.u
  have hc : (L.cocycle a).app L.π ![L.u] = L.diff hG (L.act L.u (L.on L.π a)) (L.on L.π a) :=
    L.c₀_flat a hG L.π L.u
  have ha : L.diff hG (L.on L.π a) (L.on L.π β) = F.map L.π.op v := by
    rw [← hβ]; exact L.diff_map hF hG L.π a β
  have hu : L.act L.u (L.on L.π β) = L.on L.π β := by
    refine L.diff_eq hG _ _ ?_
    have s₁ := L.diff_add hG (L.act L.u (L.on L.π a)) (L.on L.π a) (L.on L.π β)
    have s₂ := L.diff_add hG (L.act L.u (L.on L.π β)) (L.act L.u (L.on L.π a)) (L.on L.π β)
    have s₃ := L.diff_add hG (L.act L.u (L.on L.π β)) (L.act L.u (L.on L.π a))
      (L.act L.u (L.on L.π β))
    rw [L.diff_self hG, L.diff_act hG L.u (L.on L.π a) (L.on L.π β), ha] at s₃
    rw [← s₂, ← s₁, ha, ← hc, hvG, eq_neg_of_add_eq_zero_left s₃]
    abel
  have := congrArg (L.P.map (L.cls t g).op) hu
  rw [L.act_map, L.cls_u, ← on_comp, L.cls_π] at this
  exact this

/-- **The printed proof of Proposition 10.1**, formal part: if `H¹` vanishes, a lift `β` differing
from `a'` by the coboundary datum is invariant. `add` is the action of `F(V)` on `P(V)`. -/
theorem exists_invariant (hF : L.Flat V) (h1 : Subsingleton (Hn A V 1))
    (add : ∀ v : F.obj (op V), ∃ β, L.diff hF a β = v) :
    ∃ β : L.P.obj (op V), ∀ {T : C} (t : T ⟶ V) (g : H.obj (op T)),
      L.act g (L.on t β) = L.on t β := by
  have hb : L.cocycle a ∈ Bn A V 1 := by
    have e := h1.elim (Submodule.Quotient.mk ⟨_, L.cocycle_mem a⟩) 0
    rw [Submodule.Quotient.mk_eq_zero] at e
    exact e
  obtain ⟨v, hv⟩ := (mem_B1_iff A _).1 hb
  obtain ⟨β, hβ⟩ := add v
  exact ⟨β, fun t g => L.invariant_of_coboundary a v hF hv β hβ t g⟩

end LiftTorsor

end AlgMag.Sec10Printed
