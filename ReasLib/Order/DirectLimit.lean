/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Category.Preord
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordered direct limits

Mathlib's `DirectLimit` supplies the quotient carrier of a directed system of types.  This file
adds the order-theoretic layer for systems whose transition maps are order embeddings, keeping the
carrier and its quotient API in Mathlib while exposing a bundled preorder and canonical inclusions.
-/

@[expose] public section

universe d r

namespace DirectLimit

variable {ι : Type d} [Preorder ι] [IsDirectedOrder ι]
variable {F : ι → Type r} [∀ i, Preorder (F i)]

/-- A semantic witness that two direct-limit representatives can be compared after moving to one
common later stage.  This is concrete data, rather than an existential proposition, so descended
constructions can choose a comparison without depending on a deferred proof theorem. -/
structure CommonStage (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)]
    (x y : DirectLimit F (fun i j h => f i j h)) where
  /-- A common later stage for the two quotient representatives. -/
  stage : ι
  /-- The chosen representative of the left quotient point maps to `stage`. -/
  left_le : x.out.1 ≤ stage
  /-- The chosen representative of the right quotient point maps to `stage`. -/
  right_le : y.out.1 ≤ stage
  /-- The resulting comparison in the common stage. -/
  map_le : f _ _ left_le x.out.2 ≤ f _ _ right_le y.out.2

/-- Select the concrete common-stage data carried by a direct-limit comparison. -/
noncomputable def commonStage (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)]
    {x y : DirectLimit F (fun i j h => f i j h)}
    (h : Nonempty (CommonStage f x y)) : CommonStage f x y :=
  Classical.choice h

/-- A concrete common-stage witness identifying a quotient representative with a named stage
element.  It is the generic quotient bridge used by canonical direct-limit inclusions. -/
structure RepresentativeStage (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)]
    (x : DirectLimit F (fun i j h => f i j h)) (i : ι) (y : F i) where
  /-- A stage at which the two representatives agree. -/
  stage : ι
  /-- The selected quotient representative maps to `stage`. -/
  out_le : x.out.1 ≤ stage
  /-- The named stage maps to `stage`. -/
  source_le : i ≤ stage
  /-- The images of the two representatives agree at `stage`. -/
  image_eq : f _ _ out_le x.out.2 = f _ _ source_le y

/-- Choose the setoid witness relating a quotient point to one specified direct-limit
representative.  This construction uses Mathlib's quotient relation directly, so its data does
not depend on a deferred equality theorem. -/
noncomputable def representativeStage (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)]
    (x : DirectLimit F (fun i j h => f i j h)) (i : ι) (y : F i)
    (h : x = (⟦⟨i, y⟩⟧ : DirectLimit F (fun i j h => f i j h))) :
    RepresentativeStage f x i y :=
  let hrel : (setoid (fun i j h => f i j h)).r x.out ⟨i, y⟩ :=
    Quotient.exact ((Quotient.out_eq x).trans h)
  { stage := hrel.choose
    out_le := hrel.choose_spec.choose
    source_le := hrel.choose_spec.choose_spec.choose
    image_eq := hrel.choose_spec.choose_spec.choose_spec }

/-- The relation on a Mathlib direct-limit carrier induced by the stage preorders.

It records the nonemptiness of a semantic common-stage witness.  The quotient carrier remains
Mathlib's `DirectLimit`, while data-consuming constructions can recover a witness through
`commonStage` without selecting from a theorem with deferred proof debt. -/
def leRel (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] :
    DirectLimit F (fun i j h => f i j h) →
      DirectLimit F (fun i j h => f i j h) → Prop :=
  fun x y => Nonempty (CommonStage f x y)

/-- Reflexivity of the direct-limit order relation. -/
theorem leRel_refl (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (x : DirectLimit F (fun i j h => f i j h)) :
    leRel f x x := sorry

/-- Transitivity of the direct-limit order relation. -/
theorem leRel_trans (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)]
    {x y z : DirectLimit F (fun i j h => f i j h)} :
    leRel f x y → leRel f y z → leRel f x z := sorry

/-- The preorder on the Mathlib direct-limit carrier induced by an order-embedding system. -/
noncomputable instance preordPreorder (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] :
    Preorder (DirectLimit F (fun i j h => f i j h)) where
  le := leRel f
  lt x y := leRel f x y ∧ ¬leRel f y x
  le_refl := leRel_refl f
  le_trans := fun _ _ _ => leRel_trans f
  lt_iff_le_not_ge := by
    intro x y
    rfl

/-- The directed direct limit as a bundled preorder.  Its carrier is exactly Mathlib's
`DirectLimit`; this owner supplies only the missing order structure. -/
@[stacks 00YP "ordered direct-limit index"]
noncomputable def preord (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] : Preord :=
  Preord.of (DirectLimit F (fun i j h => f i j h))

/-- The canonical order embedding from one stage into the ordered direct limit. -/
def inclusion (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (i : ι) :
    F i ↪o preord f where
  toFun := fun x => ⟦⟨i, x⟩⟧
  inj' := sorry
  map_rel_iff' := sorry

/-- The canonical inclusion is represented by Mathlib's direct-limit constructor. -/
@[simp] theorem inclusion_apply (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (i : ι) (x : F i) :
    inclusion f i x = (⟦⟨i, x⟩⟧ : DirectLimit F (fun i j h => f i j h)) := sorry

/-- Direct-limit inclusions are natural with respect to the transition embeddings. -/
theorem inclusion_natural (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i j : ι} (hij : i ≤ j) (x : F i) :
    inclusion f i x = inclusion f j (f i j hij x) := sorry

/-- A comparison of two direct-limit representatives is witnessed at one common later stage. -/
theorem leRel_mk_iff (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i j : ι} (x : F i) (y : F j) :
    leRel f (⟦⟨i, x⟩⟧ : DirectLimit F (fun i j h => f i j h))
        (⟦⟨j, y⟩⟧ : DirectLimit F (fun i j h => f i j h)) ↔
      ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
        f i k hik x ≤ f j k hjk y := sorry

/-- The direct-limit order follows from a comparison at any specified common stage. -/
theorem leRel_of_common_stage (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i j k : ι} (x : F i) (y : F j)
    (hik : i ≤ k) (hjk : j ≤ k)
    (hxy : f i k hik x ≤ f j k hjk y) :
    leRel f (⟦⟨i, x⟩⟧ : DirectLimit F (fun i j h => f i j h))
        (⟦⟨j, y⟩⟧ : DirectLimit F (fun i j h => f i j h)) := sorry

/-- Any comparison of direct-limit elements can be read on their canonical representatives. -/
theorem leRel_out_iff (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {x y : DirectLimit F (fun i j h => f i j h)} :
    leRel f x y ↔
      ∃ k, ∃ hx : x.out.1 ≤ k, ∃ hy : y.out.1 ≤ k,
        f _ _ hx x.out.2 ≤ f _ _ hy y.out.2 := sorry

/-- The canonical inclusion of one stage reflects as well as preserves its order. -/
theorem inclusion_le_iff (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i : ι} {x y : F i} :
    inclusion f i x ≤ inclusion f i y ↔ x ≤ y := sorry

/-- Comparisons between elements from different stages are exactly common-stage comparisons. -/
theorem le_iff (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i j : ι} (x : F i) (y : F j) :
    inclusion f i x ≤ inclusion f j y ↔
      ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
        f i k hik x ≤ f j k hjk y := sorry

/-- Equality of two stage inclusions is equality after moving to one common stage. -/
theorem eq_iff (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] {i j : ι} (x : F i) (y : F j) :
    inclusion f i x = inclusion f j y ↔
      ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
        f i k hik x = f j k hjk y := sorry

/-- The canonical inclusion of one stage is injective. -/
theorem inclusion_injective (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (i : ι) :
    Function.Injective (inclusion f i) := sorry

/-- Every element of the ordered direct limit lies in the image of some stage inclusion. -/
theorem exists_eq_inclusion (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (x : preord f) :
    ∃ i y, x = inclusion f i y := sorry

/-- The canonical inclusion and its quotient representative are related by Mathlib's direct-limit
setoid.  This is the stable specification used by descended-system constructions. -/
theorem rel_out_mk (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] (i : ι) (x : F i) :
    (DirectLimit.setoid (fun i j h => f i j h)).r
      (inclusion f i x).out ⟨i, x⟩ := sorry

/-- The ordered direct limit of directed stage preorders is directed. -/
theorem preord_directed (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] [∀ i, IsDirectedOrder (F i)] :
    IsDirectedOrder (preord f) := sorry

/-- Typeclass access to directedness of the ordered direct limit. -/
noncomputable instance preordIsDirected (f : ∀ i j : ι, i ≤ j → F i ↪o F j)
    [DirectedSystem F (fun i j h => f i j h)] [∀ i, IsDirectedOrder (F i)] :
    IsDirectedOrder (preord f) :=
  preord_directed f

end DirectLimit
