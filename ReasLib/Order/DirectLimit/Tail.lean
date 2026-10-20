/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tails of directed systems

This leaf supplies the order-theoretic infrastructure shared by constructions
that restrict a directed system to `Set.Ici i0`.  The directed-order and
directed-system instances are canonical restrictions, so typeclass search can
recover them without rebuilding local instance proofs at every use site.
-/

@[expose] public section

universe u v

namespace Set.Ici

variable {I : Type u} [Preorder I]

/-- The tail above a specified index is canonically inhabited by that index. -/
@[stacks 00QV "direct-limit tail"]
instance nonempty (i0 : I) : Nonempty (Set.Ici i0) :=
  ⟨⟨i0, le_rfl⟩⟩

/-- A tail of a directed preorder is directed. -/
@[instance, stacks 00QV "direct-limit tail"]
theorem isDirectedOrder [IsDirectedOrder I] (i0 : I) :
    IsDirectedOrder (Set.Ici i0) := sorry

end Set.Ici

namespace Set.Ici

variable {I : Type u} [Preorder I]

/-- The preorder obtained by adjoining a separate copy of the upper tail `Set.Ici i0` to `I`.

The left copy is the original preorder.  A left index lies below a right-tail
index exactly when it lies below that tail index in `I`; there are no
right-to-left comparisons. -/
@[stacks 00YO "adjoined directed tail"]
structure Adjoin (i0 : I) where
  /-- The left original index or the right upper-tail index. -/
  val : Sum I (Set.Ici i0)

namespace Adjoin

/-- The canonical preorder on an adjoined upper tail. -/
instance preorder (i0 : I) : Preorder (Adjoin i0) where
  le x y :=
    match x.val, y.val with
    | Sum.inl i, Sum.inl j => i ≤ j
    | Sum.inl i, Sum.inr j => i ≤ j.1
    | Sum.inr _, Sum.inl _ => False
    | Sum.inr i, Sum.inr j => i ≤ j
  le_refl := sorry
  le_trans := sorry

/-- The adjoined tail is inhabited by the left copy of its anchor. -/
instance nonempty (i0 : I) : Nonempty (Adjoin i0) :=
  ⟨⟨Sum.inl i0⟩⟩

/-- The original preorder embeds as the left summand of its adjoined tail. -/
def left (i0 : I) : I ↪o Adjoin i0 where
  toFun := fun i => ⟨Sum.inl i⟩
  inj' := sorry
  map_rel_iff' := sorry

/-- The upper tail embeds as the right summand of its adjoined tail. -/
def right (i0 : I) : Set.Ici i0 ↪o Adjoin i0 where
  toFun := fun i => ⟨Sum.inr i⟩
  inj' := sorry
  map_rel_iff' := sorry

/-- The left embedding is represented by the left summand. -/
@[simp]
theorem left_apply (i0 : I) (i : I) : (left i0 i).val = Sum.inl i := sorry

/-- The right embedding is represented by the right summand. -/
@[simp]
theorem right_apply (i0 : I) (i : Set.Ici i0) : (right i0 i).val = Sum.inr i := sorry

/-- The left embedding reflects the ambient order. -/
@[simp]
theorem left_le_left_iff (i0 : I) (i j : I) :
    left i0 i ≤ left i0 j ↔ i ≤ j := sorry

/-- The right embedding reflects the order on the upper tail. -/
@[simp]
theorem right_le_right_iff (i0 : I) (i j : Set.Ici i0) :
    right i0 i ≤ right i0 j ↔ i ≤ j := sorry

/-- A mixed comparison from the original preorder to the tail is exactly the
ambient comparison to the underlying tail index. -/
@[simp]
theorem left_le_right_iff (i0 : I) (i : I) (j : Set.Ici i0) :
    left i0 i ≤ right i0 j ↔ i ≤ j.1 := sorry

/-- No index in the right tail lies below an index in the left original copy. -/
theorem not_right_le_left (i0 : I) (i : I) (j : Set.Ici i0) :
    ¬ right i0 j ≤ left i0 i := sorry

/-- Adjoining an upper tail preserves directedness. -/
@[instance, stacks 00QV "direct-limit tail"]
theorem isDirected [IsDirected I (· ≤ ·)] (i0 : I) :
    IsDirected (Adjoin i0) (· ≤ ·) := sorry

end Adjoin
end Set.Ici

namespace DirectedSystem

variable {I : Type u} [Preorder I]
variable {F : I → Type v}

/-- Restricting a directed system to a tail preserves its canonical
directed-system structure.  The transition family is explicit because it
cannot be reconstructed by typeclass search from the reindexed carrier alone. -/
@[stacks 00QV "direct-limit tail"]
theorem ici
    (f : ∀ i j, i ≤ j → F i → F j)
    [DirectedSystem F (fun i j h ↦ f i j h)] (i0 : I) :
    DirectedSystem (fun j : Set.Ici i0 ↦ F j.1)
      (fun j k h ↦ f j.1 k.1 h) :=
  { map_self := sorry
    map_map := sorry }

end DirectedSystem
