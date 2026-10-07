module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Total complex shapes

This file gives typeclass-facing names to Mathlib's `Relator.RightTotal` and
`Relator.LeftTotal` conditions on a complex shape.  The wrappers make canonical shape facts
available to typeclass search while the public API continues to use the standard relation
predicates.
-/

@[expose] public section

universe w

namespace ComplexShape

variable {ι : Type w} (c : ComplexShape ι)

/-- A complex shape has an incoming index at every degree. -/
@[stacks 01A2 "complex shapes with incoming indices"]
class HasIncoming : Prop where
  /-- The differential relation is right total. -/
  rightTotal : Relator.RightTotal c.Rel

/-- A complex shape has an outgoing index at every degree. -/
@[stacks 01A2 "complex shapes with outgoing indices"]
class HasOutgoing : Prop where
  /-- The differential relation is left total. -/
  leftTotal : Relator.LeftTotal c.Rel

/-- Having incoming indices is exactly right totality of the differential relation. -/
theorem hasIncoming_iff_rightTotal :
    c.HasIncoming ↔ Relator.RightTotal c.Rel := sorry

/-- Having outgoing indices is exactly left totality of the differential relation. -/
theorem hasOutgoing_iff_leftTotal :
    c.HasOutgoing ↔ Relator.LeftTotal c.Rel := sorry

/-- The canonical predecessor is related to its degree when incoming indices exist. -/
theorem HasIncoming.rel_prev [c.HasIncoming] (j : ι) :
    c.Rel (c.prev j) j := sorry

/-- A degree is related to its canonical successor when outgoing indices exist. -/
theorem HasOutgoing.rel_next [c.HasOutgoing] (i : ι) :
    c.Rel i (c.next i) := sorry

/-- Reversing a shape with incoming indices gives a shape with outgoing indices. -/
theorem HasIncoming.symm [c.HasIncoming] : c.symm.HasOutgoing := sorry

/-- Reversing a shape with outgoing indices gives a shape with incoming indices. -/
theorem HasOutgoing.symm [c.HasOutgoing] : c.symm.HasIncoming := sorry

/-- A shape with incoming and outgoing indices has a bi-total differential relation. -/
@[stacks 01A2 "bi-total differential relation of an unbounded complex shape"]
theorem biTotal [c.HasIncoming] [c.HasOutgoing] : Relator.BiTotal c.Rel := sorry

namespace up'

/-- Adding the step gives the canonical outgoing index of an upward complex shape. -/
@[stacks 01A2 "canonical outgoing index for upward complex shapes"]
theorem rel_add {α : Type w} [Add α] [IsRightCancelAdd α]
    (a i : α) : (ComplexShape.up' a).Rel i (i + a) := sorry

/-- A standard upward shape has a canonical outgoing index at every degree. -/
@[stacks 01A2 "outgoing indices for upward complex shapes"]
instance hasOutgoing {α : Type w} [Add α] [IsRightCancelAdd α] (a : α) :
    (ComplexShape.up' a).HasOutgoing :=
  ⟨fun i ↦ ⟨i + a, rel_add a i⟩⟩

/-- Subtracting the step gives the canonical incoming index of an unbounded upward shape. -/
@[stacks 01A2 "canonical incoming index for upward complex shapes"]
theorem sub_rel {α : Type w} [AddGroup α]
    (a j : α) : (ComplexShape.up' a).Rel (j - a) j := sorry

/-- Over an additive group, a standard upward shape also has incoming indices. -/
@[stacks 01A2 "incoming indices for unbounded upward complex shapes"]
instance hasIncoming {α : Type w} [AddGroup α] (a : α) :
    (ComplexShape.up' a).HasIncoming :=
  ⟨fun j ↦ ⟨j - a, sub_rel a j⟩⟩

end up'

namespace down'

/-- Adding the step gives the canonical incoming index of a downward complex shape. -/
@[stacks 01A2 "canonical incoming index for downward complex shapes"]
theorem add_rel {α : Type w} [Add α] [IsRightCancelAdd α]
    (a j : α) : (ComplexShape.down' a).Rel (j + a) j := sorry

/-- A standard downward shape has a canonical incoming index at every degree. -/
@[stacks 01A2 "incoming indices for downward complex shapes"]
instance hasIncoming {α : Type w} [Add α] [IsRightCancelAdd α] (a : α) :
    (ComplexShape.down' a).HasIncoming :=
  ⟨fun j ↦ ⟨j + a, add_rel a j⟩⟩

/-- Subtracting the step gives the canonical outgoing index of an unbounded downward shape. -/
@[stacks 01A2 "canonical outgoing index for downward complex shapes"]
theorem rel_sub {α : Type w} [AddGroup α]
    (a i : α) : (ComplexShape.down' a).Rel i (i - a) := sorry

/-- Over an additive group, a standard downward shape also has outgoing indices. -/
@[stacks 01A2 "outgoing indices for unbounded downward complex shapes"]
instance hasOutgoing {α : Type w} [AddGroup α] (a : α) :
    (ComplexShape.down' a).HasOutgoing :=
  ⟨fun i ↦ ⟨i - a, rel_sub a i⟩⟩

end down'

namespace up

/-- The standard upward complex shape has outgoing indices without additional boundedness
assumptions. -/
@[stacks 01A2 "outgoing indices for standard cochain-complex shapes"]
instance hasOutgoing {α : Type w} [Add α] [IsRightCancelAdd α] [One α] :
    (ComplexShape.up α).HasOutgoing := up'.hasOutgoing 1

/-- Over an additive group, the standard upward complex shape also has incoming indices. -/
@[stacks 01A2 "incoming indices for unbounded standard cochain-complex shapes"]
instance hasIncoming {α : Type w} [AddGroup α] [One α] :
    (ComplexShape.up α).HasIncoming := up'.hasIncoming 1

end up

namespace down

/-- The standard downward complex shape has incoming indices without additional boundedness
assumptions. -/
@[stacks 01A2 "incoming indices for standard chain-complex shapes"]
instance hasIncoming {α : Type w} [Add α] [IsRightCancelAdd α] [One α] :
    (ComplexShape.down α).HasIncoming := down'.hasIncoming 1

/-- Over an additive group, the standard downward complex shape also has outgoing indices. -/
@[stacks 01A2 "outgoing indices for unbounded standard chain-complex shapes"]
instance hasOutgoing {α : Type w} [AddGroup α] [One α] :
    (ComplexShape.down α).HasOutgoing := down'.hasOutgoing 1

end down

end ComplexShape
