module

public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws

@[expose] public section

universe u v

namespace FieldAlgebraProperty

/-- The intrinsic local-complete-intersection property of a field algebra, independent of its
displayed ground field. -/
abbrev localCompleteIntersectionRing : FieldAlgebraProperty.{u, v} :=
  fun _ R ↦ IsLocalCompleteIntersectionRing R

namespace localCompleteIntersectionRing

/-- Intrinsic local complete intersections satisfy the five formal-fiber permanence laws. -/
@[stacks 0BJP "local complete intersection formal-fiber laws"]
theorem formalFiberLaws :
    (localCompleteIntersectionRing : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end localCompleteIntersectionRing

attribute [instance] FieldAlgebraProperty.localCompleteIntersectionRing.formalFiberLaws

end FieldAlgebraProperty
