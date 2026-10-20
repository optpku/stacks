/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.Localization
public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.MinimalPrime

/-!
# Geometric Reducedness at Generic Points

This leaf records specialization and generic-point criteria for geometric
reducedness of schemes over a field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- Geometric reducedness at a point is preserved under generization. -/
@[stacks 04KS]
theorem geometricallyReducedAt_of_specializes
    {x x' : X.left}
    (hspecializes : Specializes x' x)
    (hx : geometricallyReducedAt X x) :
    geometricallyReducedAt X x' := sorry

namespace geometricallyReducedAt

/-- A reduced stalk is geometrically reduced when geometric reducedness holds at every
component-generic point specializing to it. -/
@[stacks 04KS]
theorem of_isReduced_stalk_of_genericPoints
    (x : X.left) (hxreduced : _root_.IsReduced (X.left.presheaf.stalk x))
    (hgeneric :
      ∀ x' : X.left,
        x' ∈ genericPoints X.left →
          Specializes x' x →
            geometricallyReducedAt X x') :
    geometricallyReducedAt X x := sorry

end geometricallyReducedAt

namespace geometricallyReduced

/-- A reduced scheme that is geometrically reduced at every component-generic point is
geometrically reduced. -/
@[stacks 04KS]
theorem of_isReduced_of_genericPoints
    [IsReduced X.left]
    (hgeneric :
      ∀ x : X.left,
        x ∈ genericPoints X.left →
          AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x) :
    geometricallyReduced X := sorry

end geometricallyReduced

end AlgebraicGeometry.SchemeOverField
