module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent

/-!
# Reduced components and their scheme-theoretic intersections

This module gives an ambient ideal-sheaf presentation of the reduced irreducible components of a
closed subscheme and of finite scheme-theoretic intersections of those components.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

noncomputable section

/-- The reduced irreducible component of `D.subscheme` indexed by `i`, regarded as a closed
subscheme of the ambient scheme. -/
noncomputable def reducedComponent (D : X.IdealSheafData)
    (i : irreducibleComponents D.subscheme) : X.IdealSheafData :=
  (vanishingIdeal (D.subscheme.irreducibleComponentClosed i)).map D.subschemeι

/-- The ambient ideal sheaf of a reduced component is the vanishing ideal of the closure of its
image in the ambient scheme. -/
theorem reducedComponent_eq_vanishingIdeal (D : X.IdealSheafData)
    (i : irreducibleComponents D.subscheme) :
    D.reducedComponent i =
      vanishingIdeal (.closure (D.subschemeι '' D.subscheme.irreducibleComponentClosed i)) := sorry

/-- A reduced component, equipped with its canonical reduced closed-subscheme structure, is a
reduced scheme. -/
instance instIsReducedSubschemeReducedComponent (D : X.IdealSheafData)
    (i : irreducibleComponents D.subscheme) :
    IsReduced (D.reducedComponent i).subscheme := sorry

/-- The scheme-theoretic intersection of the reduced components selected by the finite set `J`. -/
noncomputable def componentIntersection (D : X.IdealSheafData)
    (J : Finset (irreducibleComponents D.subscheme)) : X.IdealSheafData :=
  ⨆ j : J, D.reducedComponent j

/-- A finite component intersection is represented by the supremum of the component ideal
sheaves. -/
theorem componentIntersection_def (D : X.IdealSheafData)
    (J : Finset (irreducibleComponents D.subscheme)) :
    D.componentIntersection J = ⨆ j : J, D.reducedComponent j := sorry

/-- The support of a finite component intersection is the intersection of the component
supports. -/
theorem support_componentIntersection (D : X.IdealSheafData)
    (J : Finset (irreducibleComponents D.subscheme)) :
    (D.componentIntersection J).support = ⨅ j : J, (D.reducedComponent j).support := sorry

end

end AlgebraicGeometry.Scheme.IdealSheafData
