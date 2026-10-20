module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramified scheme morphisms

This file owns the scheme-level unramified and G-unramified properties, built
from Mathlib's formal-unramifiedness and local finite-type/presentation APIs.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A scheme morphism is unramified when it is formally unramified and locally of finite type. -/
class Unramified (f : X ⟶ S) : Prop extends FormallyUnramified f, LocallyOfFiniteType f

/-- Formal unramifiedness and local finite type provide an unramified structure. -/
instance instUnramified [FormallyUnramified f] [LocallyOfFiniteType f] :
    Unramified f := sorry

/-- Characterize unramifiedness by formal unramifiedness and local finite type. -/
theorem unramified_iff_formallyUnramified_and_locallyOfFiniteType
    (f : X ⟶ S) :
    Unramified f ↔ FormallyUnramified f ∧ LocallyOfFiniteType f := sorry

/-- An unramified morphism is formally unramified. -/
theorem Unramified.formallyUnramified
    (h : Unramified f) :
    FormallyUnramified f := sorry

/-- An unramified morphism is locally of finite type. -/
theorem Unramified.locallyOfFiniteType
    (h : Unramified f) :
    LocallyOfFiniteType f := sorry

/-- A scheme morphism is G-unramified when it is formally unramified and locally of finite
presentation. -/
class GUnramified (f : X ⟶ S) : Prop extends FormallyUnramified f, LocallyOfFinitePresentation f

/-- Formal unramifiedness and local finite presentation provide a G-unramified structure. -/
instance instGUnramified [FormallyUnramified f] [LocallyOfFinitePresentation f] :
    GUnramified f := sorry

/-- A G-unramified morphism is unramified. -/
instance instUnramifiedOfGUnramified [GUnramified f] :
    Unramified f := sorry

/-- Characterize G-unramifiedness by unramifiedness and local finite presentation. -/
theorem gUnramified_iff_unramified_and_locallyOfFinitePresentation
    (f : X ⟶ S) :
    GUnramified f ↔ Unramified f ∧ LocallyOfFinitePresentation f := sorry

/-- Characterize G-unramifiedness by formal unramifiedness and local finite presentation. -/
theorem gUnramified_iff_formallyUnramified_and_locallyOfFinitePresentation
    (f : X ⟶ S) :
    GUnramified f ↔ FormallyUnramified f ∧ LocallyOfFinitePresentation f := sorry

/-- A G-unramified morphism is unramified. -/
theorem GUnramified.unramified
    (h : GUnramified f) :
    Unramified f := sorry

/-- A G-unramified morphism is formally unramified. -/
theorem GUnramified.formallyUnramified
    (h : GUnramified f) :
    FormallyUnramified f := sorry

/-- A G-unramified morphism is locally of finite type. -/
theorem GUnramified.locallyOfFiniteType
    (h : GUnramified f) :
    LocallyOfFiniteType f := sorry

/-- A G-unramified morphism is locally of finite presentation. -/
theorem GUnramified.locallyOfFinitePresentation
    (h : GUnramified f) :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry
