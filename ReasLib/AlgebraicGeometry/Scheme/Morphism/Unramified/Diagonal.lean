module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Diagonal criterion for unramified morphisms

An unramified morphism has open diagonal, and an open diagonal together with the appropriate
finiteness hypothesis characterizes unramified and G-unramified morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The diagonal of an unramified morphism is an open immersion. -/
theorem isOpenImmersion_diagonal_of_unramified (f : X ⟶ S) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) :=
  inferInstance

/-- A locally finite type morphism with open diagonal is unramified. -/
theorem unramified_of_locallyOfFiniteType_of_isOpenImmersion_diagonal
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)] :
    Unramified f :=
  { toFormallyUnramified := inferInstance
    toLocallyOfFiniteType := inferInstance }

/-- A locally finite presentation morphism with open diagonal is G-unramified. -/
theorem gUnramified_of_locallyOfFinitePresentation_of_isOpenImmersion_diagonal
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [IsOpenImmersion (pullback.diagonal f)] :
    GUnramified f :=
  { toFormallyUnramified := inferInstance
    toLocallyOfFinitePresentation := inferInstance }

end AlgebraicGeometry
