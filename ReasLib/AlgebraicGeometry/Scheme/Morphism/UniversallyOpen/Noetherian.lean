module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

namespace AlgebraicGeometry.UniversallyOpen

universe u

/-- A flat morphism locally of finite type over a locally Noetherian scheme is
universally open. -/
theorem of_flat_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [Flat f] [LocallyOfFiniteType f] :
    UniversallyOpen f := sorry

end AlgebraicGeometry.UniversallyOpen
