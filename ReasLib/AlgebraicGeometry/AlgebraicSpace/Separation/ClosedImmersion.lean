module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Closed immersions of algebraic spaces are separated

Every closed immersion of algebraic spaces over a scheme is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- A closed immersion of algebraic spaces is separated. -/
@[instance] theorem separated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsClosedImmersion f] : Separated f :=
  sorry

/-- Closed immersions of algebraic spaces are separated as a morphism property. -/
theorem le_separated {S : Scheme.{u}} :
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) ≤
      (@Separated S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
