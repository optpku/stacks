module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Absolute quasi-separatedness permanence for algebraic spaces

Morphisms out of absolutely quasi-separated algebraic spaces are quasi-separated.
Pullbacks of absolutely quasi-separated algebraic spaces are absolutely
quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace QuasiSeparated

/-- A morphism of algebraic spaces out of an absolutely quasi-separated source is
quasi-separated. -/
instance (priority := low) of_isAbsolutelyQuasiSeparated {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAbsolutelyQuasiSeparated X] :
    QuasiSeparated f :=
  sorry

end QuasiSeparated

namespace IsAbsolutelyQuasiSeparated

/-- The vertex of an `IsPullback` square of algebraic spaces is quasi-separated when
the two factors are quasi-separated. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
    (h : IsPullback pZ pX g f) : IsAbsolutelyQuasiSeparated P :=
  sorry

/-- The chosen fibre product of quasi-separated algebraic spaces is quasi-separated. -/
instance (priority := low) instPullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
    [HasPullback f g] : IsAbsolutelyQuasiSeparated (pullback f g) :=
  sorry

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
