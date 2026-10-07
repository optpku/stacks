module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.RingTheory.RingHom.Perfect.Regular

/-!
# Perfect morphisms over regular schemes

A locally finite-type morphism to a regular scheme is perfect.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- A locally finite-type morphism of schemes with regular target is perfect. -/
@[instance]
theorem isPerfect_of_regular
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Regular S] [LocallyOfFiniteType f] :
    LocallyOfType RingHom.IsPerfectRingMap f := sorry

end AlgebraicGeometry.LocallyOfFiniteType
