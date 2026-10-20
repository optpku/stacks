module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange

/-!
# Base change of relatively perfect derived modules on algebraic spaces

Relative perfectness for a flat, locally finitely presented morphism of algebraic
spaces is preserved by derived pullback along an arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo

/-- Derived pullback along a base change preserves relative perfectness over a flat,
locally finitely presented morphism of algebraic spaces. -/
theorem baseChange {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (g : Y' ⟶ Y) (K : ModuleDerived X) (hK : IsPerfectRelativeTo f K) :
    IsPerfectRelativeTo (Limits.pullback.snd f g)
      ((ModuleDerived.pullback (Limits.pullback.fst f g)).obj K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfectRelativeTo
