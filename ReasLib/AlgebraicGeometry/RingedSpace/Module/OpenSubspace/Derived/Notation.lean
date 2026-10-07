module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived

@[expose] public section

/-!
# Source-facing notation for derived restriction

The canonical derived restriction of an object is the functor
`moduleRestrictionToOpenDerived`.  Stacks statements also use a chosen-complex view of that
object.  This leaf owns only the scoped notation for that view; the comparison with the canonical
functor is `OpenSubspace.Restriction.derivedObjIsoRestricted`.
-/

namespace RingedSpaceDerivedRestriction

/-- `K↾[U]` is the chosen-complex view of the derived restriction of `K` to `U`. -/
scoped notation:max K:max "↾[" U "]" =>
  AlgebraicGeometry.RingedSpace.restrictedModuleDerivedOnOpen _ U K

end RingedSpaceDerivedRestriction

end
