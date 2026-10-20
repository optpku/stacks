module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Compact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Proposition 75.16.1 -/
@[stacks 09M8] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isCompactObject_iff_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (E : DerivedQCoh X),
      IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj)
