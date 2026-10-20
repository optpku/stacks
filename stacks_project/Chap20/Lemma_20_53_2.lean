module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Compact
import StacksCheckRecall

@[expose] public section

/- Lemma 20.53.2 (09J7) (1): a perfect object is compact relative to ambient coproducts whose
coproduct object is bounded below. -/
@[stacks 09J7 "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isCompactOnBoundedBelow

/- Lemma 20.53.2 (09J7) (2): under finite module-cohomological dimension, every perfect object
is compact in the ambient derived category. -/
@[stacks 09J7 "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isCompactObject

#check @CategoryTheory.IsCompactObjectOn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.bounded
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.boundedBelow
#check @AlgebraicGeometry.RingedSpace.Module.HasFiniteCohomologicalDimension
#check @AlgebraicGeometry.RingedSpace.Module.hasFiniteCohomologicalDimension_iff
