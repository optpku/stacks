module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.SectionsWithSupport.KInjective
import StacksCheckRecall

@[expose] public section

/- Lemma 20.34.3 (0G6Z): the termwise sections-with-support functor for a closed subset sends
K-injective cochain complexes of ambient modules to K-injective complexes on the closed subset.
The bundled ReasLib owner exposes both the mapped complex and its canonical K-injective
instance. -/

@[stacks 0G6Z]
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport.mapComplex
#check @AlgebraicGeometry.RingedSpace.ClosedSubset.SectionsWithSupport.mapIsKInjective
