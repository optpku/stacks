module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Generators
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.7 (05NI) (1): every module sheaf on a ringed space is an epimorphic image of a
coproduct of localized structure-module generators. -/
@[stacks 05NI "(1)"]
#check @AlgebraicGeometry.RingedSpace.Modules.exists_epi_from_localizedGenerators

/- Lemma 17.17.7 (05NI) (2): every module sheaf on a ringed space is an epimorphic image of a
flat module sheaf. -/
@[stacks 05NI "(2)"]
#check @AlgebraicGeometry.RingedSpace.Modules.exists_epi_from_flat

-- Each localized generator is itself canonically flat.
#check @AlgebraicGeometry.RingedSpace.Modules.localizedGenerator_isFlat

-- The reusable object property carries its finite-coproduct and epimorphic-cover instances.
#check @AlgebraicGeometry.RingedSpace.Modules.localizedGeneratorCoproducts
