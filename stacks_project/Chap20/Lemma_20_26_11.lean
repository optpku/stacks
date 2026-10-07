module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.UpperResolution.Colimit

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.Modules

/- Lemma 20.26.11 (079T): localized-generator upper-resolution towers exist and have
quasi-isomorphic colimit comparison. -/
@[stacks 079T "localized-generator upper-resolution existence"]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.UpperTruncation.exists_localizedGeneratorResolution

#check @AlgebraicGeometry.RingedSpace.CochainComplex.UpperTruncation.fromColimit_quasiIso
#check @SheafOfModules.RingedSite.exists_upperResolution_of_localizedGenerators

end
