module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.7 (0F8Q): the Berthelot-Ogus construction induces an additive endofunctor
`Lη_I : D(𝒪_X) ⥤ D(𝒪_X)`, computed naturally by `η_I` on complexes with termwise monic
`I`-action. -/
@[stacks 0F8Q]
#check @IdealSheaf.Eta.Derived.functor

@[stacks 0F8Q "natural computation rule"]
#check @IdealSheaf.Eta.Derived.comparison

@[stacks 0F8Q "morphism computation rule"]
#check @IdealSheaf.Eta.Derived.map_toDerived

#check @IdealSheaf.Eta.Derived.additive
#check @IdealSheaf.Eta.Derived.toDerived_isLocalization
#check @IdealSheaf.IsRegularPrincipal.isInvertible
