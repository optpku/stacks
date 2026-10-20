module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Compact.LocalizedGenerator
import StacksCheckRecall

@[expose] public section

/- Lemma 20.53.1 (0F5Z): if cohomology on `U` has a uniform upper vanishing bound and each
cohomology functor preserves arbitrary coproducts, then `j_!𝒪_U[0]` is compact in `D(𝒪_X)`. -/
@[stacks 0F5Z]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalizedGenerator.isCompactObject

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.localizedGenerator
#check @AlgebraicGeometry.RingedSpace.Modules.localizedGenerator
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.HasFiniteDimension
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.PreservesCoproducts
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.hasFiniteDimension_iff
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.preservesCoproducts_iff
