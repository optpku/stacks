module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.5 (0FPT): the canonical K-flat derived tensor product makes the derived category
of modules on a commutative ringed site symmetric monoidal. -/
@[stacks 0FPT]
#check @RingedSite.Hom.ModuleDerived.symmetricCategory

#check @RingedSite.Hom.ModuleDerived.monoidalCategory
