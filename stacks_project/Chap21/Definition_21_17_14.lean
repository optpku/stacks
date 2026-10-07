module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tor
import StacksCheckRecall

@[expose] public section

/- Definition 21.17.14 (08FF): for module sheaves `F` and `G` over a commutative ringed site,
`Tor_p(F, G)` is degree `-p` homology of the canonical two-variable derived tensor product. -/

@[stacks 08FF]
#check @RingedSite.Hom.ModuleDerived.tor

#check @RingedSite.Hom.ModuleDerived.torFunctor
#check @RingedSite.Hom.ModuleDerived.torObj
#check @CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.tor

end
