module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent.Cohomology
import StacksCheckRecall

@[expose] public section

/- Lemma 21.45.7 (08FX) (1): the top cohomology sheaf of an `m`-pseudo-coherent object in
`D^{≤ m}` is of finite type. -/
@[stacks 08FX "(1)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.topCohomology_isFiniteType

/- Lemma 21.45.7 (08FX) (2): degree `m + 1` cohomology of an `m`-pseudo-coherent object in
`D^{≤ m + 1}` is finitely presented. -/
@[stacks 08FX "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsMPseudoCoherent.nextCohomology_isFinitePresentation
