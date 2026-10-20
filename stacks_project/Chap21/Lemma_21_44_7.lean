module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalHomotopy
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.7 (08FQ): a bounded-below strictly perfect complex locally lifts through a
homology isomorphism above the bound and an epimorphism at the bound, up to homotopy. -/
@[stacks 08FQ]
#check @RingedSite.CochainComplex.IsStrictlyPerfect.Lift.at_of_isStrictlyGE
