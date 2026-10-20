module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Local
import StacksCheckRecall

@[expose] public section

/- Lemma 21.47.2 (1) (08G6): strictly perfect models on a cover of a terminal object imply
perfectness. -/
@[stacks 08G6 "(1)"]
#check @RingedSite.DerivedCategory.isPerfect_of_cover_of_isTerminal

/- Lemma 21.47.2 (2) (08G6): every complex representing a perfect derived module sheaf is
perfect. -/
@[stacks 08G6 "(2)"]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.of_representation

#check @RingedSite.DerivedCategory.HasStrictlyPerfectModel
#check @RingedSite.DerivedCategory.isPerfect_iff_locally_hasStrictlyPerfectModel
