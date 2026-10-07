module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange.HorizontalComposition
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.19.5

Horizontal composition of derived base-change morphisms is the ringed-site specialization of the
general compatibility of adjunction mates with pasted squares.
-/

/- Remark 21.19.5 (0E47): for two horizontally composable squares of ringed topoi, the two
canonical derived base-change morphisms compose to the canonical morphism for the outer
rectangle. -/
@[stacks 0E47]
#check @RingedSite.Hom.DerivedBaseChange.HorizontalComposition.Canonical.map_eq

#check @CategoryTheory.DerivedBaseChange.HorizontalComposition.map_eq
#check @RingedSite.Hom.DerivedBaseChange.HorizontalComposition.Canonical.squareIso
#check @RingedSite.Hom.DerivedBaseChange.HorizontalComposition.Canonical.map
#check @RingedSite.Hom.DerivedBaseChange.HorizontalComposition.Canonical.map_isMap
