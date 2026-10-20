module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange.Composition
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.19.4

Vertical composition of derived base-change morphisms is owned by the reusable ringed-site
base-change composition API.
-/

/- Remark 21.19.4 (0E46): for two vertically composable base-change squares, the composite of
the two canonical derived base-change morphisms is the canonical morphism for the outer
rectangle. -/
@[stacks 0E46]
#check @RingedSite.Hom.DerivedBaseChange.Composition.map_eq

#check @RingedSite.Hom.DerivedBaseChange.Composition.squareIso
#check @RingedSite.Hom.DerivedBaseChange.Composition.map
#check @RingedSite.Hom.DerivedBaseChange.Composition.map_isMap
