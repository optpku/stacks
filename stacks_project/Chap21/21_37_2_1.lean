module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
import StacksCheckRecall

@[expose] public section

/-!
# Equation 21.37.2.1

The derived lower-shriek/inverse-image adjunction identifies maps into exact derived inverse image
with maps out of derived lower-shriek.
-/

/- Equation 21.37.2.1 (07AD):
`(K ⟶ g^* L) ≃ (Lg_! K ⟶ L)`. -/
@[stacks 07AD "derived lower-shriek Hom equivalence"]
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.homEquivSymm

/- The adjunction-oriented form of the same equivalence. -/
#check @RingedSite.Cocontinuous.moduleLowerShriek.derived.homEquiv
