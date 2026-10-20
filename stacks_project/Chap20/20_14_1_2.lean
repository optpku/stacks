module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Cohomology
import StacksCheckRecall

@[expose] public section

/- 20.14.1.2 / 01FA: an `f`-map `φ : G ⟶ f_* F` induces the canonical
`Γ(Y, 𝒪_Y)`-linear morphism on global degree-`i` cohomology. -/

@[stacks 01FA "cohomology map of an f-map"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.cohomologyMapOfFMap
