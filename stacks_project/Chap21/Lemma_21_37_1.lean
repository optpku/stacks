module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.1

For a continuous and cocontinuous site functor, module inverse image is modeled directly from the
continuous presentation.  The conclusion is objectwise positive-degree cohomology vanishing; it
does not assert total acyclicity and does not require a representably flat bundled morphism of
ringed sites.
-/

open CategoryTheory

/- Lemma 21.37.1 (0D6X): inverse image of an injective module has zero cohomology in every
positive degree over every object of the source site. -/
@[stacks 0D6X]
#check @RingedSite.Cocontinuous.moduleInverseImage.higherCohomology_isZero_of_injective

/- The reusable continuous-presentation owner of module inverse image. -/
#check @RingedSite.Cocontinuous.moduleInverseImage

/- Forgetting module structure identifies this inverse image with continuous sheaf
pushforward. -/
#check @RingedSite.Cocontinuous.moduleInverseImage.underlyingIso

/- Objectwise cohomology is the canonical universe-flexible `H^n(U, -)` owner. -/
#check @CategoryTheory.Sheaf.cohomologyOverObject
