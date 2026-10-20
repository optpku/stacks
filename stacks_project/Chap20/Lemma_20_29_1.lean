module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

/- [stacks 0BKK] Lemma 20.29.1: a filtered complex of `𝒪_X`-modules has an unbounded
hypercohomology spectral sequence. Its first page is the hypercohomology of the graded pieces;
under eventual vanishing at high stages and stabilization at low stages, it is bounded and
converges to the hypercohomology of the underlying complex. -/

#check @Filtered.model
#check @Filtered.modelMap
#check @StageCohomology.eventuallyVanishesAbove
#check @StageCohomology.eventuallyStabilizesBelow
#check @SpectralSequence.Realization
#check @CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.isAssociated
#check @SpectralSequence.Realization.Map
#check @SpectralSequence.Realization.pageOneIso
#check @SpectralSequence.Realization.targetIso
@[stacks 0BKK] #check @SpectralSequence.Realization.nonempty
#check @SpectralSequence.Realization.existsMap
#check @SpectralSequence.Realization.isBounded
#check @SpectralSequence.Realization.finite
#check @SpectralSequence.Realization.converges

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
