/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Filtered
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace.moduleDerivedPushforward

/- [stacks 0FLL] Lemma 20.29.5: a filtered complex of `𝒪_X`-modules has an unbounded
derived-pushforward spectral sequence along `f : X ⟶ Y`. Its first page is the derived
pushforward cohomology of the graded pieces; under eventual vanishing at high stages and
stabilization at low stages, it is bounded and converges to the derived pushforward cohomology of
the underlying complex. -/

#check @Filtered.model
#check @Filtered.modelMap
#check @StageCohomology.eventuallyVanishesAbove
#check @StageCohomology.eventuallyStabilizesBelow
#check @SpectralSequence.Realization
#check @CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization.isAssociated
#check @SpectralSequence.Realization.Map
#check @SpectralSequence.Realization.pageOneIso
#check @SpectralSequence.Realization.targetIso
@[stacks 0FLL] #check @SpectralSequence.Realization.nonempty
#check @SpectralSequence.Realization.existsMap
#check @SpectralSequence.Realization.isBounded
#check @SpectralSequence.Realization.finite
#check @SpectralSequence.Realization.converges

end AlgebraicGeometry.RingedSpace.moduleDerivedPushforward
