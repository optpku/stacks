module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Fiberwise
import StacksCheckRecall

/-!
# Lemma 15.78.5 (068X)

@stack 068X

The fiberwise global-dimension perfectness criterion is owned by the derived-category
perfectness leaf. This Chapter file is its direct official-label recall.
-/

@[expose] public section

/- Lemma 15.78.5 (068X): uniformly bounded fiber global dimension shifts the target
Tor-amplitude and implies perfectness. -/
@[stacks 068X "Lemma 15.78.5"]
#check @CategoryTheory.isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE

#check @HasGlobalDimensionLE

#print axioms CategoryTheory.isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_fiber_hasGlobalDimensionLE
