module

import StacksCheckRecall
public import ReasLib.RingTheory.KrullDimension.Relative.FinitePresentation

@[expose] public section

/-!
# Finite-presentation relative-dimension locus recall

The bounded locus is owned by `relativeDimensionAtLELocus`; its openness and quasi-compactness
belong to the finite-presentation ReasLib leaf rather than to a chosen descent presentation.

@stack 00QJ
-/

/- Lemma 10.125.8, tag 00QJ: for a finitely presented algebra, the locus
`relativeDimensionAtLELocus R S n` is open and quasi-compact. -/
@[stacks 00QJ "finite-presentation relative-dimension locus"]
#check @RelativeDimensionAtLELocus.isOpen_isCompact_of_finitePresentation
