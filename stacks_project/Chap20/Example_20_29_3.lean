/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Filtered.Truncation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Truncation

/- [stacks 0BKM] Example 20.29.3: the canonical truncation filtration of a derived
`𝒪_X`-module gives, after the standard renumbering
`E'_r^{i,j} = E_{r-1}^{-j,i+2j}`, a spectral sequence
`E'_2^{i,j} = H^i(X, H^j(K))`. For bounded-below `K` it is bounded and converges to
hypercohomology. On a bounded-below complex representative it compares, from `E₂` onward, with
the second Cartan--Eilenberg spectral sequence. -/

#check @DerivedCategory.TruncationFilteredPreimage.stageIso
#check @Realization
#check @Realization.filtered
#check @Realization.originalSequence
#check @Realization.sequence
#check @Realization.gradedPieceIso
#check @CohomologicalSpectralSequence.Renumber.entryIso
#check @Realization.pageTwoIso
#check @Realization.targetIso
#check @Realization.isAssociated
#check @Realization.isRenumbering
@[stacks 0BKM] #check @Realization.nonempty
#check @Realization.isBounded
#check @Realization.finite
#check @Realization.converges
#check @Realization.cartanEilenbergComparison

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.SpectralSequence.Truncation
