/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
import StacksCheckRecall

/-!
# Definition 12.24.5

Source-facing entry point for the filtration on the cohomology of a filtered complex. The
reusable construction is owned by `FilteredComplex.inducedCohomologyFiltration` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

section

variable [HasImages 𝒜] [CategoryWithHomology 𝒜]

/- Definition 12.24.5: the `p`-th stage of the decreasing filtration on
`K.underlying.homology n` is `imageSubobject (K.cohomologyMap p n)`. -/
@[stacks 012P]
#check (FilteredComplex.inducedCohomologyFiltration :
  ∀ (K : FilteredComplex 𝒜) (n : ℤ), DecreasingFiltration (K.underlying.homology n))

#check FilteredComplex.cohomologyMap
#check FilteredComplex.cohomologyMap_factorization
#check FilteredComplex.cohomologyMap_naturality
#check FilteredComplex.inducedCohomologyFiltration_obj

end

/- The cochain specialization is directly expressed by the general `FilteredComplex` API. -/
#check @FilteredComplex.underlying
#check @FilteredComplex.stage
#check @FilteredComplex.stageInclusion
#check @FilteredComplex.stageComparison
#check @FilteredComplex.gradedPiece

end CategoryTheory
