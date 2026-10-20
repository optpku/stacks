/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.AdjunctionComparison
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Remark 20.42.11 is the ringed-space specialization of the categorical comparison owner in
`CategoryTheory.Adjunction`.  The concrete derived adjunction and tensor comparison are supplied
by the opens ringed-site development. -/
@[stacks 0B69]
#check @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison

/- The mate description is part of the shared owner API and is recalled here for downstream use. -/
#check @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison_spec

end AlgebraicGeometry.RingedSpace
