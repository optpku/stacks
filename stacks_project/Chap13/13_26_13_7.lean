/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Finite.Compatibility
import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Comparison
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.Graded

/-!
# Equation 13.26.13.7

The source-facing comparison is the left-exact, T-specific owner in `ReasLib`; the generic
right-derived uniqueness comparison remains available as its construction tool.
-/

/- Equation 13.26.13.7 (`015U`): the `p`-th associated-graded piece commutes with the filtered
right-derived functor. -/
open CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.GradedPiece
@[stacks 015U] #check @gradedPieceIso
#check @gradedPieceIso.fac
#check @gradedPieceIso.fac_app
#check @gradedPieceIso.inv_fac
#check @gradedPieceIso.inv_fac_app

/- The certificate-taking generic uniqueness comparison remains available for noncanonical
localization data. -/
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.GradedPiece.RightDerived.iso
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.GradedPiece.RightDerived.canonicalIso

end CategoryTheory.FilteredComplex.RightDerived.Finite.Graded
