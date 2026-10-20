module

import ReasLib.CategoryTheory.Filtration.Derived.Finite.Compatibility
import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Comparison
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.Forget

/-!
# Equation 13.26.13.8

The source-facing comparison is the left-exact, T-specific forgetful owner in `ReasLib`; the
generic right-derived uniqueness comparison remains available as its construction tool.
-/

/- Equation 13.26.13.8 (`015V`): forgetting a finite filtration commutes with the filtered
right-derived functor. -/
open CategoryTheory.FilteredObject.FiniteDerived.Plus.LeftExact.Forget
@[stacks 015V] #check @forgetIso
#check @forgetIso.fac
#check @forgetIso.fac_app
#check @forgetIso.inv_fac
#check @forgetIso.inv_fac_app

/- The certificate-taking generic uniqueness comparison remains available for noncanonical
localization data. -/
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.Forget.RightDerived.iso
#check @CategoryTheory.FilteredObject.FiniteDerived.Plus.Forget.RightDerived.canonicalIso

end CategoryTheory.FilteredComplex.RightDerived.Finite.Forget
