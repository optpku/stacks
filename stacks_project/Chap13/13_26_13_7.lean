/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Finite.Compatibility
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.Graded

/-!
# Equation 13.26.13.7

The canonical comparison is owned together with its forward and inverse factorization formulas.
-/

/- Equation 13.26.13.7 (`015U`): the `p`-th associated-graded piece commutes with a bounded-below filtered
right-derived functor when the two displayed composites are right-derived functors of the same
homotopy-level source.  The canonical comparison and its factorization equations are: -/
@[stacks 015U] #check @canonicalIso

/- The certificate-taking comparison remains available for noncanonical localization data. -/
#check @iso

#check @canonicalIso.fac

#check @canonicalIso.fac_app

#check @canonicalIso.inv_fac

#check @canonicalIso.inv_fac_app

end CategoryTheory.FilteredComplex.RightDerived.Finite.Graded
