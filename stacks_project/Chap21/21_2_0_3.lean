/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 21.2.0.3 (071E): global sheaf cohomology is computed by applying global sections to a
chosen injective resolution and taking homology. -/
@[stacks 071E "global sheaf cohomology from an injective resolution"]
#check @Sheaf.globalCohomology_isomorphic_homology_of_injectiveResolution

/- The canonical cohomology functor remains the primary owner of the left-hand side. -/
#check @Sheaf.functorH
