/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Complex.FiniteAcyclic
import StacksCheckRecall

@[expose] public section

/- Definition 13.13.2 (`05RZ`): finite filtered quasi-isomorphisms and acyclic objects are the
canonical inverse-image properties of the associated-graded homotopy functor.  ReasLib owns both
the functor and the characterization; no chapter aliases or caret notation are needed here. -/
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.Forget.functor
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.AssociatedGraded.functor
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.AssociatedGraded.homotopy
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.Homotopy.quasiIso
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.Homotopy.quasiIso_iff
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.Homotopy.acyclic
@[stacks 05RZ] #check @CategoryTheory.FilteredObject.Finite.Acyclic.iff_subcategory
