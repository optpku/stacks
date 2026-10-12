/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open scoped CategoryTheory DerivedCategory.CohomologyIn

universe w v u

/- Lemma 13.17.1 (`06UQ`) (1): the canonical full subcategory of `D(A)` consists of objects
whose cohomology lies degreewise in the chosen weak Serre subcategory. -/
@[stacks 06UQ "(1)"] #check DerivedCategory.cohomologyIn
@[stacks 06UQ "(1)"] #check DerivedCategory.CohomologyIn
@[stacks 06UQ "(1)"] #check DerivedCategory.CohomologyIn.mem_iff

/- Lemma 13.17.1 (`06UQ`) (2): the bounded-below, bounded-above, and bounded versions use the
same degreewise cohomology condition in their canonical derived categories. -/
@[stacks 06UQ "(2)"] #check DerivedCategory.Plus.CohomologyIn
@[stacks 06UQ "(2)"] #check DerivedCategory.Minus.CohomologyIn
@[stacks 06UQ "(2)"] #check DerivedCategory.Bounded.CohomologyIn
@[stacks 06UQ "(2)"] #check DerivedCategory.Plus.CohomologyIn.mem_iff
@[stacks 06UQ "(2)"] #check DerivedCategory.Minus.CohomologyIn.mem_iff
@[stacks 06UQ "(2)"] #check DerivedCategory.Bounded.CohomologyIn.mem_iff

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]

/- Lemma 13.17.1 (`06UQ`) (1): the unbounded cohomology-in property is strictly full, stable
under retracts, and triangulated. -/
@[stacks 06UQ "(1)"]
#check (inferInstance : (DerivedCategory.cohomologyIn P).IsClosedUnderIsomorphisms)

@[stacks 06UQ "(1)"]
#check (inferInstance : (DerivedCategory.cohomologyIn P).IsStableUnderRetracts)

@[stacks 06UQ "(1)"]
#check (inferInstance : (DerivedCategory.cohomologyIn P).IsTriangulated)

/- Lemma 13.17.1 (`06UQ`) (2): each bounded cohomology-in property inherits the same three
closure properties from the unbounded owner. -/
@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Plus.cohomologyIn P).IsClosedUnderIsomorphisms)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Plus.cohomologyIn P).IsStableUnderRetracts)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Plus.cohomologyIn P).IsTriangulated)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Minus.cohomologyIn P).IsClosedUnderIsomorphisms)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Minus.cohomologyIn P).IsStableUnderRetracts)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Minus.cohomologyIn P).IsTriangulated)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Bounded.cohomologyIn P).IsClosedUnderIsomorphisms)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Bounded.cohomologyIn P).IsStableUnderRetracts)

@[stacks 06UQ "(2)"]
#check (inferInstance : (DerivedCategory.Bounded.cohomologyIn P).IsTriangulated)
