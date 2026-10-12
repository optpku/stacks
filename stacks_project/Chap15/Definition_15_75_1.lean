/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import StacksCheckRecall

/-!
# Definition 15.75.1

@stack 0657

The reusable perfect-complex API is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Perfect`.
-/

@[expose] public section

/- Definition 15.75.1 (1), tag `0657`: perfect derived objects. -/
@[stacks 0657 "(1), perfect derived object"]
#check @DerivedCategory.IsPerfect

/- Definition 15.75.1 (2), tag `0657`: perfect modules. -/
@[stacks 0657 "(2), perfect module"]
#check @ModuleCat.IsPerfect
