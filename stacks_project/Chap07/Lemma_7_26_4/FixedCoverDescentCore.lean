/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Coverwise
public import ReasLib.CategoryTheory.Sites.Cover.Family
public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.TypeSheaf

/-!
# Fixed-cover descent recall

The former local glueing core is represented by the general coverwise stack
criterion and the `Type`-valued localized-sheaf stack.  Cover index data and
its slice transport are owned by the two `Sites.Cover` leaves.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.family
#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
#check @CategoryTheory.IsStack.OnSite.Descent.isStackFor_iff
#check @CategoryTheory.GrothendieckTopology.PseudofunctorOver.toDescentData_essSurj
