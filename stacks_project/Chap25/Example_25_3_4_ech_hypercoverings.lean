module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Construction
import StacksCheckRecall

/-!
# Cech hypercoverings

The reusable construction is owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Construction`.
-/

open CategoryTheory

/- Example 25.3.4 (Cech hypercoverings): a covering fixed-target family determines its Cech
hypercovering. -/
@[stacks 01G6] #check @Hypercovering.cech
