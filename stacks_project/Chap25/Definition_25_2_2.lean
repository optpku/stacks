module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
import StacksCheckRecall

/-!
# Definition 25.2.2

The reusable construction is owned at the topology-independent formal-coproduct layer.
-/

/- Definition 25.2.2: the presheaf associated to a semi-representable family is the coproduct
of its representable summands. -/
@[stacks 01G1] #check @CategoryTheory.Limits.FormalCoproduct.toPresheaf
