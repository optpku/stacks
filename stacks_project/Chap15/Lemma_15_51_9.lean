module

public import ReasLib.RingTheory.FormalFiber.Geometric.Reduced
import StacksCheckRecall

/-!
# Lemma 15.51.9

@stack 0BIW
-/

@[expose] public section

/- Lemma 15.51.9: geometric reducedness satisfies the five formal-fiber permanence laws. -/
@[stacks 0BIW "geometrically reduced formal-fiber laws"]
#check @FieldAlgebraProperty.geometricallyReduced.formalFiberLaws
