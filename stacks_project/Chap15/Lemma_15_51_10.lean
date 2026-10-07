module

public import ReasLib.RingTheory.FormalFiber.Geometric.Normal
import StacksCheckRecall

/-!
# Lemma 15.51.10

@stack 0BIX
-/

@[expose] public section

/- Lemma 15.51.10: geometric normality satisfies the five formal-fiber permanence laws. -/
@[stacks 0BIX "geometrically normal formal-fiber laws"]
#check @FieldAlgebraProperty.geometricallyNormal.formalFiberLaws
