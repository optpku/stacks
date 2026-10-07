module

public import ReasLib.RingTheory.FormalFiber.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.23.3: the intrinsic property `IsLocalCompleteIntersectionRing R`, viewed as a
field-algebra property independent of the displayed field, satisfies formal-fiber laws (A),
(B), (C), (D), and (E). -/
@[stacks 0BJP] #check
  (FieldAlgebraProperty.localCompleteIntersectionRing.formalFiberLaws :
    (FieldAlgebraProperty.localCompleteIntersectionRing :
      FieldAlgebraProperty.{u, u}).FormalFiberLaws)
