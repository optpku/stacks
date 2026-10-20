module

public import ReasLib.RingTheory.FormalFiber.GorensteinProperty
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.23.1: the intrinsic property `IsGorensteinRing R`, viewed as a field-algebra
property independent of the displayed field, satisfies formal-fiber laws (A), (B), (C), (D),
and (E). -/
@[stacks 0BJN]
#check
  (FieldAlgebraProperty.gorensteinRing.formalFiberLaws :
    (FieldAlgebraProperty.gorensteinRing : FieldAlgebraProperty.{u, u}).FormalFiberLaws)
