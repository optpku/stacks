module

public import ReasLib.FieldTheory.Transcendence.Algebraic
import StacksCheckRecall

@[expose] public section

universe u v

namespace Algebra

/- Exercise 111.20.1: if `K'/K/k` is a tower of field extensions and `K'` is algebraic over `K`,
then `trdeg k K = trdeg k K'`. -/
@[stacks 077F] #check (Algebra.trdeg_eq_of_isAlgebraic :
  ∀ {k : Type u} {K : Type v} {K' : Type v},
    [Field k] → [Field K] → [Field K'] →
    [Algebra k K] → [Algebra k K'] → [Algebra K K'] →
    [IsScalarTower k K K'] → [Algebra.IsAlgebraic K K'] →
    trdeg k K = trdeg k K')

end Algebra
