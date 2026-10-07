module

public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius
import StacksCheckRecall

universe u

variable (k : Type u) [Field k] [Fintype k]

/- Definition 64.3.8: the arithmetic Frobenius is the map
frob_k : AlgebraicClosure k → AlgebraicClosure k, x ↦ x^q of
G_k = Gal(AlgebraicClosure k / k), where q = Fintype.card k. -/
@[stacks 03SU] #check
  (FiniteField.arithmeticFrobenius k : Gal(AlgebraicClosure k / k))
#check
  (FiniteField.frobeniusAlgEquivOfAlgebraic_apply k (AlgebraicClosure k) :
    ∀ x : AlgebraicClosure k,
      FiniteField.arithmeticFrobenius k x = x ^ Fintype.card k)
