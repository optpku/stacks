module

public import ReasLib.FieldTheory.Polynomial.SeparableDegree
import StacksCheckRecall

@[expose] public section

/- Lemma 9.12.4 (Tag 09H3): an irreducible polynomial is separable exactly when its roots in an
algebraic closure are pairwise distinct. -/
@[stacks 09H3]
#check Polynomial.irreducibleSeparableIffNodupRootsMapAlgebraicClosure
