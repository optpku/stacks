module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SmoothLocal
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 100.7.2: let `X` be an algebraic stack. Let `P` be a property of
schemes which is local in the smooth topology. We say `X` has property `P` if
any of the equivalent conditions of Lemma 100.7.1 hold. -/
@[stacks 04YG] #check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (P : CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
    [P.IsLocal AlgebraicGeometry.Scheme.bigSmoothPrecoverage]
    (X : AlgebraicGeometry.GroupoidsOver S) [AlgebraicGeometry.AlgebraicStack X], Prop)
