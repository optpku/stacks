module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.GermProperty
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 100.7.5: let `P` be a property of germs of schemes which is
smooth local. Let `X` be an algebraic stack. Let `x ∈ |X|`. We say `X` has
property `P` at `x` if any of the equivalent conditions of Lemma 100.7.4
holds. -/
@[stacks 04YJ] #check (AlgebraicGeometry.AlgebraicStack.hasSmoothLocalAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (P : AlgebraicGeometry.GermProperty.{u})
    (hP : P.IsSmoothLocal) (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X] (x : AlgebraicGeometry.AlgebraicStack.Points X),
    Prop)
