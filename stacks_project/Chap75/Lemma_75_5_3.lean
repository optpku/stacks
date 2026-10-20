module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Coproduct
import StacksCheckRecall

universe u

/- Lemma 75.5.3: for a scheme `S` and an algebraic space `X` over `S`, the
category `D_QCoh(𝒪_X)` has direct sums. -/
@[stacks 08F3] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.hasCoproducts :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Limits.HasCoproducts.{u} (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X))
