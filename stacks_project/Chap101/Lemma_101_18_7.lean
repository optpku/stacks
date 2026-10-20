module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints.ResidualGerbe
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.18.7: Let `X` be an algebraic stack and let `x : Points X`.
The following are equivalent: `x` is a finite type point; there exists an
algebraic stack `Z` whose underlying topological space is a singleton and a
locally-of-finite-type morphism `f : Z ⟶ X` with image `{x}` on points; and
the residual gerbe of `X` at `x` exists and its canonical inclusion into `X`
is locally of finite type. -/
@[stacks 06G3] #check (AlgebraicGeometry.AlgebraicStack.isFiniteTypePoint_tfae :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X),
    List.TFAE
      [IsFiniteTypePoint x, existsSingletonLocallyOfFiniteType x,
        existsResidualGerbeLocallyOfFiniteType x])

end AlgebraicGeometry.AlgebraicStack
