module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Representable
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 106.3.2 (1): a morphism `i : X ⟶ X'` of algebraic stacks is a
thickening of algebraic stacks (abuse of language) if and only if it is
representable by algebraic spaces and a thickening in the sense of Properties
of Stacks, Section 100.3. -/
@[stacks 0CJ7] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.iff_has :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X'),
    IsThickening i ↔ relativelyRepresentableByAlgebraicSpaces i ∧
      Groupoids.Hom.has (@AlgebraicSpace.IsThickening S) i)

/- Lemma 106.3.2 (2): in this case `i` is a closed immersion. -/
@[stacks 0CJ7] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.toClosedImmersion :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] {i : X ⟶ X'} [IsThickening i],
    Groupoids.Hom.ClosedImmersion i)

/- Lemma 106.3.2 (3): in this case `i` is a universal homeomorphism. -/
@[stacks 0CJ7] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.instUniversalHomeomorphism :
  ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i],
    UniversalHomeomorphism i)
