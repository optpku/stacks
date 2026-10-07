module

public import stacks_project.Chap106.Lemma_106_3_2_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open scoped Bicategory

universe u

/- Lemma 106.3.2 (1): a morphism `i : X ⟶ X'` of algebraic stacks is a
thickening of algebraic stacks (abuse of language) if and only if it is
representable by algebraic spaces and a thickening in the sense of Properties
of Stacks, Section 100.3. -/
@[stacks 0CJ7] #check iff_has

/- Lemma 106.3.2 (2): in this case `i` is a closed immersion. -/
@[stacks 0CJ7] #check IsThickening.toClosedImmersion

/- Lemma 106.3.2 (3): in this case `i` is a universal homeomorphism. -/
@[stacks 0CJ7] #check instUniversalHomeomorphism
