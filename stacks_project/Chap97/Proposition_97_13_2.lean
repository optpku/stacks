module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap97.Proposition_97_13_2_Group
public import stacks_project.Chap97.Proposition_97_13_2_Action
public import stacks_project.Chap97.Proposition_97_13_2_Comparison

/-!
# Proposition 97.13.2

The finite Hilbert stack `H_d` of a point is equivalent to the quotient stack
`[X/G]` of the unit-fixing `GL_d`-action on the universal free-algebra scheme,
and in particular `H_d` is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.GLFixOne
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/-- Proposition 97.13.2 (1): the Spec comparison `[X/G] ⟶ H_d` is an equivalence of
stacks in groupoids over `(Sch/Spec(Z))_fppf`. -/
@[stacks 05YQ, instance]
instance comparison_isEquivalence (d : ℕ) [NeZero d] :
    (FiberedCategoryOver.Groupoids.toBasedFunctor (comparison d)).IsEquivalence :=
  sorry

/-- Proposition 97.13.2 (2): the finite Hilbert stack `H_d` of a point is an algebraic
stack over `Spec(Z)`. -/
@[stacks 05YQ, instance]
instance instAlgebraicStack (d : ℕ) [NeZero d] :
    AlgebraicStack (ofScheme specZ d).toGroupoids :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
