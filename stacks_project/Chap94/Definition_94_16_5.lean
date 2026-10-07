module

public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Definition_94_16_5_Presentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.16.5: a presentation of an algebraic stack X over S is given by a
smooth groupoid (U, R, s, t, c) in algebraic spaces over S, and an equivalence
f : [U / R] ⟶ X. -/
@[stacks 04TI] #check AlgebraicGeometry.AlgebraicStack.Presentation
