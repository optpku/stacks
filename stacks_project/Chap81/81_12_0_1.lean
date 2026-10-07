module

public import stacks_project.Chap81.«81_12_0_1_Glueing»
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/- 81.12.0.1: the canonical functor Spaces/X ⟶ Spaces(U ← U' → X') sending
Y to (U ×_X Y, U' ×_X Y, X' ×_X Y) by base change along the Spec square of
(R → R', f). -/
@[stacks 0F9N] #check AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor
