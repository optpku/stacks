module

public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing
import StacksCheckRecall

open AlgebraicGeometry.AlgebraicSpace

/- Situation 81.10.6: standing formal-glueing setup over a base scheme `S`. A
quasi-compact and quasi-separated morphism `f : Y ⟶ X` of algebraic spaces over `S`
and a finite-presentation closed immersion `i : Z ⟶ X` are given, with
`inverseImageTo f i` an isomorphism and `f` flat at every point of
`pointsImage (inverseImageι f i)`. The derived opens are
`closedImmersionComplement i` and `closedImmersionComplement (inverseImageι f i)`,
and `restrictToComplement f i` fills the commutative square. -/
@[stacks 0AEV] #check AlgebraicGeometry.AlgebraicSpace.IsFormalGlueing

#check AlgebraicGeometry.AlgebraicSpace.restrictToComplement
