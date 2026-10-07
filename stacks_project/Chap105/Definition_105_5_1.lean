module

public import stacks_project.Chap105.Definition_105_5_1_Algebraic
public import stacks_project.Chap105.Definition_105_5_1_Moduli
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 105.5.1: we say M_{1,1} is an algebraic stack if and only if we
have descent for objects for the étale topology on Sch, the key fact holds, and
there exists a surjective smooth morphism S ⟶ M_{1,1}. -/
@[stacks 072R] #check AlgebraicGeometry.EllipticCurve.Moduli.IsAlgebraicStack
