module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry

/- Definition 107.2.2
In Situation 107.2.1, X is an algebraic stack locally of finite type over a
locally Noetherian scheme S. Let x0 : Spec(k) ⟶ X be a morphism, where k is a finite
type field over S. A versal ring to X at x0 is a complete Noetherian local
S-algebra A with residue field k such that there exists a versal formal object
(A, ξ_n, f_n) as in Artin's Axioms, Definition 98.12.1 with ξ_1 ≅ x0 (a
2-isomorphism). This is owned by AlgebraicGeometry.AlgebraicStack.IsVersalRing. -/
@[stacks 0DQV] #check (AlgebraicGeometry.AlgebraicStack.IsVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S} [AlgebraicStack X]
    (x0 : AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom], CompleteLocalSAlgebra S → Prop)

#check AlgebraicGeometry.AlgebraicStack.IsVersalRing.spec
#check AlgebraicGeometry.AlgebraicStack.IsVersalRing.iff
