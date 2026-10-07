module

public import stacks_project.Chap78.Lemma_78_12_2_ActionIso
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open GroupoidAlgebraicSpace

/- Lemma 78.12.2: Let `B → S` as in Section 78.3. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. If `(F, α)` is a quasi-coherent module on
`(U, R, s, t, c)` then `α` is an isomorphism. -/
@[stacks 077W] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.System.action_isIso :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (A : System G),
    IsIso A.action)

/- Companion: the bundled isomorphism with inverse obtained by reindexing along inversion. -/
#check System.actionIso

/- Companion: the inverse morphism obtained by reindexing the equivariance map along inversion. -/
#check System.actionInverse
