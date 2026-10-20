module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace
open scoped Bicategory

/- Lemma 83.3.6: The canonical square formed by an invariant base change of a
groupoid and its quotient stack is a 2-fibre product over the big fppf site. -/
@[stacks 0DTG] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.baseChangeQuotientCone_isBilimit :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {X X' : Over B} (φ : G.U ⟶ X) (hφ : G.toPreRelation.IsInvariantHom φ)
      (g : X' ⟶ X), (baseChangeQuotientCone G φ hφ g).IsBilimit)
