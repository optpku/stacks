module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 83.5.10: in the situation of Definition 83.5.8, an invariant morphism
is set-theoretically invariant. -/
@[stacks 048X]
#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.isSetTheoreticallyInvariant_of_isInvariant :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B} (P : PreRelation U) {φ : U ⟶ X},
    P.IsInvariantHom φ → P.IsSetTheoreticallyInvariant φ)
