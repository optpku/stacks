module

import stacks_project.Chap83.Definition_83_5_18_OrbitSpace
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {U X : Over B} (P : PreRelation U) {φ : U ⟶ X}

/- Lemma 83.5.10: in the situation of Definition 83.5.8, an invariant morphism
is set-theoretically invariant. -/
@[stacks 048X]
#check (PreRelation.isSetTheoreticallyInvariant_of_isInvariant P :
  P.IsInvariant φ → P.IsSetTheoreticallyInvariant φ)
