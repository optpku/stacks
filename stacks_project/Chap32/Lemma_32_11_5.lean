module

import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.ClosedImmersion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.11.5: A closed immersion inducing a homeomorphism of underlying topological
spaces preserves and reflects quasi-affineness. -/
@[stacks 0B7L] #check
  (AlgebraicGeometry.Scheme.isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
      IsHomeomorph i → (X.IsQuasiAffine ↔ Z.IsQuasiAffine))
