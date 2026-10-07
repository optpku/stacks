module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.SchemeTheoreticallyDominant
import StacksCheckRecall

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
variable (U : X.Opens)

/- Lemma 29.7.10: if two `S`-morphisms `f, g : X ⟶ Y` agree on an open subscheme
`U ⊆ X` whose scheme-theoretic closure is `X`, and `Y ⟶ S` is separated, then `f = g`. -/
@[stacks 01RH] #check
  (AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated' (S := S) U.ι :
    ∀ {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] [IsSeparated (Y ↘ S)]
      [IsSchemeTheoreticallyDominant U.ι], U.ι ≫ f = U.ι ≫ g → f = g)

end AlgebraicGeometry
