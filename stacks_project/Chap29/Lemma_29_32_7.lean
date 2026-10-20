module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Diagonal
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Lemma 29.32.7: for a morphism of schemes `f : X ⟶ S`, the canonical comparison from
`Ω[f.toShHom]` to the conormal sheaf of `pullback.diagonal f` is an isomorphism. -/
@[stacks 08S2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.Diagonal.comparison_isIso f :
    IsIso (AlgebraicGeometry.Scheme.RelativeDifferentials.Diagonal.comparison f))

end AlgebraicGeometry
