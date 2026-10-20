module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/- Lemma 29.7.5: for an open immersion `j : U ⟶ X`, the open subscheme `j.opensRange`
is scheme theoretically dense in `X` if and only if the canonical structure sheaf map
`𝒪_X ⟶ j_*𝒪_U` is injective. -/
@[stacks 01RE] #check
  (AlgebraicGeometry.schemeTheoreticallyDense_opensRange_iff_mono j :
    schemeTheoreticallyDense j.opensRange ↔ Mono j.c)

end AlgebraicGeometry
