module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.OpennessOfVersality

/-!
# Openness of versality for the contraction functor

The functor of compatible open and formal contraction data satisfies openness
of versality over a locally Noetherian base scheme.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

/-- The contraction functor over a locally Noetherian base satisfies openness
of versality. -/
theorem opennessOfVersality {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : ContractionSituation S) :
    AlgebraicGeometry.Scheme.Over.OpennessOfVersality σ.functor :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
