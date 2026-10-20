module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Sheaf
import StacksCheckRecall

/-!
# Étale sheafness of the Artin contraction functor

In Situation 98.27.1 the contraction functor on locally Noetherian schemes
over `S` is a sheaf for the étale topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.StandardTopology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

/- Lemma 98.27.10: In Situation 98.27.1 the functor `σ.functor` satisfies the
sheaf property for all étale coverings of locally Noetherian schemes over `S`. -/
@[stacks 0GHG] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.isSheaf_etale :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S),
      Presheaf.IsSheaf (locallyNoetherianTopology StandardTopology.etale S) σ.functor)

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
