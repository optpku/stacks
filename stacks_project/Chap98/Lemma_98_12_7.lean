module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.Approximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.12.7: a versal effective formal object admits a finite-type
approximation versal at a finite type point, with the prescribed residue field
and all positive infinitesimal restrictions. -/
@[stacks 07XH] #check (AlgebraicGeometry.GroupoidsOver.nonempty_approximateVersal :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    (ξ : FormalObject X) (s : S)
    (hs : ξ.base.toS (closedPoint ξ.base.carrier) = s)
    [IsGRing (S.presheaf.stalk s)] [FormalObject.IsEffective ξ]
    (h_versal : FormalObject.IsVersalOnObjects ξ),
    Nonempty (ApproximateVersal ξ))

end AlgebraicGeometry.GroupoidsOver
