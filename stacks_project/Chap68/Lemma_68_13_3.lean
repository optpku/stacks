module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ReducedSingleton
import StacksCheckRecall

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.13.3: An algebraic space over a scheme is reduced, locally
Noetherian, and has exactly one point if and only if it admits a locally
finitely presented, surjective, flat morphism from the spectrum of a field. -/
@[stacks 06QX] #check
  (AlgebraicGeometry.AlgebraicSpace.isReduced_isLocallyNoetherian_subsingleton_points_tfae :
    ∀ {S : Scheme.{u}} (Z : AlgebraicSpace S),
      List.TFAE
        [ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
            Subsingleton (Points Z)
        , existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ])

end AlgebraicGeometry.AlgebraicSpace
