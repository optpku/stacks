module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints.Monomorphism
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.25.7 -/
@[stacks 06EL] #check
  (AlgebraicGeometry.AlgebraicSpace.isFiniteTypePoint_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
      List.TFAE [IsFiniteTypePoint x, existsSingletonLocallyOfFiniteType x,
        existsEtaleFieldMono x])

end AlgebraicGeometry.AlgebraicSpace
