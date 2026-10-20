module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Conormal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {D X : AlgebraicSpace S}
variable (i : D ⟶ X) [IsEffectiveCartierDivisor i]

/- Lemma 71.7.2. The conormal sheaf of an effective Cartier divisor is the
restriction of its ideal sheaf, equivalently its negative divisor sheaf. -/
@[stacks 0B4F] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.pullbackIdealComparison_isIso i :
    IsIso
      (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.pullbackIdealComparison i :
        (Modules.pullback i).obj (Hom.negSheaf i) ⟶ Hom.conormalSheaf i))
