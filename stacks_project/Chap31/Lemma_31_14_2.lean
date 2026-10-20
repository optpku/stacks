module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Normal
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

variable {S : AlgebraicGeometry.Scheme.{u}} (D : S.IdealSheafData)
variable [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]

/- Lemma 31.14.2 (1): the conormal sheaf of an effective Cartier divisor is the pullback of
its ideal sheaf `D.negSheaf`. -/
@[stacks 0B3P] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.pullbackIdealComparison_isIso D.subschemeι :
    IsIso
      (AlgebraicGeometry.Scheme.Hom.Conormal.pullbackIdealComparison D.subschemeι :
        (AlgebraicGeometry.Scheme.Modules.pullback D.subschemeι).obj D.negSheaf ⟶
          AlgebraicGeometry.Scheme.Hom.conormalSheaf D.subschemeι))

/- Lemma 31.14.2 (2): the normal sheaf of an effective Cartier divisor is the pullback of
its associated sheaf `D.associatedSheaf`. -/
@[stacks 0B3P] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.normalSheafIso D :
    (AlgebraicGeometry.Scheme.Modules.pullback D.subschemeι).obj D.associatedSheaf ≅
      AlgebraicGeometry.Scheme.Hom.normalSheaf D.subschemeι)
