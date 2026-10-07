module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Fppf
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.16.1: local Noetherianity of schemes is local for the fppf precoverage. -/
@[stacks 034C] #check
  (AlgebraicGeometry.IsLocallyNoetherian.isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.IsLocallyNoetherian :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
