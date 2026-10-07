module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uY uY' uX uX' vY vY' vX vX'

variable {D_Y : Type uY} {D_Y' : Type uY'} {D_X : Type uX} {D_X' : Type uX'}
variable [Category.{vY} D_Y] [Category.{vY'} D_Y']
variable [Category.{vX} D_X] [Category.{vX'} D_X']

variable
  (gPull : D_Y ⥤ D_Y') (gPush : D_Y' ⥤ D_Y)
  (gPrimePull : D_X ⥤ D_X') (gPrimePush : D_X' ⥤ D_X)
  (a : D_Y ⥤ D_X) (aPrime : D_Y' ⥤ D_X')
  (gAdj : gPull ⊣ gPush) (gPrimeAdj : gPrimePull ⊣ gPrimePush)
  (dualBaseChangeIso : aPrime ⋙ gPrimePush ≅ gPush ⋙ a)

/- 48.5.0.1: The base-change transformation
`a ⋙ gPrimePull ⟶ gPull ⋙ aPrime` is the mate of the inverse dual
base-change isomorphism. It is the composite formed from the unit of `gAdj`,
`dualBaseChangeIso.inv`, and the counit of `gPrimeAdj`. -/
@[stacks 0AA6] #check
  (CategoryTheory.DerivedBaseChange.mapOfRight
    gAdj gPrimeAdj dualBaseChangeIso.inv : a ⋙ gPrimePull ⟶ gPull ⋙ aPrime)
