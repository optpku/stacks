/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
  (jPull : D_Y ⥤ D_Y') (jPush : D_Y' ⥤ D_Y)
  (jPrimePull : D_X ⥤ D_X') (jPrimePush : D_X' ⥤ D_X)
  (a : D_Y ⥤ D_X) (aPrime : D_Y' ⥤ D_X')
  (jAdj : jPull ⊣ jPush) (jPrimeAdj : jPrimePull ⊣ jPrimePush)
  (ξ : aPrime ⋙ jPrimePush ≅ jPush ⋙ a)

/- 48.4.1.1: The transformation `a ⋙ jPrimePull ⟶ jPull ⋙ aPrime` is the mate of
`ξ.inv`, obtained by composing the adjunction unit, `ξ.inv`, and the adjunction counit. -/
@[stacks 0A9L] #check
  (CategoryTheory.DerivedBaseChange.mapOfRight jAdj jPrimeAdj ξ.inv :
    a ⋙ jPrimePull ⟶ jPull ⋙ aPrime)

#check CategoryTheory.DerivedBaseChange.mapOfRight_mate
