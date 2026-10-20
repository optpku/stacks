module

public import ReasLib.CategoryTheory.Adjunction.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uZ uZ' uX uX' vZ vZ' vX vX'

variable {D_Z : Type uZ} {D_Z' : Type uZ'} {D_X : Type uX} {D_X' : Type uX'}
variable [Category.{vZ} D_Z] [Category.{vZ'} D_Z']
variable [Category.{vX} D_X] [Category.{vX'} D_X']

variable
  (iPush : D_Z ⥤ D_X) (iPrimePush : D_Z' ⥤ D_X')
  (gPull : D_Z ⥤ D_Z') (fPull : D_X ⥤ D_X')
  (rHomOZ : D_X ⥤ D_Z) (rHomOZPrime : D_X' ⥤ D_Z')
  (iAdj : iPush ⊣ rHomOZ) (iPrimeAdj : iPrimePush ⊣ rHomOZPrime)
  (baseChangeIso : gPull ⋙ iPrimePush ≅ iPush ⋙ fPull)
  (K : D_X)

/- 48.10.0.1: The canonical morphism
`gPull.obj (rHomOZ.obj K) ⟶ rHomOZPrime.obj (fPull.obj K)` is the component at `K`
of the right mate of the tor-independent base-change comparison `baseChangeIso`. -/
@[stacks 0E2K] #check
  (CategoryTheory.DerivedBaseChange.app iAdj iPrimeAdj baseChangeIso K :
    gPull.obj (rHomOZ.obj K) ⟶ rHomOZPrime.obj (fPull.obj K))
