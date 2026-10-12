/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)
variable (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra)

/- 35.4.19.1: The descent pushforward is the equalizer of the restricted
coalgebra coaction and the extension-restriction adjunction unit. -/
@[stacks 08X6] #check
  (ModuleCat.DescentPushforward.fork f D :
    Fork ((ModuleCat.restrictScalars f).map D.a)
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj D.A)))

#check (ModuleCat.DescentPushforward.forkIsLimit f D :
  IsLimit (ModuleCat.DescentPushforward.fork f D))
