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

/- Definition 35.4.19: the descent pushforward sends a descent datum to the
equalizer of its restricted coaction and the scalar-extension unit. -/
@[stacks 08X5] #check (ModuleCat.descentPushforward :
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S),
    (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra ⥤
      ModuleCat.{max w v} R)

/- The object part of descent pushforward is the equalizer of the restricted
coaction and the extension-restriction unit. -/
#check (ModuleCat.descentPushforward_obj :
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra),
      (ModuleCat.descentPushforward f).obj D =
        equalizer ((ModuleCat.restrictScalars f).map D.a)
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app
            ((ModuleCat.restrictScalars f).obj D.A)))
