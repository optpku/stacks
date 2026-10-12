/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal.Adjunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed

universe uX uY vX vY

variable {D_X : Type uX} {D_Y : Type uY}
variable [Category.{vX} D_X] [Category.{vY} D_Y]
variable [MonoidalCategory D_X] [MonoidalCategory D_Y]
variable [MonoidalClosed D_X] [MonoidalClosed D_Y]

variable (fPush : Functor D_X D_Y) [fPush.LaxMonoidal]
variable (a : Functor D_Y D_X) (adj : fPush ⊣ a)
variable (L : D_X) (K : D_Y)

/- 48.3.5.1: for a derived pushforward `fPush` with right adjoint `a`, the sheafy
trace morphism is the lax-monoidal internal-Hom comparison followed by the adjunction counit. -/
@[stacks 0B6H] #check
  (CategoryTheory.Functor.LaxMonoidal.InternalHom.adjunctionComparison fPush adj L K :
    fPush.obj ((ihom L).obj (a.obj K)) ⟶ (ihom (fPush.obj L)).obj K)
