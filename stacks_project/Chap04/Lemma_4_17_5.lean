/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Final
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable (F : I ⥤ J)
variable (hfiber : ∀ j : J, IsConnected (F.Fiber j))
variable (hlift : ∀ ⦃X Y : J⦄ (f : X ⟶ Y),
  ∃ (a b : I) (g : a ⟶ b), F.IsHomLift f g)

/- Lemma 4.17.5: connected strict fibers together with lifts of all base morphisms imply
finality. -/
@[stacks 05US "finality from connected fibres and lifts of base morphisms"]
#check (Functor.Final.of_connectedFibers_and_homLifts F hfiber hlift : F.Final)

end CategoryTheory.Functor
