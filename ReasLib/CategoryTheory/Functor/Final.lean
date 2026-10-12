/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Finality from connected strict fibers

Connected strict fibers together with lifts of base morphisms imply finality.  The conclusion is
the canonical `Functor.Final` owner and therefore feeds directly into the standard colimit API.
-/

@[expose] public section

universe vI uI vJ uJ

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]

/-- Lemma 4.17.5 (Stacks 05US): a functor with connected strict fibers and a lift of every base
morphism is final. -/
@[stacks 05US]
theorem Final.of_connectedFibers_and_homLifts (F : I ⥤ J)
    (hfiber : ∀ j : J, IsConnected (F.Fiber j))
    (hlift : ∀ ⦃X Y : J⦄ (f : X ⟶ Y),
      ∃ (a b : I) (g : a ⟶ b), F.IsHomLift f g) :
    F.Final := sorry

/-- A functor with connected strict fibers and a lift of every base morphism is initial. -/
theorem Initial.of_connectedFibers_and_homLifts (F : I ⥤ J)
    (hfiber : ∀ j : J, IsConnected (F.Fiber j))
    (hlift : ∀ ⦃X Y : J⦄ (f : X ⟶ Y),
      ∃ (a b : I) (g : a ⟶ b), F.IsHomLift f g) :
    F.Initial := sorry

end CategoryTheory.Functor
