/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
import ReasLib.CategoryTheory.Functor.Derived.Pointwise
import StacksCheckRecall

@[expose] public section

/-!
# 13.14.9.1 (05S9)

The total derived functor is the canonical Mathlib owner specialized to the localization functor
`S.Q`.  The source-facing hypothesis is `Functor.RightDerived.EverywhereDefined` or
`Functor.LeftDerived.EverywhereDefined`; its weak pointwise consequence is inserted automatically
by the neutral bridge instance.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (S : MorphismProperty 𝒟) (F : 𝒟 ⥤ 𝒟')

section Right

variable [Functor.RightDerived.EverywhereDefined F S]

/- The strong source-definedness owner and its weak pointwise companion. -/
@[stacks 05S9 "right everywhere-defined hypothesis"]
#check @Functor.RightDerived.EverywhereDefined
#check @Functor.RightDerived.EverywhereDefined.hasPointwise

/- The total right-derived existence bridge and canonical localization model. -/
@[stacks 05S9 "right total derived functor"]
#check @Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
#check @Functor.totalRightDerived
#check (F.totalRightDerived S.Q S : S.Localization ⥤ 𝒟')

end Right

section Left

variable [Functor.LeftDerived.EverywhereDefined F S]

/- The strong source-definedness owner and its weak pointwise companion. -/
@[stacks 05S9 "left everywhere-defined hypothesis"]
#check @Functor.LeftDerived.EverywhereDefined
#check @Functor.LeftDerived.EverywhereDefined.hasPointwise

/- The total left-derived existence bridge and canonical localization model. -/
@[stacks 05S9 "left total derived functor"]
#check @Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
#check @Functor.totalLeftDerived
#check (F.totalLeftDerived S.Q S : S.Localization ⥤ 𝒟')

end Left

end CategoryTheory
