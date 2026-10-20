module

import ReasLib.CategoryTheory.Pretriangulated.K0.Euler
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.28.4

The alternating Euler construction for homological functors is owned by
`ReasLib.CategoryTheory.Pretriangulated.K0.Euler`.
-/

open CategoryTheory
open CategoryTheory.Functor

universe vD vA uD uA

variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]

@[stacks 0FCR] #check @Functor.eulerClass

@[stacks 0FCR] #check @Functor.eulerClass_hasFiniteSupport

@[stacks 0FCR] #check @Functor.eulerClass_eq_sum_of_vanishingIn

@[stacks 0FCR] #check @Functor.eulerClass_eq_of_iso

@[stacks 0FCR] #check @Functor.eulerClass_eq_of_natIso

@[stacks 0FCR] #check @Functor.eulerClass_distinguished

@[stacks 0FCR] #check @Functor.eulerK0Map

@[stacks 0FCR] #check @Functor.eulerK0Map_apply_of
