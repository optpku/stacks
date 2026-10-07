module

import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.6.4

The reusable shift-vanishing object properties and their triangulated closure
API are owned by `ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing`.
-/

open CategoryTheory
open CategoryTheory.Functor

universe vD vA uD uA

variable {D : Type uD} [Category.{vD} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (H : D ⥤ A) [H.IsHomological]

@[stacks 05RE] #check @Functor.shiftVanishingPlus

@[stacks 05RE] #check @Functor.shiftVanishingMinus

@[stacks 05RE] #check @Functor.shiftVanishingBounded

@[stacks 05RE] #check @Functor.shiftVanishingIn

@[stacks 05RE] #check @Functor.mem_shiftVanishingBounded_iff

@[stacks 05RE] #check (inferInstance : H.shiftVanishingPlus.IsTriangulated)

@[stacks 05RE] #check (inferInstance : H.shiftVanishingMinus.IsTriangulated)

@[stacks 05RE] #check (inferInstance : H.shiftVanishingBounded.IsTriangulated)
