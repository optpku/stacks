/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Inertia.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vertical automorphisms in relative inertia

These facts are independent of the based relative-inertia owner. They record
that the chosen automorphism and its inverse lie over the identity whenever the
defining functor factors through a common base.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {S : Type uX} [Category.{vX} S]
variable {S' : Type uY} [Category.{vY} S']

/-- A relative-inertia automorphism is vertical for every projection through which its defining
functor factors. The factorization equation is the only non-inferable input. -/
@[stacks 034H "vertical relative-inertia automorphism"]
theorem RelativeInertia.aut.hom.isHomLift
    {F : S ⥤ S'} {p : S ⥤ C} {p' : S' ⥤ C}
    (comm : F ⋙ p' = p) (X : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj X.obj)) X.aut.hom := sorry

/-- The inverse of a relative-inertia automorphism is vertical for every projection through
which its defining functor factors. -/
@[stacks 034H "inverse vertical relative-inertia automorphism"]
theorem RelativeInertia.aut.inv.isHomLift
    {F : S ⥤ S'} {p : S ⥤ C} {p' : S' ⥤ C}
    (comm : F ⋙ p' = p) (X : RelativeInertia F) :
    p.IsHomLift (𝟙 (p.obj X.obj)) X.aut.inv := sorry

namespace BasedCategory

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- The chosen relative-inertia automorphism of a based functor is canonically vertical over the
source projection. -/
instance RelativeInertia.aut.hom.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    X.p.IsHomLift (𝟙 (X.p.obj A.obj)) A.aut.hom := sorry

/-- The inverse chosen relative-inertia automorphism of a based functor is canonically vertical
over the source projection. -/
instance RelativeInertia.aut.inv.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    X.p.IsHomLift (𝟙 (X.p.obj A.obj)) A.aut.inv := sorry

end BasedCategory
end CategoryTheory
