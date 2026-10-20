/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
# Universe-normalized functors

This leaf extends `Cat.asSmallFunctor` to a single functor whose source and target categories may
initially live in different universes. Both categories are moved into one common `AsSmall` owner.
-/

@[expose] public section

universe w vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A functor between categories in arbitrary universes, transported to common small models. -/
def asSmall (F : C ⥤ D) :
    AsSmall.{max w vC uC vD uD} C ⥤ AsSmall.{max w vC uC vD uD} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- A natural transformation transported between the common small models of its source and
target categories. -/
def asSmallMap {F G : C ⥤ D} (η : F ⟶ G) :
    asSmall.{w} F ⟶ asSmall.{w} G :=
  whiskerLeft AsSmall.down (whiskerRight η AsSmall.up)

/-- A natural isomorphism transported between the common small models of its source and target
categories. -/
def asSmallMapIso {F G : C ⥤ D} (e : F ≅ G) :
    asSmall.{w} F ≅ asSmall.{w} G :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight e AsSmall.up)

end CategoryTheory.Functor
