/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled stacks over a site

This file owns the object layer of the full sub-2-category of fibered categories cut out by
the stack condition. Morphisms, `2`-morphisms, and projection constructors are provided by
focused sibling modules.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The object property selecting stacks over `(C, J)` inside `FiberedCategoryOver C`. -/
@[stacks 02ZG "stack object property over a site"]
abbrev IsStack.OnSite.objectProperty (J : GrothendieckTopology C) :
    ObjectProperty (FiberedCategoryOver.{u, v, w, vS} C) :=
  fun X ↦ IsStack.OnSite J X.p

set_option linter.checkUnivs false in
/-- The 2-category of stacks over `(C, J)`, as the full sub-2-category of
`FiberedCategoryOver C` cut out by `IsStack.OnSite.objectProperty J`. -/
@[stacks 02ZG]
abbrev StackOver (J : GrothendieckTopology C) :=
  (IsStack.OnSite.objectProperty.{u, v, w, vS} J).FullSubbicategory

namespace StackOver

variable {J : GrothendieckTopology C}

/-- The underlying fibered category over `C`. -/
@[stacks 02ZG "ambient fibered category of a bundled stack"]
abbrev toFiberedCategoryOver (X : StackOver.{u, v, w, vS} J) :
    FiberedCategoryOver.{u, v, w, vS} C := X.1

/-- The projection functor of a stack. -/
@[stacks 02ZG "projection of a bundled stack"]
abbrev p (X : StackOver.{u, v, w, vS} J) := X.toFiberedCategoryOver.p

/-- The total category of a stack. -/
@[stacks 02ZG "total category of a bundled stack"]
abbrev total (X : StackOver.{u, v, w, vS} J) := X.toFiberedCategoryOver.total

/-- The underlying based category. -/
@[stacks 02ZG "based category of a bundled stack"]
abbrev toBasedCategory (X : StackOver.{u, v, w, vS} J) : BasedCategory.{vS, w} C :=
  X.toFiberedCategoryOver.toBasedCategory

/-- The stack condition on the projection functor. -/
@[stacks 02ZG "stack condition instance for a bundled stack"]
instance isStackOnSite (X : StackOver.{u, v, w, vS} J) : IsStack.OnSite J X.p := X.2

/-- Coercion to the ambient fibered category. -/
@[stacks 02ZG "coercion from a bundled stack to its ambient category"]
instance : CoeOut (StackOver.{u, v, w, vS} J) (FiberedCategoryOver.{u, v, w, vS} C) where
  coe X := X.toFiberedCategoryOver

/-- Construct a stack from a fibered category and a proof of the stack condition. -/
@[stacks 02ZG "construct a bundled stack"]
def mk (X : FiberedCategoryOver.{u, v, w, vS} C) (h : IsStack.OnSite J X.p) :
    StackOver.{u, v, w, vS} J :=
  ObjectProperty.FullSubbicategory.mk _ X h

end StackOver

end CategoryTheory
