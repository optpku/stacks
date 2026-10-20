module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Basic
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Strict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection constructors for bundled stacks

This file owns the forgetful strict pseudofunctor and the constructors that bundle a projection
functor carrying a stack condition.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The forgetful strict pseudofunctor from `StackOver J` to `FiberedCategoryOver C`. -/
@[stacks 02ZG "forgetful pseudofunctor for bundled stacks"]
abbrev StackOver.forget (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.{u, v, w, vS} J)
      (FiberedCategoryOver.{u, v, w, vS} C) :=
  ObjectProperty.FullSubbicategory.ι (IsStack.OnSite.objectProperty.{u, v, w, vS} J)

/-- The canonical fibered category built from a stack projection is a stack over the same site.
This isolates the transport along `FiberedCategoryOver.ofFunctor.p` from the bundled
`StackOver` constructor. -/
@[stacks 02ZG "transport the stack condition through a projection constructor"]
theorem FiberedCategoryOver.ofFunctor.isStackOnSite (J : GrothendieckTopology C)
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) (h : IsStack.OnSite J p) :
    IsStack.OnSite J (FiberedCategoryOver.ofFunctor p).p := sorry

/-- The canonical fibered category built from a stack projection inherits the stack condition. -/
@[stacks 02ZG "canonical stack instance for a projection constructor"]
instance FiberedCategoryOver.ofFunctor.stackOnSite
    (J : GrothendieckTopology C)
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsStack.OnSite J p] :
    IsStack.OnSite J (FiberedCategoryOver.ofFunctor p).p := sorry

/-- Construct a stack from a projection functor carrying its canonical stack instance. -/
@[stacks 02ZG "construct a bundled stack from a projection"]
noncomputable abbrev StackOver.ofProjection (J : GrothendieckTopology C)
    -- Pin `S`'s universes to `w`/`vS`: with `Type*` the metavariables in
    -- `FiberedCategoryOver.ofFunctor` cannot be solved.
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsStack.OnSite J p] :
    StackOver.{u, v, w, vS} J :=
  StackOver.mk (FiberedCategoryOver.ofFunctor p) inferInstance

/-- Construct a stack from a projection and a one-off stack witness, without installing a local
instance. -/
@[stacks 02ZG "construct a bundled stack from an explicit stack witness"]
noncomputable abbrev StackOver.ofProjectionWith (J : GrothendieckTopology C)
    {S : Type w} [Category.{vS} S] (p : S ⥤ C) (h : IsStack.OnSite J p) :
    StackOver.{u, v, w, vS} J :=
  StackOver.mk (FiberedCategoryOver.ofFunctor p)
    (FiberedCategoryOver.ofFunctor.isStackOnSite J p h)

end CategoryTheory
