module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Extend.Functor
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Restrict.Functor
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension and restriction for stacks over a slice

The topology-independent extension and restriction strict pseudofunctors preserve the
appropriate stack conditions.  Restricting them to those object properties gives the two
canonical functors between `Localized J U` and `OverSlice J U`.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace Extend

/-- Extension sends a stack over the slice site to a neutral strict-slice
object whose domain is a stack over `(C, J)`. -/
@[stacks 04WV "stack-slice extension object property"]
theorem obj_mem
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : FiberedCategoryOver.{max u v, v, max u v, v} (Over U))
    (hX : IsStack.OnSite (J.over U) X.p) :
    overSliceProperty J U
      ((FiberedCategoryOver.Slice.Extend.functor (Over.forget U)).obj X) := sorry

/-- Construction A, obtained by restricting the source and target object
properties of the topology-independent extension strict pseudofunctor. -/
@[stacks 04WV "stack-slice extension functor"]
noncomputable def functor
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor (Localized J U) (OverSlice J U) :=
  FullSubbicategory.map
    (FiberedCategoryOver.Slice.Extend.functor (Over.forget U)) (obj_mem hU)

namespace functor

/-- Forgetting the target stack witness from Construction A on objects gives
the neutral extension object. -/
@[simp, stacks 04WV "stack-slice extension object projection"]
theorem obj.val
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    ((functor hU).obj X).1 =
      FiberedCategoryOver.Slice.Extend.obj
        (Over.forget U) X.toFiberedCategoryOver := sorry

/-- Forgetting the target property from Construction A on a morphism gives the
neutral extension morphism. -/
@[simp, stacks 04WV "stack-slice extension morphism projection"]
theorem map.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} (F : X ⟶ Y) :
    ((functor hU).map F).hom =
      FiberedCategoryOver.Slice.Extend.map
        (Over.forget U) (StackOver.Hom.toMor F) := sorry

/-- Forgetting the target property from Construction A on a `2`-morphism gives
the neutral extension `2`-morphism. -/
@[simp, stacks 04WV "stack-slice extension two-cell projection"]
theorem map₂.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((functor hU).map₂ eta).hom =
      FiberedCategoryOver.Slice.Extend.map₂
        (Over.forget U) (StackOver.Hom.toMor₂ eta) := sorry

end functor

end Extend

namespace Restrict

/-- Restriction sends a neutral strict-slice object with stack domain to a
stack over the slice site. Only separatedness of the represented presheaf is needed in this
direction. -/
@[stacks 04WV "stack-slice restriction object property"]
theorem obj_mem
    {U : C} (hU : Presheaf.IsSeparated J (yoneda.obj U))
    (X : StrictSlice (FiberedCategoryOver.ofFunctor (Over.forget U)))
    (hX : overSliceProperty J U X) :
    IsStack.OnSite (J.over U)
      ((FiberedCategoryOver.Slice.Restrict.functor (Over.forget U)).obj X).p := sorry

/-- Construction B, obtained by restricting the source and target object
properties of the topology-independent restriction strict pseudofunctor. Unlike extension, this
construction only requires separatedness of the represented presheaf. -/
@[stacks 04WV "stack-slice restriction functor"]
noncomputable def functor
    {U : C} (hU : Presheaf.IsSeparated J (yoneda.obj U)) :
    StrictPseudofunctor (OverSlice J U) (Localized J U) :=
  FullSubbicategory.map
    (FiberedCategoryOver.Slice.Restrict.functor (Over.forget U)) (obj_mem hU)

namespace functor

/-- Forgetting the target stack witness from Construction B on objects gives
the neutral restriction object. -/
@[simp, stacks 04WV "stack-slice restriction object projection"]
theorem obj.val
    {U : C} (hU : Presheaf.IsSeparated J (yoneda.obj U))
    (X : OverSlice J U) :
    ((functor hU).obj X).1 =
      FiberedCategoryOver.Slice.Restrict.obj X.toFiberedSlice := sorry

/-- Forgetting the target stack property from Construction B on a morphism
gives the neutral restriction morphism. -/
@[simp, stacks 04WV "stack-slice restriction morphism projection"]
theorem map.hom
    {U : C} (hU : Presheaf.IsSeparated J (yoneda.obj U))
    {X Y : OverSlice J U} (F : X ⟶ Y) :
    ((functor hU).map F).hom =
      FiberedCategoryOver.Slice.Restrict.map F.hom := sorry

/-- Forgetting the target stack property from Construction B on a
`2`-morphism gives the neutral restriction `2`-morphism. -/
@[simp, stacks 04WV "stack-slice restriction two-cell projection"]
theorem map₂.hom
    {U : C} (hU : Presheaf.IsSeparated J (yoneda.obj U))
    {X Y : OverSlice J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((functor hU).map₂ eta).hom =
      FiberedCategoryOver.Slice.Restrict.map₂ eta.hom := sorry

end functor

end Restrict

end StackOver.Localization

end CategoryTheory
