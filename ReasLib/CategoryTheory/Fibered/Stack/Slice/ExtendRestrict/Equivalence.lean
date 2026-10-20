/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Inverse
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.ExtendRestrict.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence induced by extension and restriction

The topology-independent strict inverse between extension and restriction restricts to the
stack object properties.  This file exports the resulting round trips and biequivalence
instances.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace Extend.restrict

/-- Constructions A and B are mutually inverse on objects, `1`-morphisms, and `2`-morphisms.
This is the stack-property specialization of
`ObjectProperty.FullSubbicategory.map.isStrictInverse`. -/
@[stacks 04WV "stack-slice extension-restriction inverse"]
theorem isStrictInverse
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor.IsStrictInverse
      (Extend.functor hU) (Restrict.functor hU.isSeparated) := sorry

/-- Restricting an extended localized stack recovers the original object. -/
@[simp, stacks 04WV "stack-slice restriction-extension object round trip"]
theorem obj
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : Localized J U) :
    (Restrict.functor hU.isSeparated).obj ((Extend.functor hU).obj X) = X := sorry

/-- Restricting an extended morphism recovers the original morphism, with endpoint transports
recorded by heterogeneous equality. -/
@[simp, stacks 04WV "stack-slice restriction-extension morphism round trip"]
theorem map
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} (F : X ⟶ Y) :
    (Restrict.functor hU.isSeparated).map ((Extend.functor hU).map F) ≍ F := sorry

/-- Restricting an extended `2`-morphism recovers the original `2`-morphism, with endpoint
transports recorded by heterogeneous equality. -/
@[simp, stacks 04WV "stack-slice restriction-extension two-cell round trip"]
theorem map₂
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : Localized J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (Restrict.functor hU.isSeparated).map₂ ((Extend.functor hU).map₂ eta) ≍ eta := sorry

end Extend.restrict

namespace Restrict.extend

/-- Extending a restricted stack over the canonical slice recovers the original object. -/
@[simp, stacks 04WV "stack-slice extension-restriction object round trip"]
theorem obj
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    (Extend.functor hU).obj ((Restrict.functor hU.isSeparated).obj X) = X := sorry

/-- Extending a restricted morphism recovers the original morphism, with endpoint transports
recorded by heterogeneous equality. -/
@[simp, stacks 04WV "stack-slice extension-restriction morphism round trip"]
theorem map
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : OverSlice J U} (F : X ⟶ Y) :
    (Extend.functor hU).map ((Restrict.functor hU.isSeparated).map F) ≍ F := sorry

/-- Extending a restricted `2`-morphism recovers the original `2`-morphism, with endpoint
transports recorded by heterogeneous equality. -/
@[simp, stacks 04WV "stack-slice extension-restriction two-cell round trip"]
theorem map₂
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : OverSlice J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    (Extend.functor hU).map₂ ((Restrict.functor hU.isSeparated).map₂ eta) ≍ eta := sorry

end Restrict.extend

namespace Extend

/-- Construction A is canonically a biequivalence. -/
@[stacks 04WV "stack-slice extension biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (functor hU).toPseudofunctor := sorry

end Extend

namespace Restrict

/-- Construction B is canonically a biequivalence. -/
@[stacks 04WV "stack-slice restriction biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (functor hU.isSeparated).toPseudofunctor := sorry

end Restrict

end StackOver.Localization

end CategoryTheory
