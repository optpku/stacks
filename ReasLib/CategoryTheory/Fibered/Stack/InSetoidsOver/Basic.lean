/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.Setoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction

/-!
# Stacks in setoids over a site

This file defines the bundled object layer for stacks in setoids: the full-subcategory owner,
its canonical forgetful views, and constructors from setoid-fibred categories and projections.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The object property selecting stacks in setoids inside `StackOver.Groupoids J`. -/
@[stacks 0433 "stack-in-setoids object property"]
abbrev IsStack.InSetoids.objectProperty (J : GrothendieckTopology C) :
    ObjectProperty (StackOver.Groupoids J) :=
  fun X ↦ Functor.IsFibered.InSetoids X.p

/-- The 2-category of stacks in setoids over `(C, J)`. -/
@[stacks 0433]
abbrev StackOver.Setoids (J : GrothendieckTopology C) :=
  (IsStack.InSetoids.objectProperty J).FullSubbicategory

namespace FiberedCategoryOver.Groupoids.ofFunctor

/-- Bundling a stack-in-setoids projection as a groupoid-fibered category preserves the full
stack-in-setoids condition. -/
@[stacks 0433 "stack-in-setoids projection closure"]
theorem isSetoidStack
    (J : GrothendieckTopology C) {S : Type*} [Category S] (p : S ⥤ C)
    [IsStack.InSetoids J p] :
    IsStack.InSetoids J (FiberedCategoryOver.Groupoids.ofFunctor p).p := sorry

end FiberedCategoryOver.Groupoids.ofFunctor

namespace StackOver.Setoids

variable {J : GrothendieckTopology C}

/-- The canonical strict forgetful pseudofunctor from stacks in setoids to stacks in groupoids. -/
@[stacks 0433 "stack-in-setoids forgetful pseudofunctor"]
abbrev forget (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.Setoids J) (StackOver.Groupoids J) :=
  ObjectProperty.FullSubbicategory.ι _

/-- The underlying stack in groupoids. -/
@[stacks 0433 "stack-in-setoids underlying groupoid stack"]
abbrev toGroupoids (X : StackOver.Setoids J) : StackOver.Groupoids J :=
  (forget J).obj X

/-- The underlying category fibred in setoids. This view retains the thin-fibre owner instead of
forgetting immediately to the groupoid-fibred or ambient stack layers. -/
@[stacks 0433 "stack-in-setoids underlying setoid-fibred category"]
abbrev toSetoids (X : StackOver.Setoids J) : FiberedCategoryOver.Setoids C :=
  ⟨X.toGroupoids.toBasedCategory, X.2⟩

/-- The underlying stack over the site. -/
@[stacks 0433 "stack-in-setoids underlying stack"]
abbrev toStackOver (X : StackOver.Setoids J) : StackOver J :=
  X.toGroupoids.toStackOver

/-- The underlying category fibred over the base category. -/
@[stacks 0433 "stack-in-setoids underlying fibred category"]
abbrev toFiberedCategoryOver (X : StackOver.Setoids J) : FiberedCategoryOver C :=
  X.toGroupoids.toFiberedCategoryOver

/-- The projection functor. -/
@[stacks 0433 "stack-in-setoids projection"]
abbrev p (X : StackOver.Setoids J) := X.toGroupoids.p

/-- The total category. -/
@[stacks 0433 "stack-in-setoids total category"]
abbrev total (X : StackOver.Setoids J) := X.toGroupoids.total

/-- The underlying based category. -/
@[stacks 0433 "stack-in-setoids based category"]
abbrev toBasedCategory (X : StackOver.Setoids J) : BasedCategory C :=
  X.toGroupoids.toBasedCategory

/-- Coerce to a stack in groupoids. -/
instance : CoeOut (StackOver.Setoids J) (StackOver.Groupoids J) where
  coe X := X.toGroupoids

/-- Coerce to the underlying category fibred in setoids. -/
instance : CoeOut (StackOver.Setoids J) (FiberedCategoryOver.Setoids C) where
  coe X := X.toSetoids

/-- Coerce to the ambient stack owner. -/
instance : CoeOut (StackOver.Setoids J) (StackOver J) where
  coe X := X.toStackOver

/-- Coerce to the ambient category fibred over the base. -/
instance : CoeOut (StackOver.Setoids J) (FiberedCategoryOver C) where
  coe X := X.toFiberedCategoryOver

/-- Coerce to the underlying based category. -/
instance : CoeOut (StackOver.Setoids J) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The setoid-fiber condition. -/
@[stacks 0433 "stack-in-setoids canonical instance"]
instance (X : StackOver.Setoids J) : Functor.IsFibered.InSetoids X.p := X.2

/-- The stack-in-setoids condition. -/
@[stacks 0433 "stack-in-setoids stack instance"]
instance (X : StackOver.Setoids J) : IsStack.InSetoids J X.p := sorry

/-- The site-level stack condition of a bundled stack in setoids is inherited from its
underlying bundled stack in groupoids.  Keeping this as an instance mirrors
`StackOver.Groupoids.isStackOnSite` and avoids rebuilding the condition at use sites. -/
@[stacks 0433 "stack-in-setoids site condition"]
instance isStackOnSite (X : StackOver.Setoids J) : IsStack.OnSite J X.p :=
  X.toGroupoids.property

/-- Bundle an existing setoid-fibred category satisfying descent without reconstructing its
total category from the projection. -/
@[stacks 0433 "stack-in-setoids bundling constructor"]
def mk (X : FiberedCategoryOver.Setoids C) (h : IsStack.OnSite J X.p) :
    StackOver.Setoids J :=
  ObjectProperty.FullSubbicategory.mk _
    (StackOver.Groupoids.mk
      ((FiberedCategoryOver.Setoids.toGroupoids C).obj X) h)
    X.property

namespace mk

/-- Forgetting a directly bundled setoid stack recovers the supplied setoid-fibred owner. -/
@[simp, stacks 0433 "stack-in-setoids bundling readout"]
theorem toSetoids (X : FiberedCategoryOver.Setoids C) (h : IsStack.OnSite J X.p) :
    (mk X h).toSetoids = X := sorry

/-- The explicit owner isomorphism for direct bundling of a setoid-fibred category. -/
@[stacks 0433 "stack-in-setoids bundling isomorphism"]
def toSetoidsIso (X : FiberedCategoryOver.Setoids C) (h : IsStack.OnSite J X.p) :
    (mk X h).toSetoids ≅ X :=
  ObjectProperty.FullSubbicategory.isoMk (Iso.refl X.1)

end mk

/-- Construct from a projection functor known to be a stack in setoids. -/
@[stacks 0433 "stack-in-setoids projection constructor"]
noncomputable abbrev ofProjection (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) [IsStack.InSetoids J p] :
    StackOver.Setoids J :=
  ⟨StackOver.Groupoids.ofProjection J p,
    (FiberedCategoryOver.Groupoids.ofFunctor.isSetoidStack J p).toInSetoids⟩

/-- Construct a bundled stack in setoids from an explicit stack-in-setoids proof.

This is the theorem-valued companion to `ofProjection`; it lets consumers bundle a canonical
projection without introducing a local typeclass instance. -/
@[stacks 0433 "stack-in-setoids explicit projection constructor"]
noncomputable abbrev ofProjectionWith (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) (h : IsStack.InSetoids J p) :
    StackOver.Setoids J :=
  @ofProjection C _ J S _ p h

end StackOver.Setoids

end CategoryTheory
