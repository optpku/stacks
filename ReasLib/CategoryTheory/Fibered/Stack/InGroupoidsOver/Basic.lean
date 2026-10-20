module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Definition
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.LocalProperties
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction

/-!
# Stacks in groupoids over a site

This file defines the bundled object layer for stacks in groupoids: its full-subbicategory
owner, canonical forgetful views, coercions, instances, and direct constructors.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory Bicategory.InducedBicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The object property selecting stacks in groupoids inside `FiberedCategoryOver.Groupoids C`. -/
@[stacks 02ZK "stack-in-groupoids object property"]
abbrev IsStack.InGroupoids.objectProperty (J : GrothendieckTopology C) :
    ObjectProperty (FiberedCategoryOver.Groupoids C) :=
  fun X ↦ IsStack.OnSite J X.p

/-- The `2`-category of stacks in groupoids over `(C, J)`.

Its objects satisfy descent, while its `1`- and `2`-morphisms are the corresponding morphisms
and vertical transformations of groupoid-fibred categories over `C`. -/
@[stacks 02ZK]
abbrev StackOver.Groupoids (J : GrothendieckTopology C) :=
  (IsStack.InGroupoids.objectProperty J).FullSubbicategory

namespace FiberedCategoryOver.Groupoids.ofFunctor

/-- Bundling a stack-in-groupoids projection as a groupoid-fibered category preserves its
stack-in-groupoids condition. -/
@[stacks 02ZK "stack-in-groupoids projection closure"]
theorem isStack
    (J : GrothendieckTopology C) {S : Type*} [Category S] (p : S ⥤ C)
    [IsStack.InGroupoids J p] :
    IsStack.InGroupoids J (FiberedCategoryOver.Groupoids.ofFunctor p).p := sorry

end FiberedCategoryOver.Groupoids.ofFunctor

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

/-- The canonical strict forgetful pseudofunctor from stacks in groupoids to categories fibred
in groupoids. -/
@[stacks 02ZK "stack-in-groupoids forgetful pseudofunctor"]
abbrev forget (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.Groupoids J)
      (FiberedCategoryOver.Groupoids C) :=
  ObjectProperty.FullSubbicategory.ι _

/-- The underlying groupoid-fibered category. -/
@[stacks 02ZK "underlying groupoid-fibred category of a stack"]
abbrev toGroupoids (X : StackOver.Groupoids J) : FiberedCategoryOver.Groupoids C :=
  (forget J).obj X

/-- The underlying fibered category over `C`. -/
@[stacks 02ZK "underlying fibred category of a groupoid stack"]
abbrev toFiberedCategoryOver (X : StackOver.Groupoids J) :
    FiberedCategoryOver C :=
  ⟨X.toGroupoids.1, X.toGroupoids.2.toIsFibered⟩

/-- Coerce to the 2-category of all stacks. -/
@[stacks 02ZK "underlying ordinary stack of a groupoid stack"]
abbrev toStackOver (X : StackOver.Groupoids J) : StackOver J :=
  ⟨X.toFiberedCategoryOver, X.property⟩

/-- The projection functor. -/
@[stacks 02ZK "projection of a stack in groupoids"]
abbrev p (X : StackOver.Groupoids J) := X.toGroupoids.p

/-- The total category. -/
@[stacks 02ZK "total category of a stack in groupoids"]
abbrev total (X : StackOver.Groupoids J) := X.toGroupoids.total

/-- The underlying based category. -/
@[stacks 02ZK "based category of a stack in groupoids"]
abbrev toBasedCategory (X : StackOver.Groupoids J) : BasedCategory C :=
  X.toGroupoids.toBasedCategory

/-- Coerce to the ambient stack owner. -/
instance : CoeOut (StackOver.Groupoids J) (StackOver J) where
  coe X := X.toStackOver

/-- Coerce to the underlying groupoid-fibred category. -/
instance : CoeOut (StackOver.Groupoids J) (FiberedCategoryOver.Groupoids C) where
  coe X := X.toGroupoids

/-- Coerce to the ambient fibred category. -/
instance : CoeOut (StackOver.Groupoids J) (FiberedCategoryOver C) where
  coe X := X.toFiberedCategoryOver

/-- Coerce to the underlying based category. -/
instance : CoeOut (StackOver.Groupoids J) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The stack condition. -/
@[stacks 02ZK "stack-in-groupoids site condition"]
instance isStackOnSite (X : StackOver.Groupoids J) : IsStack.OnSite J X.p := X.property

/-- The stack-in-groupoids condition. -/
@[stacks 02ZK "stack-in-groupoids canonical instance"]
instance isStack (X : StackOver.Groupoids J) : IsStack.InGroupoids J X.p := sorry

/-- Bundle an existing groupoid-fibred category satisfying descent without reconstructing its
total category from the projection. -/
@[stacks 02ZK "stack-in-groupoids bundling constructor"]
def mk (X : FiberedCategoryOver.Groupoids C) (h : IsStack.OnSite J X.p) :
    StackOver.Groupoids J :=
  ObjectProperty.FullSubbicategory.mk _ X h

namespace mk

/-- Forgetting a directly bundled groupoid stack recovers the supplied groupoid-fibred owner. -/
@[simp, stacks 02ZK "stack-in-groupoids bundling readout"]
theorem toGroupoids (X : FiberedCategoryOver.Groupoids C) (h : IsStack.OnSite J X.p) :
    (mk X h).toGroupoids = X := sorry

/-- The explicit owner isomorphism for direct bundling of a groupoid-fibred category. -/
@[stacks 02ZK "stack-in-groupoids bundling isomorphism"]
def toGroupoidsIso (X : FiberedCategoryOver.Groupoids C) (h : IsStack.OnSite J X.p) :
    (mk X h).toGroupoids ≅ X :=
  ObjectProperty.FullSubbicategory.isoMk (Iso.refl X.1)

end mk

/-- Construct from a projection functor that is a stack in groupoids. -/
@[stacks 02ZK "stack-in-groupoids projection constructor"]
noncomputable abbrev ofProjection (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) [IsStack.InGroupoids J p] :
    StackOver.Groupoids J :=
  ⟨FiberedCategoryOver.Groupoids.ofFunctor p,
    (FiberedCategoryOver.Groupoids.ofFunctor.isStack J p).toOnSite⟩

/-- Construct a bundled stack in groupoids from an explicit stack-in-groupoids proof.

This theorem-valued bridge avoids installing a proof-local instance when the stack condition is
obtained from another reusable theorem. -/
@[stacks 02ZK "stack-in-groupoids explicit projection constructor"]
noncomputable abbrev ofProjectionWith (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) (h : IsStack.InGroupoids J p) :
    StackOver.Groupoids J :=
  @ofProjection C _ J S _ p h

variable (X : StackOver.Groupoids J)

end StackOver.Groupoids

end CategoryTheory
