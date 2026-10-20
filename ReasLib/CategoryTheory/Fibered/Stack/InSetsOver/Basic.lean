module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Setoids.ToSetoidsFiber
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Basic
import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Restriction

/-!
# Stacks in sets over a site

This file defines the bundled object layer for stacks in sets: the full-subcategory owner, its
canonical forgetful views, and constructors from set-fibred categories and projections.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- The object property selecting stacks in sets inside `StackOver.Setoids J`. -/
@[stacks 042Z "stack-in-sets object property"]
abbrev IsStack.InSets.objectProperty (J : GrothendieckTopology C) :
    ObjectProperty (StackOver.Setoids J) :=
  fun X ↦ Functor.IsDiscreteFibration X.p

/-- The `2`-category of stacks in sets over `(C, J)`. -/
@[stacks 042Z "stacks in sets"]
abbrev StackOver.Sets (J : GrothendieckTopology C) :=
  (IsStack.InSets.objectProperty J).FullSubbicategory

namespace StackOver.Sets

variable {J : GrothendieckTopology C}

/-- The canonical strict forgetful pseudofunctor from stacks in sets to stacks in setoids. -/
@[stacks 042Z "stack-in-sets forgetful pseudofunctor"]
abbrev forget (J : GrothendieckTopology C) :
    StrictPseudofunctor (StackOver.Sets J) (StackOver.Setoids J) :=
  ObjectProperty.FullSubbicategory.ι _

/-- The underlying stack in setoids. -/
@[stacks 042Z "stack-in-sets underlying setoid stack"]
abbrev toSetoids (X : StackOver.Sets J) : StackOver.Setoids J :=
  (forget J).obj X

/-- The underlying category fibred in sets. -/
@[stacks 042Z "stack-in-sets underlying set-fibred category"]
abbrev toSets (X : StackOver.Sets J) : FiberedCategoryOver.Sets C :=
  ⟨X.toSetoids.toBasedCategory, X.2⟩

/-- Forgetting the set-valued owner from `toSets` gives the same setoid-fibred category as
forgetting the bundled stack in sets to a stack in setoids. -/
@[simp, stacks 02ZK "set-stack underlying setoid-stack readout"]
theorem toSets.toSetoids (X : StackOver.Sets J) :
    (FiberedCategoryOver.Sets.toSetoids C).obj X.toSets = X.toSetoids.toSetoids := sorry

/-- The underlying stack in groupoids. -/
@[stacks 042Z "stack-in-sets underlying groupoid stack"]
abbrev toGroupoids (X : StackOver.Sets J) : StackOver.Groupoids J :=
  X.toSetoids.toGroupoids

/-- The underlying stack over the site. -/
@[stacks 042Z "stack-in-sets underlying stack"]
abbrev toStackOver (X : StackOver.Sets J) : StackOver J :=
  X.toSetoids.toStackOver

/-- The underlying category fibred over `C`. -/
@[stacks 042Z "stack-in-sets underlying fibred category"]
abbrev toFiberedCategoryOver (X : StackOver.Sets J) : FiberedCategoryOver C :=
  X.toSetoids.toFiberedCategoryOver

/-- The projection functor. -/
@[stacks 042Z "stack-in-sets projection"]
abbrev p (X : StackOver.Sets J) := X.toSetoids.p

/-- The total category. -/
@[stacks 042Z "stack-in-sets total category"]
abbrev total (X : StackOver.Sets J) := X.toSetoids.total

/-- The underlying based category. -/
@[stacks 042Z "stack-in-sets based category"]
abbrev toBasedCategory (X : StackOver.Sets J) : BasedCategory C :=
  X.toSetoids.toBasedCategory

/-- Coerce to a stack in setoids. -/
instance : CoeOut (StackOver.Sets J) (StackOver.Setoids J) where
  coe X := X.toSetoids

/-- Coerce to the underlying category fibred in sets. -/
instance : CoeOut (StackOver.Sets J) (FiberedCategoryOver.Sets C) where
  coe X := X.toSets

/-- Coerce to a stack in groupoids. -/
instance : CoeOut (StackOver.Sets J) (StackOver.Groupoids J) where
  coe X := X.toGroupoids

/-- Coerce to the ambient stack owner. -/
instance : CoeOut (StackOver.Sets J) (StackOver J) where
  coe X := X.toStackOver

/-- Coerce to the ambient category fibred over the base. -/
instance : CoeOut (StackOver.Sets J) (FiberedCategoryOver C) where
  coe X := X.toFiberedCategoryOver

/-- Coerce to the underlying based category. -/
instance : CoeOut (StackOver.Sets J) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The discrete-fibration condition of a stack in sets. -/
@[stacks 042Z "stack-in-sets discrete-fibration instance"]
instance (X : StackOver.Sets J) : Functor.IsDiscreteFibration X.p := X.2

/-- The stack-in-sets condition of a bundled stack in sets. -/
@[stacks 042Z "stack-in-sets canonical instance"]
instance (X : StackOver.Sets J) : IsStack.InSets J X.p := sorry

/-- Bundle an existing set-fibred category satisfying descent without reconstructing its total
category from the projection. -/
@[stacks 042Z "stack-in-sets bundling constructor"]
def mk (X : FiberedCategoryOver.Sets C) (h : IsStack.OnSite J X.p) :
    StackOver.Sets J :=
  ObjectProperty.FullSubbicategory.mk _
    (StackOver.Setoids.mk ((FiberedCategoryOver.Sets.toSetoids C).obj X) h)
    X.property

namespace mk

/-- Forgetting a directly bundled set stack recovers the supplied set-fibred owner. -/
@[simp, stacks 042Z "stack-in-sets bundling readout"]
theorem toSets (X : FiberedCategoryOver.Sets C) (h : IsStack.OnSite J X.p) :
    (mk X h).toSets = X := sorry

/-- The explicit owner isomorphism for direct bundling of a set-fibred category. -/
@[stacks 042Z "stack-in-sets bundling isomorphism"]
def toSetsIso (X : FiberedCategoryOver.Sets C) (h : IsStack.OnSite J X.p) :
    (mk X h).toSets ≅ X :=
  ObjectProperty.FullSubbicategory.isoMk (Iso.refl X.1)

end mk

namespace ofProjection

/-- The projection underlying `StackOver.Setoids.ofProjection J p` remains discrete whenever
`p` is a stack in sets. -/
@[stacks 042Z "stack-in-sets projection closure"]
theorem isDiscreteFibration
    (J : GrothendieckTopology C) {S : Type*} [Category S] (p : S ⥤ C)
    [IsStack.InSets J p] :
    Functor.IsDiscreteFibration (StackOver.Setoids.ofProjection J p).p := sorry

end ofProjection

/-- Construct a bundled stack in sets from a projection carrying the canonical typeclass. -/
@[stacks 042Z "stack-in-sets projection constructor"]
noncomputable abbrev ofProjection (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) [IsStack.InSets J p] :
    StackOver.Sets J :=
  ⟨StackOver.Setoids.ofProjection J p, ofProjection.isDiscreteFibration J p⟩

/-- Construct a bundled stack in sets from an explicit stack-in-sets proof.

This bridge is useful for source statements whose stack condition is supplied by a theorem rather
than typeclass search; it avoids a proof-local `letI`. -/
@[stacks 042Z "stack-in-sets explicit projection constructor"]
noncomputable abbrev ofProjectionWith (J : GrothendieckTopology C)
    {S : Type*} [Category S] (p : S ⥤ C) (h : IsStack.InSets J p) :
    StackOver.Sets J :=
  @ofProjection C _ J S _ p h

end StackOver.Sets

end CategoryTheory
