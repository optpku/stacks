/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Absolute.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred-inertia pseudofunctor construction

This leaf owns the universe-changing strict pseudofunctor induced by absolute
inertia and its ordinary pseudofunctor view.
-/

@[expose] public section

universe u v uS vS uT vT w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

section PseudofunctorImplementation

/-- The ambient based inertia action sends fibred objects to fibred objects. -/
@[stacks 04Z4 "fibred absolute-inertia object closure"]
theorem objectLift.obj_mem
    (X : FiberedCategoryOver.{u, v, w, vS} C) :
    BasedCategory.isFibered C
      (((FiberedCategoryOver.toBased C).comp
        (BasedCategory.Inertia.strictPseudofunctor C)).obj X) := sorry
/- Proof strategy: identify the image with `BasedCategory.inertia X.toBasedCategory` and use
`BasedCategory.Inertia.Projection.Fibered.self`. -/

variable (C) in
/-- The object-property lift of based inertia to fibred objects. Its `1`- and `2`-cell actions
are inherited from the ambient based inertia pseudofunctor. -/
@[stacks 04Z4 "object-level lift of cartesian inertia"]
def objectLift :
    StrictPseudofunctor
      (FiberedCategoryOver.{u, v, w, vS} C)
      ((BasedCategory.isFibered.{u, v, max w vS, vS} C).FullSubbicategory) :=
  ObjectProperty.FullSubbicategory.lift
    ((FiberedCategoryOver.toBased C).comp
      (BasedCategory.Inertia.strictPseudofunctor C))
    objectLift.obj_mem

/-- The object-lifted inertia action preserves the hom property selecting cartesian based
functors. -/
@[stacks 04Z4 "fibred absolute-inertia hom-property closure"]
theorem objectLift.map_mem
    {X Y : FiberedCategoryOver.{u, v, w, vS} C} (F : X ⟶ Y) :
    FiberedCategoryOver.homProperty C
      ((Inertia.objectLift C).obj X) ((Inertia.objectLift C).obj Y)
      ((Inertia.objectLift C).map F).hom := sorry
/- Proof strategy: identify the lifted map with `BasedCategory.Inertia.map F.obj` and use
`FiberedCategoryOver.Inertia.map.preservesStronglyCartesian`. -/

variable (C) in
/-- Absolute inertia is the canonical two-stage universe-changing strict pseudofunctor on
fibred categories over `C`: first the ambient based inertia action is lifted through the
fibred-object property, then through the cartesian-functor hom property. Consequently all
non-Prop object, `1`-cell, and `2`-cell data and all strict coherence are inherited from the two
generic lifts. -/
@[stacks 04Z4 "strict cartesian absolute-inertia pseudofunctor"]
def strictPseudofunctor :
    StrictPseudofunctor
      (FiberedCategoryOver.{u, v, w, vS} C)
      (FiberedCategoryOver.{u, v, max w vS, vS} C) :=
  Bicategory.LocallyInducedBicategory.lift
    (objectLift C)
    objectLift.map_mem

variable (C) in
/-- The pseudofunctor view of the strict fibred-inertia pseudofunctor. Its identity and
composition comparisons lift the explicit based comparisons `mapIdIso` and `mapCompIso`. -/
@[stacks 04Z4 "cartesian absolute-inertia pseudofunctor"]
def pseudofunctor :
    Pseudofunctor
      (FiberedCategoryOver.{u, v, w, vS} C)
      (FiberedCategoryOver.{u, v, max w vS, vS} C) :=
  (strictPseudofunctor C).toPseudofunctor

end PseudofunctorImplementation

end FiberedCategoryOver.Inertia

end CategoryTheory
