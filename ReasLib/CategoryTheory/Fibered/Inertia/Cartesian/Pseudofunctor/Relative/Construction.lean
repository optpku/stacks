module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Map.Relative.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Construction

/-!
# The fibred relative-inertia pseudofunctor

Relative inertia is first evaluated by the existing based pseudo-comma
pseudofunctor.  The result is then lifted through the property of having a
fibred projection and the hom property of preserving strongly cartesian
morphisms.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The based relative-inertia action on fibred pseudo-comma squares, before restoring the
fibred object and cartesian-morphism properties. -/
noncomputable def basedPseudofunctor :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
      (BasedCategory.{vS, max w vS} C) :=
  (toBased C).comp
    (BasedCategory.RelativeInertia.pseudoComma.pseudofunctor C)

/-- The based relative inertia of a fibred pseudo-comma object again has fibred projection. -/
theorem objectLift.obj_mem
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    BasedCategory.isFibered C ((basedPseudofunctor C).obj S) := sorry

variable (C) in
/-- Lift based relative inertia through the object property selecting fibred projections. -/
noncomputable def objectLift :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
      ((BasedCategory.isFibered.{u, v, max w vS, vS} C).FullSubbicategory) :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (basedPseudofunctor C) objectLift.obj_mem

/-- The object-lifted relative-inertia action sends every pseudo-comma square to a based
functor preserving strongly cartesian arrows. -/
theorem objectLift.map_mem
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) :
    FiberedCategoryOver.homProperty C
      ((objectLift C).obj S) ((objectLift C).obj T)
      ((objectLift C).map f).hom := sorry

variable (C) in
/-- Relative inertia is the canonical pseudofunctor from invertibly commuting squares of
fibred-category morphisms to fibred categories.

Its non-`Prop` data come from
`BasedCategory.RelativeInertia.pseudoComma.pseudofunctor`; the two generic lifts add only the
fibred-object and strongly-cartesian-preservation witnesses.  There is intentionally no
`strictPseudofunctor`: the based relative-inertia core has genuine identity and composition
comparison isomorphisms. -/
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
      (FiberedCategoryOver.{u, v, max w vS, vS} C) :=
  Bicategory.LocallyInducedBicategory.liftPseudofunctor
    (objectLift C) objectLift.map_mem

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
