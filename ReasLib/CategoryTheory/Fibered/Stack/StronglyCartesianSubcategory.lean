/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.StronglyCartesianSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# The associated groupoid of a stack

Restricting a fibered category to its strongly cartesian morphisms gives its canonical associated
category fibered in groupoids. This file records that the construction preserves the stack
condition, independently of any bundled presentation or chosen cleavage.

The maps below give the object-and-`1`-morphism action needed for the stack construction. They do
not claim a pseudofunctor on arbitrary stack `2`-morphisms, whose components need not be strongly
cartesian.

## Main declarations

* `Functor.IsStronglyCartesian.projection_isStackOnSite` - the associated projection of a stack
  is again a stack.
* `Functor.IsStronglyCartesian.projection_isStackInGroupoids` - the associated projection is a
  stack in groupoids.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]

namespace Functor.IsStronglyCartesian

/-- The restriction of a stack projection to its strongly cartesian morphisms remains a stack.
This is the site-theoretic part of the associated-groupoid construction. -/
@[instance, stacks 03YI "strongly-cartesian projection preserves the stack condition"]
theorem projection_isStackOnSite
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsStack.OnSite J p] :
    IsStack.OnSite J (projection p) := sorry

/-- The associated groupoid projection of a stack is canonically a stack in groupoids. -/
@[stacks 03YI]
theorem projection_isStackInGroupoids
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsStack.OnSite J p] :
    IsStack.InGroupoids J (projection p) := sorry

end Functor.IsStronglyCartesian

namespace StackOver

variable {J : GrothendieckTopology C}

/-- The canonical associated groupoid of a stack, obtained by retaining all objects and only
the strongly cartesian morphisms. -/
@[stacks 03YI "associated groupoid of a stack"]
noncomputable def associatedGroupoid (X : StackOver.{uC, vC, uS, vS} J) :
    StackOver.Groupoids.{uC, vC, uS, vS} J :=
  ⟨X.toFiberedCategoryOver.associatedGroupoid,
    Functor.IsStronglyCartesian.projection_isStackOnSite J X.p⟩

namespace associatedGroupoid

/-- The groupoid-fibred view of the associated groupoid is the canonical strongly-cartesian
wide subcategory. -/
@[simp, stacks 03YI "stack associated-groupoid underlying groupoid-fibred category"]
theorem toGroupoids (X : StackOver.{uC, vC, uS, vS} J) :
    X.associatedGroupoid.toGroupoids =
      X.toFiberedCategoryOver.associatedGroupoid := sorry

/-- The projection of the associated groupoid is the restriction of the original projection to
strongly cartesian morphisms. -/
@[simp, stacks 03YI "stack associated-groupoid projection"]
theorem p (X : StackOver.{uC, vC, uS, vS} J) :
    X.associatedGroupoid.p = Functor.IsStronglyCartesian.projection X.p := sorry

/-- The canonical inclusion of the associated groupoid into the original stack. -/
@[stacks 03YI "stack associated-groupoid inclusion"]
noncomputable def inclusion (X : StackOver.{uC, vC, uS, vS} J) :
    X.associatedGroupoid.toStackOver ⟶ X :=
  StackOver.Hom.lift
    (FiberedCategoryOver.associatedGroupoid.inclusion
      X.toFiberedCategoryOver)

/-- Forgetting the stack condition from the associated-groupoid inclusion recovers the neutral
fibred-category inclusion. -/
@[simp, stacks 03YI "stack associated-groupoid inclusion underlying morphism"]
theorem inclusion.toMor (X : StackOver.{uC, vC, uS, vS} J) :
    StackOver.Hom.toMor (inclusion X) =
      FiberedCategoryOver.associatedGroupoid.inclusion
        X.toFiberedCategoryOver := sorry

variable {X Y : StackOver.{uC, vC, uS, vS} J}

/-- A morphism of stacks induces a morphism between their associated groupoid stacks. This is
the direct lift of the neutral associated-groupoid `1`-morphism action. -/
@[stacks 03YI "1-cell action on the associated groupoid of a stack"]
noncomputable def map (F : X ⟶ Y) : X.associatedGroupoid ⟶ Y.associatedGroupoid :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.associatedGroupoid.map (StackOver.Hom.toMor F))

/-- Forgetting a stack-level associated-groupoid map recovers the neutral map of
groupoid-fibred categories. -/
@[simp, stacks 03YI "stack associated-groupoid map underlying morphism"]
theorem map.toGroupoidsMor (F : X ⟶ Y) :
    StackOver.Groupoids.Hom.toGroupoidsMor (map F) =
      FiberedCategoryOver.associatedGroupoid.map (StackOver.Hom.toMor F) := sorry

/-- The associated-groupoid map of an identity stack morphism is the identity. -/
@[simp, stacks 03YI "stack associated-groupoid identity"]
theorem map_id (X : StackOver.{uC, vC, uS, vS} J) :
    map (𝟙 X) = 𝟙 X.associatedGroupoid := sorry

/-- Associated-groupoid maps of stack morphisms preserve composition. -/
@[simp, stacks 03YI "stack associated-groupoid composition"]
theorem map_comp
    {Z : StackOver.{uC, vC, uS, vS} J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    map (F ≫ G) = map F ≫ map G := sorry

/-- Regard the associated-groupoid map as a morphism of the underlying ordinary stacks. -/
@[stacks 03YI "ordinary stack bridge for associated-groupoid maps"]
noncomputable def map.toStackOver (F : X ⟶ Y) :
    X.associatedGroupoid.toStackOver ⟶ Y.associatedGroupoid.toStackOver :=
  StackOver.Hom.lift
    ((FiberedCategoryOver.Groupoids.toFibered C).map
      (StackOver.Groupoids.Hom.toGroupoidsMor (map F)))

/-- The ordinary-stack bridge has the expected underlying fibred-category morphism. -/
@[simp, stacks 03YI "ordinary stack associated-groupoid map computation"]
theorem map.toStackOver.toMor (F : X ⟶ Y) :
    StackOver.Hom.toMor (map.toStackOver F) =
      (FiberedCategoryOver.Groupoids.toFibered C).map
        (StackOver.Groupoids.Hom.toGroupoidsMor (map F)) := sorry

/-- Associated-groupoid inclusions are natural for morphisms of stacks, after viewing the
associated-groupoid map in the ordinary stack bicategory. -/
@[stacks 03YI "stack associated-groupoid inclusion naturality"]
theorem inclusion_naturality (F : X ⟶ Y) :
    map.toStackOver F ≫ inclusion Y = inclusion X ≫ F := sorry

end associatedGroupoid

end StackOver

end CategoryTheory
