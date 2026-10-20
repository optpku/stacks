module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Construction

/-!
# Inertia of algebraic stacks

Absolute and relative inertia of algebraic stacks are algebraic stacks. Their
canonical projections are representable by algebraic spaces and locally of
finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (inertia relativeInertia)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

open FiberedCategoryOver.Groupoids.Inertia (forget)

/-- The inertia stack of an algebraic stack is an algebraic stack. -/
@[stacks 050Q, instance]
instance instAlgebraicStack {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] : AlgebraicStack (inertia X) :=
  sorry

/-- The canonical projection from the inertia stack of an algebraic stack is
representable by algebraic spaces and locally of finite type. -/
@[stacks 050Q, instance]
instance instLocallyOfFiniteType_forget {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] :
    Groupoids.Hom.LocallyOfFiniteType (forget.{u + 1, u, u, u + 1} X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

open FiberedCategoryOver.Groupoids.RelativeInertia (forget)

/-- The relative inertia of a morphism of algebraic stacks is an algebraic stack. -/
@[stacks 050Q, instance]
instance instAlgebraicStack {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    AlgebraicStack (relativeInertia f) :=
  sorry

/-- The canonical projection from the relative inertia of a morphism of algebraic
stacks is representable by algebraic spaces and locally of finite type. -/
@[stacks 050Q, instance]
instance instLocallyOfFiniteType_forget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Groupoids.Hom.LocallyOfFiniteType (forget.{u + 1, u, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia
