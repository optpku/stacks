module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford

/-!
# Algebraic stacks with no automorphisms

For an algebraic stack over a scheme `S`, being a stack in setoids, the
canonical inertia 1-morphism being an equivalence, and being representable by
an algebraic space are equivalent. The corresponding criteria with an
additional Deligne-Mumford condition are also recorded.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack over a scheme is Deligne-Mumford and a stack in setoids
if and only if it is Deligne-Mumford and its canonical inertia forgetful
1-morphism is an equivalence. -/
theorem inSetoids_iff_inertia_forget {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (DeligneMumfordStack X ∧
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p) ↔
      (DeligneMumfordStack X ∧
        (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence) := sorry

/-- An algebraic stack over a scheme is Deligne-Mumford and a stack in setoids
if and only if it is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_iff_deligneMumford_inSetoids
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (DeligneMumfordStack X ∧
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p) ↔
      IsRepresentableByAlgebraicSpace X := sorry

/-- An algebraic stack over a scheme is Deligne-Mumford with canonical inertia
forgetful 1-morphism an equivalence if and only if it is representable by an
algebraic space. -/
theorem isRepresentableByAlgebraicSpace_iff_deligneMumford_inertia
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (DeligneMumfordStack X ∧
        (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence) ↔
      IsRepresentableByAlgebraicSpace X := sorry

/-- An algebraic stack over a scheme is a stack in setoids if and only if its
canonical inertia forgetful 1-morphism is an equivalence. -/
theorem inSetoids_iff_inertia_isEquivalence {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ↔
      (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence := sorry

/-- An algebraic stack over a scheme is a stack in setoids if and only if it is
representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_iff_inSetoids {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ↔
      IsRepresentableByAlgebraicSpace X := sorry

/-- The canonical inertia forgetful 1-morphism of an algebraic stack over a
scheme is an equivalence if and only if the stack is representable by an
algebraic space. -/
theorem isRepresentableByAlgebraicSpace_iff_inertia_isEquivalence
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence ↔
      IsRepresentableByAlgebraicSpace X := sorry

end AlgebraicGeometry.AlgebraicStack
