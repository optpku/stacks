/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.ClosedImmersion

/-!
# Reduced induced structures and reduction

The reduced object property on a closed point-set is the intersection of the
essential images of all reduced closed immersions with that range on points.
Its restricted category gives the reduced induced stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids (toFunctor)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

namespace Substack

/-- The reduced object property consists of the objects in every reduced closed
immersion with the prescribed range on points. -/
def reducedProperty (Z : Closeds (Points X)) : ObjectProperty X.total :=
  fun x => ∀ (Y : GroupoidsOver S) [AlgebraicStack Y] (i : Y ⟶ X),
    ClosedImmersion i → Set.range (Points.map i) = Z.carrier → IsReduced Y →
      (toFunctor i).essImage x

/-- The reduced object property is the essential image of every reduced closed
immersion having the prescribed range on points. -/
theorem reducedProperty_eq_essImage (Z : Closeds (Points X))
    {Y : GroupoidsOver S} [AlgebraicStack Y] (i : Y ⟶ X) [ClosedImmersion i]
    (hZ : Set.range (Points.map i) = Z.carrier) (hY : IsReduced Y) :
    reducedProperty Z = (toFunctor i).essImage :=
  sorry

/-- The reduced object property defines a closed substack. -/
theorem reducedProperty_isClosed (Z : Closeds (Points X)) :
    IsClosed X (reducedProperty Z) :=
  sorry

/-- The closed substack defined by the reduced object property has exactly the
prescribed point-set. -/
theorem reducedProperty_pointsSet (Z : Closeds (Points X)) :
    pointsSet X (reducedProperty Z) (reducedProperty_isClosed Z) = Z.carrier :=
  sorry

/-- The category restricted to the reduced object property is reduced. -/
instance instIsReduced_reducedCategory (Z : Closeds (Points X)) :
    IsReduced (closedCategory X (reducedProperty Z) (reducedProperty_isClosed Z)) :=
  sorry

end Substack

namespace ClosedSubstackStructure

/-- The reduced induced structure on a closed point-set is its reduced object property. -/
@[reducible]
def reduced (Z : Closeds (Points X)) : ClosedSubstackStructure Z :=
  ⟨Substack.reducedProperty Z, Substack.reducedProperty_isClosed Z,
    Substack.reducedProperty_pointsSet Z⟩

/-- The reduced induced structure is reduced and has the prescribed range on points. -/
theorem reduced_spec (Z : Closeds (Points X)) :
    Set.range (Points.map (reduced Z).ι) = Z.carrier ∧ IsReduced (reduced Z).Y :=
  sorry

/-- Every reduced structure on a closed point-set has the same object property
as the reduced induced structure. -/
theorem reduced_unique {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z)
    (hT : IsReduced T.Y) : T.val = (reduced Z).val :=
  sorry

end ClosedSubstackStructure

/-- The reduction of an algebraic stack is the reduced induced stack on its whole point space. -/
abbrev reduction (X : GroupoidsOver S) [AlgebraicStack X] : GroupoidsOver S :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y

/-- The reduction includes into the ambient stack by the literal closed-substack inclusion. -/
abbrev reductionι (X : GroupoidsOver S) [AlgebraicStack X] : reduction X ⟶ X :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι

/-- The reduction is reduced, and its inclusion is a closed immersion surjective on points. -/
theorem reduction_spec (X : GroupoidsOver S) [AlgebraicStack X] :
    IsReduced (reduction X) ∧ ClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)) :=
  sorry

/-- The reduction is the underlying stack of the reduced structure on the top closed subset. -/
theorem reduction_eq_reduced_top (X : GroupoidsOver S) [AlgebraicStack X] :
    reduction X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y :=
  rfl

/-- The reduction inclusion is the inclusion of the reduced structure on the top closed subset. -/
theorem reductionι_eq_reduced_top_ι (X : GroupoidsOver S) [AlgebraicStack X] :
    reductionι X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι :=
  rfl

end AlgebraicGeometry.AlgebraicStack
