/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.Factorization

/-!
# Factorization through closed immersions of algebraic stacks

Morphisms from reduced algebraic stacks factor through closed immersions exactly
when their images on points lie in the range of the closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom.ClosedImmersion

/-- A morphism from a reduced algebraic stack factors through a closed immersion
if and only if its range on points is contained in that of the closed immersion. -/
theorem factorsThrough_iff_range_subset {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    [AlgebraicStack.IsReduced Y] (i : Z ⟶ X) [ClosedImmersion i] (f : Y ⟶ X) :
    FactorsThrough f i ↔
      Set.range (AlgebraicStack.Points.map f) ⊆ Set.range (AlgebraicStack.Points.map i) := sorry

/-- Two factorizations of a morphism through a closed immersion of algebraic
stacks, each equipped with a factorization 2-isomorphism, are 2-isomorphic. -/
theorem lift_unique {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (i : Z ⟶ X) [ClosedImmersion i] {f : Y ⟶ X} {g g' : Y ⟶ Z}
    (hg : g ≫ i ≅ f) (hg' : g' ≫ i ≅ f) : Nonempty (g ≅ g') := sorry

end AlgebraicGeometry.Groupoids.Hom.ClosedImmersion
