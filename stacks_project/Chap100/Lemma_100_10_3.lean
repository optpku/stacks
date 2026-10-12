/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_11_Substack
public import stacks_project.Chap100.Lemma_100_10_1_Points
public import stacks_project.Chap100.Lemma_100_11_2_Reduced

/-!
# Maps from reduced algebraic stacks into closed substacks

A 1-morphism from a reduced algebraic stack factors through a closed substack if
and only if the induced map on points lands in that closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ClosedSubstack

/-- Lemma 100.10.3: Let `X`, `Y` be algebraic stacks. Let `Z ⊂ X` be a closed
substack. Assume `Y` is reduced. A morphism `f : Y ⟶ X` factors through `Z` if
and only if `f(|Y|) ⊂ |Z|`, i.e. `FactorsThrough f Z.ι` if and only if
`Set.range (Points.map f) ⊆ Z.pointsSet`. -/
@[stacks 050B]
theorem factorsThrough_iff_range_subset {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [IsReduced Y] (Z : ClosedSubstack X)
    (f : Y ⟶ X) :
    FactorsThrough f Z.ι ↔ Set.range (Points.map f) ⊆ Z.pointsSet :=
  sorry

/-- Two 2-isomorphic factorizations of a 1-morphism through a closed substack
are themselves 2-isomorphic. -/
theorem lift_unique {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (Z : ClosedSubstack X) {f : Y ⟶ X}
    {g g' : Y ⟶ Z.Y} (hg : g ≫ Z.ι ≅ f) (hg' : g' ≫ Z.ι ≅ f) :
    Nonempty (g ≅ g') :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ClosedSubstack
