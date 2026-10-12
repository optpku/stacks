/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap106.Lemma_106_11_5_DvrExtension

/-!
# Noetherian valuative criterion for universal closedness of algebraic stacks

A finite-type morphism of algebraic stacks into a locally Noetherian target is
universally closed as soon as every DVR valuative square admits a dominating
valuation-ring extension with a nonempty dotted-arrow category.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

/-- Lemma 106.11.5: a finite-type morphism `f : X ⟶ Y` of algebraic stacks
over a scheme `S` with `Y` locally Noetherian is universally closed whenever
every 2-commutative valuative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` with
`A` a discrete valuation ring and `K` its field of fractions admits a field
extension `K'/K` and a valuation ring `A' ⊂ K'` dominating `A` whose induced
dotted-arrow category is nonempty. -/
@[stacks 0H2C]
instance of_existsExtension {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [IsLocallyNoetherian Y]
    [ValuativeCriterion.DVR.ExistsExtension f] : UniversallyClosed f :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
