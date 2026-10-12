/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_37_1_Proper
public import stacks_project.Chap106.Lemma_106_11_3_FactorsThrough
public import stacks_project.Chap106.Lemma_106_11_3_DvrAlong

/-!
# Refined Noetherian DVR valuative criterion for properness of algebraic stacks

A finite-type separated morphism of algebraic stacks into a locally Noetherian
target is proper as soon as every DVR valuative 2-square whose generic
1-morphism factors through a dense finite-type morphism admits a dominating
valuation-ring extension with a nonempty dotted-arrow category.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

open ValuativeCriterion.DVR.Along

namespace Proper

/-- Lemma 106.11.3: let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic
stacks over a scheme `S`. Assume that `Y` is locally Noetherian, that `f` and
`h` are of finite type, that `f` is separated, and that the image of
`|h| : |U| ⟶ |X|` is dense in `|X|`. If every 2-commutative diagram
`Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` with `A` a discrete valuation ring and
`K` its field of fractions admits a field extension `K'/K` and a valuation
ring `A' ⊂ K'` dominating `A` whose induced dotted-arrow category is nonempty,
then `f` is proper. -/
@[stacks 0CQM]
theorem of_existsExtensionAlong {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h : U ⟶ X)
    [IsLocallyNoetherian Y] [FiniteType f] [FiniteType h] [Separated f]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (h_dense : @DenseRange (Points X) τ (Points U) (Points.map h))
    (h_existence : ExistsExtension h f) :
    Proper f :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicStack
