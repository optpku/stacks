/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap106.Lemma_106_11_4_Uniqueness

/-!
# Refined Noetherian DVR valuative criterion for separatedness of algebraic stacks

A locally of finite type quasi-separated morphism of algebraic stacks into a
locally Noetherian target is separated as soon as every DVR valuative 2-square
whose generic 1-morphism factors through a dense finite-type morphism has
dotted-arrow category empty or a setoid with exactly one isomorphism class.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

open ValuativeCriterion.DVR.Along

namespace Separated

/-- Lemma 106.11.4: let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic
stacks over a scheme `S`. Assume that `Y` is locally Noetherian, that `f` is
locally of finite type and quasi-separated, that `h` is of finite type, and
that the image of `|h| : |U| ⟶ |X|` is dense in `|X|`. If every 2-commutative
diagram `Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` with `A` a discrete valuation
ring and `K` its field of fractions has dotted-arrow category either empty or
a setoid with exactly one isomorphism class, then `f` is separated. -/
@[stacks 0E95]
theorem of_uniquenessAlong {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h : U ⟶ X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f] [FiniteType h]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (h_dense : @DenseRange (Points X) τ (Points U) (Points.map h))
    (h_uniqueness : Uniqueness h f) :
    Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicStack
