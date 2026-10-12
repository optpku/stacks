/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap99.Theorem_99_15_11_Algebraicity_of_the_stack_of_curves_Groupoids
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Theorem 99.15.11

The stack Curves of Situation 99.15.1 is algebraic. For any algebraic space
`B`, the stack `B`-Curves of Remark 99.15.5 is algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Theorem 99.15.11 (Algebraicity of the stack of curves) (1): the stack
`Curves` of Situation 99.15.1 is an algebraic stack over `S` in the sense of
Definition 94.12.1 at Hom-universe `u + 1`. -/
@[stacks 0D5A]
instance instAlgebraicStack (S : Scheme.{u}) :
    CohStack.AlgebraicStack (toGroupoids S) :=
  sorry

/-- `CohStack.AlgebraicStack (toGroupoids S)` is equivalent to the three clauses
of Definition 94.12.1: `p S` is a stack in groupoids over `(Sch/S)_fppf`, the
diagonal of `toGroupoids S` is representable by algebraic spaces, and there is a
scheme `U` over `S` with a surjective smooth 1-morphism
`Classifying.slice U ⟶ toGroupoids S`. -/
theorem algebraicStack_iff (S : Scheme.{u}) :
    CohStack.AlgebraicStack (toGroupoids S) ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (p S) ∧
        Classifying.relativelyRepresentableByAlgebraicSpaces
          (CohStack.diagonal (toGroupoids S)) ∧
        ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids S),
          Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoids S` admits a scheme `U` over `S` and a
surjective smooth 1-morphism `Classifying.slice U ⟶ toGroupoids S`. -/
theorem existsSmoothSurjectiveAtlas (S : Scheme.{u})
    [CohStack.AlgebraicStack (toGroupoids S)] :
    ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids S),
      Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

end Curves

namespace CurvesGroupoidsOver

/-- Theorem 99.15.11 (Algebraicity of the stack of curves) (2): for any
algebraic space `B` over `S`, the stack `B`-Curves of Remark 99.15.5 is an
algebraic stack over `S` in the sense of Definition 94.12.1 at Hom-universe
`u + 1`. -/
@[stacks 0D5A]
instance instAlgebraicStack {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CohStack.AlgebraicStack (toGroupoids B) :=
  sorry

/-- `CohStack.AlgebraicStack (toGroupoids B)` is equivalent to the three clauses
of Definition 94.12.1: `p B` is a stack in groupoids over `(Sch/S)_fppf`, the
diagonal of `toGroupoids B` is representable by algebraic spaces, and there is a
scheme `U` over `S` with a surjective smooth 1-morphism
`Classifying.slice U ⟶ toGroupoids B`. -/
theorem algebraicStack_iff {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CohStack.AlgebraicStack (toGroupoids B) ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (p B) ∧
        Classifying.relativelyRepresentableByAlgebraicSpaces
          (CohStack.diagonal (toGroupoids B)) ∧
        ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids B),
          Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoids B` admits a scheme `U` over `S` and a
surjective smooth 1-morphism `Classifying.slice U ⟶ toGroupoids B`. -/
theorem existsSmoothSurjectiveAtlas {S : Scheme.{u}} (B : AlgebraicSpace S)
    [CohStack.AlgebraicStack (toGroupoids B)] :
    ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids B),
      Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

end CurvesGroupoidsOver
end AlgebraicGeometry.AlgebraicSpace.Spaces
