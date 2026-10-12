/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import stacks_project.Chap99.Theorem_99_14_15_Algebraicity_of_the_stack_of_polarized_schemes_Groupoids

/-!
# Theorem 99.14.15

The stack Polarized of Situation 99.14.1 is algebraic. For any algebraic space
`B`, the stack `B`-Polarized of Remark 99.14.5 is algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Theorem 99.14.15 (Algebraicity of the stack of polarized schemes) (1): the
stack Polarized of Situation 99.14.1 is an algebraic stack over `specZ` in the
sense of Definition 94.12.1 at Hom-universe `u`. -/
@[stacks 0D4X]
instance instAlgebraicStack : AlgebraicStack toGroupoidsOverSpecZ :=
  sorry

/-- `AlgebraicStack toGroupoidsOverSpecZ` is equivalent to the three clauses of
Definition 94.12.1: `p ⋙ toOverSpecZ` is a stack in groupoids over
`(Sch / specZ)_fppf`, the diagonal of `toGroupoidsOverSpecZ` is representable by
algebraic spaces, and there is a scheme `U` over `specZ` with a surjective
smooth 1-morphism `GroupoidsOver.slice U ⟶ toGroupoidsOverSpecZ`. -/
theorem algebraicStack_iff :
    AlgebraicStack toGroupoidsOverSpecZ ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over specZ) toGroupoidsOverSpecZ.p ∧
        relativelyRepresentableByAlgebraicSpaces
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
            toGroupoidsOverSpecZ) ∧
        ∃ (U : Over specZ) (π : GroupoidsOver.slice U ⟶ toGroupoidsOverSpecZ),
          Groupoids.Hom.Smooth π ∧ Groupoids.Hom.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoidsOverSpecZ` admits a scheme `U` over `specZ`
and a surjective smooth 1-morphism
`GroupoidsOver.slice U ⟶ toGroupoidsOverSpecZ`. -/
theorem existsSmoothSurjectiveAtlas [AlgebraicStack toGroupoidsOverSpecZ] :
    ∃ (U : Over specZ) (π : GroupoidsOver.slice U ⟶ toGroupoidsOverSpecZ),
      Groupoids.Hom.Smooth π ∧ Groupoids.Hom.Surjective π :=
  sorry

namespace polarizedOver

/-- Theorem 99.14.15 (Algebraicity of the stack of polarized schemes) (2): for
any algebraic space `B` over `specZ`, the stack `B`-Polarized of Remark 99.14.5
is an algebraic stack over `specZ` in the sense of Definition 94.12.1 at
Hom-universe `u`. -/
@[stacks 0D4X]
instance instAlgebraicStack (B : AlgebraicSpace specZ) :
    AlgebraicStack (toGroupoids B) :=
  sorry

/-- `AlgebraicStack (toGroupoids B)` is equivalent to the three clauses of
Definition 94.12.1: `p B` is a stack in groupoids over `(Sch / specZ)_fppf`,
the diagonal of `toGroupoids B` is representable by algebraic spaces, and there
is a scheme `U` over `specZ` with a surjective smooth 1-morphism
`GroupoidsOver.slice U ⟶ toGroupoids B`. -/
theorem algebraicStack_iff (B : AlgebraicSpace specZ) :
    AlgebraicStack (toGroupoids B) ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over specZ) (p B) ∧
        relativelyRepresentableByAlgebraicSpaces
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
            (toGroupoids B)) ∧
        ∃ (U : Over specZ) (π : GroupoidsOver.slice U ⟶ toGroupoids B),
          Groupoids.Hom.Smooth π ∧ Groupoids.Hom.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoids B` admits a scheme `U` over `specZ` and a
surjective smooth 1-morphism `GroupoidsOver.slice U ⟶ toGroupoids B`. -/
theorem existsSmoothSurjectiveAtlas (B : AlgebraicSpace specZ)
    [AlgebraicStack (toGroupoids B)] :
    ∃ (U : Over specZ) (π : GroupoidsOver.slice U ⟶ toGroupoids B),
      Groupoids.Hom.Smooth π ∧ Groupoids.Hom.Surjective π :=
  sorry

end polarizedOver

end AlgebraicGeometry.Polarized
