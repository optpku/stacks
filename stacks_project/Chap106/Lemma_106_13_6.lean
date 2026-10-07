module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import stacks_project.Chap106.Definition_106_12_1_Moduli
public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine

/-!
# Uniform categorical moduli spaces of well-nigh affine stacks

If an algebraic stack is well-nigh affine, then a uniform categorical moduli
space in the category of affine schemes is a uniform categorical moduli space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- Lemma 106.13.6. Let the algebraic stack `X` be well-nigh affine. The morphism
`f : X ⟶ M.toGroupoids` of Lemma 106.13.4 is a uniform categorical moduli space. -/
@[stacks 0DUR, instance]
instance instIsUniformCategoricalModuliSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    IsUniformCategoricalModuliSpace f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
