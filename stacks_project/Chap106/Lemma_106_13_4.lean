module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism
public import stacks_project.Chap106.Definition_106_12_1_Moduli
public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine

/-!
# Uniform categorical moduli spaces of well-nigh affine stacks

A well-nigh affine algebraic stack admits a uniform categorical moduli space in
the category of affine schemes. That morphism is separated, quasi-compact, and
a universal homeomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsWellNighAffine

/-- Lemma 106.13.4 (1). Let the algebraic stack `X` be well-nigh affine. There
exists a uniform categorical moduli space `f : X ⟶ M.toGroupoids` in the
category of affine schemes. -/
@[stacks 0DUP]
theorem exists_isUniformCategoricalModuliSpaceIn_isAffine
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsWellNighAffine X] :
    ∃ (M : AlgebraicSpace S) (f : X ⟶ M.toGroupoids),
      IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f :=
  sorry

/-- Lemma 106.13.4 (2). Let the algebraic stack `X` be well-nigh affine. A
uniform categorical moduli space `f : X ⟶ M.toGroupoids` in the category of
affine schemes is separated. -/
@[stacks 0DUP, instance]
instance instSeparated {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    Separated f :=
  sorry

/-- Lemma 106.13.4 (3). Let the algebraic stack `X` be well-nigh affine. A
uniform categorical moduli space `f : X ⟶ M.toGroupoids` in the category of
affine schemes is quasi-compact. -/
@[stacks 0DUP, instance]
instance instQuasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    QuasiCompact f :=
  sorry

/-- Lemma 106.13.4 (4). Let the algebraic stack `X` be well-nigh affine. A
uniform categorical moduli space `f : X ⟶ M.toGroupoids` in the category of
affine schemes is a universal homeomorphism. -/
@[stacks 0DUP, instance]
instance instUniversalHomeomorphism {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsWellNighAffine X] {M : AlgebraicSpace S}
    (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpaceIn (@AlgebraicSpace.IsAffine S) f] :
    UniversalHomeomorphism f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
