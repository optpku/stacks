module

public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap67.Lemma_67_49_7_Normalization
public import stacks_project.Chap67.Lemma_67_49_7_Reduction

/-!
# Normalization of the reduction of an algebraic space

If an algebraic space satisfies the equivalent conditions of Lemma 67.49.1, its
absolute normalization morphism factors through any reduction inclusion, and the
factor is an absolute normalization of the reduced space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Normalization

/-- Lemma 67.49.7 (1): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. If `ν : Xν ⟶ X` is an
absolute normalization morphism and `ι : Xred ⟶ X` is a reduction inclusion,
then `ν` factors through `ι`. -/
@[stacks 0BB3]
theorem factorsThroughReduction {S : Scheme.{u}} {X Xν Xred : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {ν : Xν ⟶ X} [IsNormalizationTo ν] {ι : Xred ⟶ X} [IsReduction ι] :
    ∃ νred : Xν ⟶ Xred, νred ≫ ι = ν :=
  sorry

/-- Lemma 67.49.7 (2): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. If `ν : Xν ⟶ X` is an
absolute normalization morphism, `ι : Xred ⟶ X` is a reduction inclusion, and
`νred : Xν ⟶ Xred` factors `ν` through `ι`, then `νred` is an absolute
normalization morphism of `Xred`. -/
@[stacks 0BB3]
theorem reductionFactorIsNormalization {S : Scheme.{u}}
    {X Xν Xred : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {ν : Xν ⟶ X} [IsNormalizationTo ν] {ι : Xred ⟶ X} [IsReduction ι]
    {νred : Xν ⟶ Xred} (hfac : νred ≫ ι = ν) :
    IsNormalizationTo νred :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Normalization
