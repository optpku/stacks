module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap94.Lemma_94_19_1_Localization
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_38_1_SchemeTheoreticImage
public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary
public import stacks_project.Chap107.Lemma_107_5_9_RelativeDimension
public import stacks_project.Chap107.Lemma_107_5_24_FiberDimension
public import stacks_project.Chap107.Lemma_107_5_24_Jacobson
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Dimensions of scheme-theoretic images of quasi-DM morphisms

A locally of finite type quasi-DM morphism of Jacobson, pseudo-catenary,
locally Noetherian algebraic stacks, with irreducible source and
quasi-separated target, cannot raise dimension on passage to the
scheme-theoretic image, and the inequality is strict precisely when every
finite-type fibre has positive dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.24 (1): if `f : T ⟶ X` is a locally of finite type quasi-DM
morphism of Jacobson, pseudo-catenary, locally Noetherian algebraic stacks,
with `T` irreducible and `X` quasi-separated, and `ι : Z ⟶ X` is the
scheme-theoretic image of `T`, then `dimension Z ≤ dimension T`. -/
@[stacks 0DS6]
theorem dimension_schemeTheoreticImage_le {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [QuasiSeparated
      (baseProjection.{u + 1, u, u + 1}
        (viewedOver (specULiftZIsTerminal.from S) X))]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    dimension Z ≤ dimension T :=
  sorry

/-- Lemma 107.5.24 (2): in the situation of Lemma 107.5.24 (1), exactly one of
the following holds: every finite-type point `t` of `|T|` has
`(0 : EInt) < relativeDimensionAt f t`; or `dimension T = dimension Z`. -/
@[stacks 0DS6]
theorem dimension_schemeTheoreticImage_xor {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [QuasiSeparated
      (baseProjection.{u + 1, u, u + 1}
        (viewedOver (specULiftZIsTerminal.from S) X))]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    Xor (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t)
      (dimension T = dimension Z) :=
  sorry

/-- In the situation of `dimension_schemeTheoreticImage_le`, every finite-type
fibre of `f` has positive dimension if and only if
`dimension Z < dimension T`. -/
theorem dimension_schemeTheoreticImage_lt_iff {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [QuasiSeparated
      (baseProjection.{u + 1, u, u + 1}
        (viewedOver (specULiftZIsTerminal.from S) X))]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t) ↔
      dimension Z < dimension T :=
  sorry

end AlgebraicGeometry.AlgebraicStack
