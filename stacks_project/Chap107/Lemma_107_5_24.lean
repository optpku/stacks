/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Dimension
import StacksCheckRecall

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
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.24: the dimension of the scheme-theoretic image is at most that of the source. -/
@[stacks 0DS6] #check (AlgebraicGeometry.AlgebraicStack.dimension_schemeTheoreticImage_le :
    ∀ {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι],
    dimension Z ≤ dimension T)

/- Lemma 107.5.24: exactly one of fibre positivity and equality of dimensions holds. -/
@[stacks 0DS6] #check (AlgebraicGeometry.AlgebraicStack.dimension_schemeTheoreticImage_xor :
    ∀ {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι],
    Xor (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t)
      (dimension T = dimension Z))

/- Lemma 107.5.24: fibre positivity is equivalent to strict dimension drop. -/
@[stacks 0DS6] #check (AlgebraicGeometry.AlgebraicStack.dimension_schemeTheoreticImage_lt_iff :
    ∀ {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι],
    (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t) ↔
      dimension Z < dimension T)

end AlgebraicGeometry.AlgebraicStack
