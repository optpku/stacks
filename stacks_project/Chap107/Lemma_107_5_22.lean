module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Dimension

/-!
# Fibre dimensions versus the scheme-theoretic image

A locally of finite type morphism of Jacobson, pseudo-catenary, locally
Noetherian algebraic stacks, with irreducible source and quasi-separated
target, has fibre dimension at least `dimension T - dimension Z` at every
point of `Points T`, where `Z` is the scheme-theoretic image, and equality
holds on a nonempty (equivalently, dense) open of `Points T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.22 (1): if `f : T ⟶ X` is a locally of finite type morphism of
Jacobson, pseudo-catenary, locally Noetherian algebraic stacks, with `T`
irreducible and `X` quasi-separated, and `ι : Z ⟶ X` is the scheme-theoretic
image of `T`, then `relativeDimensionAt f t + dimension Z ≥ dimension T` for
every `t : Points T`. This encodes the source inequality
`relativeDimensionAt f t ≥ dimension T - dimension Z` additively in `EInt`. -/
@[stacks 0DS4] #check
  (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_schemeTheoreticImage_ge :
    ∀ {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι]
    (t : Points T),
    relativeDimensionAt f t + dimension Z ≥ dimension T)

/- Lemma 107.5.22 (2): in the situation of Lemma 107.5.22 (1), there is a
nonempty (equivalently, dense) open subset of `Points T` on which
`relativeDimensionAt f t + dimension Z = dimension T`. -/
@[stacks 0DS4] #check
  (AlgebraicGeometry.AlgebraicStack.exists_isOpen_relativeDimensionAt_schemeTheoreticImage_eq :
    ∀ {S : Scheme.{u}} {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι],
    ∃ U : Set (Points T), IsOpen U ∧ U.Nonempty ∧ Dense U ∧
      ∀ t ∈ U, relativeDimensionAt f t + dimension Z = dimension T)

end AlgebraicGeometry.AlgebraicStack
