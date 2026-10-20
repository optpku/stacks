module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage

/-!
# Dimension of scheme-theoretic images

The general fibre-dimension lower bound and equality on a nonempty dense open
subset, together with dimension bounds and the fibre-positivity dichotomy for
quasi-DM morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a locally-of-finite-type morphism between Jacobson, pseudo-catenary,
locally Noetherian algebraic stacks with irreducible source, quasi-separated
target and locally Noetherian scheme-theoretic image, the relative dimension at
every source point plus the dimension of the image is at least the dimension
of the source. -/
@[stacks 0DS4]
theorem relativeDimensionAt_schemeTheoreticImage_ge {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι]
    (t : Points T) :
    relativeDimensionAt f t + dimension Z ≥ dimension T :=
  sorry

/-- For a locally-of-finite-type morphism between Jacobson, pseudo-catenary,
locally Noetherian algebraic stacks with irreducible source, quasi-separated
target and locally Noetherian scheme-theoretic image, there is a nonempty dense
open subset of the source on which the relative dimension plus the dimension
of the image equals the dimension of the source. -/
@[stacks 0DS4]
theorem exists_isOpen_relativeDimensionAt_schemeTheoreticImage_eq
    {S : Scheme.{u}} {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    ∃ U : Set (Points T), IsOpen U ∧ U.Nonempty ∧ Dense U ∧
      ∀ t ∈ U, relativeDimensionAt f t + dimension Z = dimension T :=
  sorry

/-- The scheme-theoretic image of a locally-of-finite-type quasi-DM morphism
between Jacobson, pseudo-catenary, locally Noetherian algebraic stacks has
dimension at most that of the irreducible source when the target is
quasi-separated and the image is locally Noetherian. -/
@[stacks 0DS6]
theorem dimension_schemeTheoreticImage_le {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    dimension Z ≤ dimension T :=
  sorry

/-- For a locally-of-finite-type quasi-DM morphism between Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks with irreducible source,
quasi-separated target and locally Noetherian scheme-theoretic image, exactly
one of positivity of relative dimension at every finite-type source point and
equality of source and image dimensions holds. -/
@[stacks 0DS6]
theorem dimension_schemeTheoreticImage_xor {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    Xor (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t)
      (dimension T = dimension Z) :=
  sorry

/-- For a locally-of-finite-type quasi-DM morphism between Jacobson,
pseudo-catenary, locally Noetherian algebraic stacks with irreducible source,
quasi-separated target and locally Noetherian scheme-theoretic image, positivity
of relative dimension at every finite-type source point is equivalent to strict
dimension drop on passage to the image. -/
theorem dimension_schemeTheoreticImage_lt_iff {S : Scheme.{u}}
    {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι] :
    (∀ t : Points T, IsFiniteTypePoint t →
        (0 : EInt) < relativeDimensionAt f t) ↔
      dimension Z < dimension T :=
  sorry

end AlgebraicGeometry.AlgebraicStack
