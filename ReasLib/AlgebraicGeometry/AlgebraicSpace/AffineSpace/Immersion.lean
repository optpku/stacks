module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Immersions into relative affine space

A morphism admits an immersion into relative affine space when it factors
through a finite-dimensional affine space over its target by an immersion.
Absolute quasi-separatedness alone does not guarantee such a factorization
for locally finite type morphisms from affine algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : U ⟶ X` of algebraic spaces factors as an immersion into
some finite-dimensional relative affine space
`AffineSpace (ULift (Fin n)) X` over `X`. -/
def existsImmersionToAffineSpace {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) : Prop :=
  ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
    IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f

/-- A morphism of algebraic spaces admits an immersion into some relative affine
space over the target if and only if it equals the structure morphism of that
affine space after an immersion. -/
theorem existsImmersionToAffineSpace_iff {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) :
    existsImmersionToAffineSpace f ↔
      ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
        IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f :=
  Iff.rfl

/-- Every locally finite type morphism from an affine algebraic space into an
absolutely quasi-separated and absolutely locally separated algebraic space
admits an immersion into a finite-dimensional relative affine space over its
target. -/
theorem exists_immersion_to_affineSpace {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) [IsAffine U] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyLocallySeparated X] :
    existsImmersionToAffineSpace f :=
  sorry

/-- There exist an affine algebraic space `U` and a locally finite type
morphism `f : U ⟶ X` into an absolutely quasi-separated
algebraic space `X` which does not immerse into any
`AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088M]
theorem exists_quasiSeparated_without_immersion_to_affineSpace :
    ∃ (S : Scheme.{u}) (X U : AlgebraicSpace S) (f : U ⟶ X),
      IsAffine U ∧ LocallyOfFiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f :=
  sorry

/-- There exists a finite type morphism `f : Y ⟶ X` of algebraic spaces,
with `Y` affine and `X` absolutely quasi-separated, which does not admit an
immersion into any finite-dimensional relative affine space over `X`. -/
@[stacks 088W]
theorem exists_finiteType_without_immersion_to_affineSpace :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsAffine Y ∧ FiniteType f ∧ IsAbsolutelyQuasiSeparated X ∧
        ¬ existsImmersionToAffineSpace f :=
  sorry

/-- The proposition that every locally finite type morphism from an affine
algebraic space to an absolutely locally separated algebraic space admits an
immersion into a finite-dimensional relative affine space over its target.
This proposition is posed as an open question. -/
@[stacks 088M]
def existsImmersionToAffineSpace_of_locallySeparated : Prop :=
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
    IsAffine U → LocallyOfFiniteType f → IsAbsolutelyLocallySeparated X →
      existsImmersionToAffineSpace f

/-- The locally-separated-only immersion proposition states that every
locally finite type morphism from an affine algebraic space into an
absolutely locally separated algebraic space immerses into some relative affine
space over the target. -/
theorem existsImmersionToAffineSpace_of_locallySeparated_iff :
    existsImmersionToAffineSpace_of_locallySeparated.{u} ↔
      ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (f : U ⟶ X),
        IsAffine U → LocallyOfFiniteType f → IsAbsolutelyLocallySeparated X →
          existsImmersionToAffineSpace f :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
