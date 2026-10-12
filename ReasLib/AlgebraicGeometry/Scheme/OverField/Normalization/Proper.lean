/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

/-!
# Proper and projective normalizations over a field

This module records that normalization preserves properness and projectivity for schemes over a
field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Normalization

variable {k : Type u} [Field k]

/-- The normalization of a proper scheme over a field is proper over the same field. -/
instance instIsProperNormalization
    (X : SchemeOverField k) [IsProper X.hom] :
    IsProper (SchemeOverField.normalization X).hom := sorry

/-- The normalization of a projective scheme over a field is projective over the same field. -/
instance instProjectiveNormalization
    (X : SchemeOverField k) [Projective X.hom] :
    Projective (SchemeOverField.normalization X).hom := sorry

end AlgebraicGeometry.SchemeOverField.Normalization
