module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Affine covers of projective varieties

Every projective variety over a field admits a surjective morphism from an affine
variety over the same field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveVariety

/-- A projective variety over a field admits a surjective morphism from an affine variety. -/
theorem exists_affine_surjective {k : Type u} [Field k] (X : SchemeOverField k)
    [ProjectiveVariety X] :
    ∃ (U : SchemeOverField k) (hU : AffineVariety U) (f : U ⟶ X),
      Surjective f.left := sorry

end AlgebraicGeometry.ProjectiveVariety
