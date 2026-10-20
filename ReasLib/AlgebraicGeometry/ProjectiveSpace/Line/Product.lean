module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor

/-!
# Products of projective lines

This file owns the product of two projective lines over a common commutative base
and the associated external tensor-product twists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.Product

section CommRing

variable (R : Type u) [CommRing R]

/-- The product of two copies of the projective line over `R`. -/
abbrev scheme : Scheme.{u} :=
  Limits.pullback (ProjectiveLine.toSpec R) (ProjectiveLine.toSpec R)

/-- The projection from the product of projective lines to its first factor. -/
abbrev fst : scheme R ⟶ ProjectiveLine.scheme R :=
  Limits.pullback.fst (ProjectiveLine.toSpec R) (ProjectiveLine.toSpec R)

/-- The projection from the product of projective lines to its second factor. -/
abbrev snd : scheme R ⟶ ProjectiveLine.scheme R :=
  Limits.pullback.snd (ProjectiveLine.toSpec R) (ProjectiveLine.toSpec R)

/-- The structure morphism of the product of projective lines over `R`. -/
abbrev toSpec : scheme R ⟶ Spec (.of R) :=
  fst R ≫ ProjectiveLine.toSpec R

/-- The external tensor product of the degree-`a` and degree-`b` twists on the two factors. -/
abbrev twistingSheaf (a b : ℤ) : (scheme R).Modules :=
  externalTensorProduct (ProjectiveLine.toSpec R) (ProjectiveLine.toSpec R)
    (ProjectiveSpace.twistingSheaf R 1 a) (ProjectiveSpace.twistingSheaf R 1 b)

end CommRing

end AlgebraicGeometry.ProjectiveLine.Product
