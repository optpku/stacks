module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen

/-!
# Twisting sheaves on standard projective space

This file specializes the canonical twisting sheaves on a projective spectrum to standard
projective space over a commutative ring.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The canonical twisting sheaf of degree `d` on standard projective `n`-space over `R`. -/
@[stacks 01YS "standard projective-space twisting sheaf"]
noncomputable abbrev twistingSheaf
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) : (scheme R n).Modules :=
  Proj.AssociatedModule.twistingSheaf
    (R := R) (A := MvPolynomial (Fin (n + 1)) R) (grading R n) d

/-- The degree-`d` twist of a module sheaf on standard projective space. -/
@[stacks 01YS "standard projective-space tensor twist"]
noncomputable abbrev twist
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (d : ℤ) :
    (scheme R n).Modules :=
  ProjTwistFamily.tensorTwist
    (Proj.AssociatedModule.twistingSheaf
      (R := R) (A := MvPolynomial (Fin (n + 1)) R) (grading R n)) ℱ d

/-- Twisting a module sheaf by degree `d` is tensoring with the canonical degree-`d`
twisting sheaf. -/
theorem twist_def
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (d : ℤ) :
    twist R n ℱ d = ℱ ⊗ twistingSheaf R n d := sorry

end AlgebraicGeometry.ProjectiveSpace
