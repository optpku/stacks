/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Coordinate divisors on the relative projective line

The two standard homogeneous coordinates determine closed subschemes of the projective line
over an arbitrary scheme by pullback from the integral model.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.Relative

/-- The projection from the relative projective line to its integral projective-line model. -/
abbrev toIntegerModel (S : Scheme.{u}) :
    ProjectiveSpace 1 S ⟶ ProjectiveLine.scheme (ULift.{u} ℤ) :=
  pullback.snd (terminal.from S)
    (terminal.from (ProjectiveLine.scheme (ULift.{u} ℤ)))

/-- The homogeneous zero locus `V(T₁)` in the integral projective line. -/
def zeroCoordinateLocus :
    TopologicalSpace.Closeds (ProjectiveLine.scheme (ULift.{u} ℤ)) :=
  ⟨ProjectiveSpectrum.zeroLocus (ProjectiveLine.grading (ULift.{u} ℤ))
      {ProjectiveLine.y (ULift.{u} ℤ)},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The homogeneous zero locus `V(T₀)` in the integral projective line. -/
def infinityCoordinateLocus :
    TopologicalSpace.Closeds (ProjectiveLine.scheme (ULift.{u} ℤ)) :=
  ⟨ProjectiveSpectrum.zeroLocus (ProjectiveLine.grading (ULift.{u} ℤ))
      {ProjectiveLine.x (ULift.{u} ℤ)},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The divisor `D₀ = V(T₁)` on the relative projective line over `S`, with its scheme
structure obtained by pulling back the integral vanishing ideal. -/
noncomputable def zeroDivisor (S : Scheme.{u}) :
    (ProjectiveSpace 1 S).IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal zeroCoordinateLocus).comap (toIntegerModel S)

/-- The support of `zeroDivisor S` is the inverse image of the homogeneous zero locus
`V(T₁)`. -/
theorem zeroDivisor_support (S : Scheme.{u}) :
    ((zeroDivisor S).support : Set (ProjectiveSpace 1 S)) =
      (toIntegerModel S).base ⁻¹'
        ProjectiveSpectrum.zeroLocus (ProjectiveLine.grading (ULift.{u} ℤ))
          {ProjectiveLine.y (ULift.{u} ℤ)} := sorry

/-- The divisor `D∞ = V(T₀)` on the relative projective line over `S`, with its scheme
structure obtained by pulling back the integral vanishing ideal. -/
noncomputable def infinityDivisor (S : Scheme.{u}) :
    (ProjectiveSpace 1 S).IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal infinityCoordinateLocus).comap (toIntegerModel S)

/-- The support of `infinityDivisor S` is the inverse image of the homogeneous zero locus
`V(T₀)`. -/
theorem infinityDivisor_support (S : Scheme.{u}) :
    ((infinityDivisor S).support : Set (ProjectiveSpace 1 S)) =
      (toIntegerModel S).base ⁻¹'
        ProjectiveSpectrum.zeroLocus (ProjectiveLine.grading (ULift.{u} ℤ))
          {ProjectiveLine.x (ULift.{u} ℤ)} := sorry

end AlgebraicGeometry.ProjectiveLine.Relative
