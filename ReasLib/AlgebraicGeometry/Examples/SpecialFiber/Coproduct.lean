/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.Examples.SpecialFiber.Hypersurface

/-!
# A non-flat family with projective special fibre over the complex affine line

The coproduct of `ℙ¹` over `D(T)` with a copy of `ℙ²_C` supported at the origin.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.NonflatProjectiveFiber

/-- The affine line `A^1_C`. -/
abbrev base : Scheme :=
  SplitConicOverLine.base

/-- The origin of `Spec (Polynomial ℂ)`. -/
abbrev origin : base :=
  SplitConicOverLine.origin

/-- The basic open `D(T) ⊆ Spec (Polynomial ℂ)`. -/
abbrev punctured : base.Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℂ)

/-- `punctured` is the standard basic open of the coordinate `T`. -/
theorem punctured_eq :
    punctured = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ℂ) :=
  sorry

/-- The total space `ℙ¹_{D(T)} ⨿ ℙ²_C`. -/
abbrev total : Scheme :=
  ProjectiveSpace 1 punctured.toScheme ⨿ ProjectiveSpace.scheme ℂ 2

/-- The morphism sending `ℙ¹` over `D(T)` into the affine line along the open immersion, and
sending `ℙ²_C` to the origin. -/
def hom : total ⟶ base :=
  coprod.desc (ProjectiveSpace.toBase 1 punctured.toScheme ≫ punctured.ι)
    (ProjectiveSpace.toSpec ℂ 2 ≫ SplitConicOverLine.originHom)

/-- `hom` is the coproduct of the relative `ℙ¹` structure map and the origin-supported `ℙ²`. -/
theorem hom_spec :
    hom =
      coprod.desc (ProjectiveSpace.toBase 1 punctured.toScheme ≫ punctured.ι)
        (ProjectiveSpace.toSpec ℂ 2 ≫ SplitConicOverLine.originHom) :=
  sorry

/-- The scheme-theoretic special fibre of `hom` over the origin. -/
abbrev specialFiber : Scheme :=
  hom.fiber origin

/-- `specialFiber` is the scheme-theoretic fibre of `hom` at `origin`. -/
theorem specialFiber_eq :
    specialFiber = hom.fiber origin :=
  sorry

/-- The fibre of `hom` over a closed point other than the origin is the projective line. -/
theorem fiber_iso_projectiveLine (t : base) (ht : t ∈ closedPoints base) (ht0 : t ≠ origin) :
    Nonempty (hom.fiber t ≅ ProjectiveLine.scheme ℂ) :=
  sorry

/-- The special fibre of `hom` is not the projective line. -/
theorem specialFiber_not_iso_projectiveLine :
    ¬ Nonempty (specialFiber ≅ ProjectiveLine.scheme ℂ) :=
  sorry

/-- The special fibre of `hom` is an integral scheme. -/
instance specialFiber_isIntegral : IsIntegral specialFiber :=
  sorry

/-- The special fibre of `hom` is irreducible. -/
instance specialFiber_irreducibleSpace : IrreducibleSpace specialFiber :=
  sorry

/-- The special fibre of `hom` is projective over the residue field of the origin. -/
instance specialFiber_projective :
    Projective (hom.fiberToSpecResidueField origin) :=
  sorry

/-- The special fibre of `hom` is integral and projective. -/
theorem specialFiber_integral_projective :
    IsIntegral specialFiber ∧ Projective (hom.fiberToSpecResidueField origin) :=
  sorry

/-- The special fibre of `hom` is smooth over the residue field of the origin. -/
instance specialFiber_smooth :
    Smooth (hom.fiberToSpecResidueField origin) :=
  sorry

/-- The special fibre of `hom` is smooth and projective. -/
theorem specialFiber_smooth_projective :
    Smooth (hom.fiberToSpecResidueField origin) ∧
      Projective (hom.fiberToSpecResidueField origin) :=
  sorry

end AlgebraicGeometry.NonflatProjectiveFiber
