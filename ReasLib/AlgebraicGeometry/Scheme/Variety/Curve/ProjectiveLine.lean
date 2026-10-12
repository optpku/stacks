/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Existence
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper curve over a field, the projective-line condition is equivalent to the
smoothness, integrality, genus, invertible-module degree, cohomology, and closed-point
criteria listed in the characterization theorem. -/
theorem projectiveLine_tfae
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom] :
    let structureModule :=
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)
    let genusZero := Scheme.Hom.cohomologyFinrank X.hom structureModule 1 = 0
    let firstCohomologyVanishes :=
      IsZero (Scheme.Hom.cohomology X.hom structureModule 1)
    let constantGlobalFunctions :=
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)
    let hasOddDegreeInvertibleModule :=
      ∃ m : ℤ, Scheme.Hom.HasInvertibleModuleOfDegree X.hom
        (topologicalKrullDim_eq_one X).le (2 * m + 1)
    let hasDegreeOneInvertibleModule :=
      Scheme.Hom.HasInvertibleModuleOfDegree X.hom
        (topologicalKrullDim_eq_one X).le 1
    let hasNormalClosedPointsOfCoprimeDegrees :=
      ∃ (n : ℕ) (x : Fin n → X.left) (a : Fin n → ℤ),
        (∀ i, x i ∈ closedPoints X.left ∧ X.left.isNormalAt (x i)) ∧
          ∑ i, a i * (Module.finrank k (X.left.residueField (x i)) : ℤ) = 1
    List.TFAE
      [ Nonempty (X ≅ Over.mk (ProjectiveLine.toSpec k)),
        Smooth X.hom ∧ GeometricallyIrreducible X.hom ∧ genusZero ∧
          hasOddDegreeInvertibleModule,
        GeometricallyIntegral X.hom ∧ genusZero ∧ Scheme.Gorenstein X.left ∧
          hasOddDegreeInvertibleModule,
        constantGlobalFunctions ∧ genusZero ∧ Scheme.Gorenstein X.left ∧
          hasOddDegreeInvertibleModule,
        GeometricallyIntegral X.hom ∧ genusZero ∧ hasDegreeOneInvertibleModule,
        constantGlobalFunctions ∧ genusZero ∧ hasDegreeOneInvertibleModule,
        firstCohomologyVanishes ∧ hasDegreeOneInvertibleModule,
        firstCohomologyVanishes ∧ hasNormalClosedPointsOfCoprimeDegrees ] := sorry

/-- A smooth proper genus-zero curve over an algebraically closed field is
isomorphic to the projective line. -/
theorem iso_projectiveLine_of_genus_zero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [IsProper X.hom] [Smooth X.hom]
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0) :
    Nonempty (X ≅ Over.mk (ProjectiveLine.toSpec k)) := sorry

end AlgebraicGeometry.SchemeOverField
