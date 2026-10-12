/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product

/-!
# Numerical genera of proper varieties

This file defines arithmetic genus, geometric genus, and irregularity for varieties over a field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The arithmetic genus of a proper variety is the signed reduced Euler characteristic of its
structure sheaf. -/
noncomputable def arithmeticGenus
    (X : SchemeOverField k) [Variety X] [IsProper X.hom] : ℤ :=
  ((X.dimension : ℤ).negOnePow : ℤ) *
    (Scheme.Hom.eulerCharacteristic X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) - 1)

/-- The arithmetic genus expands as the signed reduced Euler characteristic of the structure
sheaf. -/
theorem arithmeticGenus_def
    (X : SchemeOverField k) [Variety X] [IsProper X.hom] :
    arithmeticGenus X = ((X.dimension : ℤ).negOnePow : ℤ) *
      (Scheme.Hom.eulerCharacteristic X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) - 1) := sorry

/-- The geometric genus of a smooth proper variety is the degree-zero cohomology finrank of its
top exterior power of relative differentials. -/
noncomputable def geometricGenus
    (X : SchemeOverField k) [Variety X] [IsProper X.hom]
    [SmoothOfRelativeDimension X.dimension X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (Λ[X.dimension] Ω[X.hom.toShHom]) 0

/-- The geometric genus expands as the degree-zero cohomology finrank of the top exterior power
of relative differentials. -/
theorem geometricGenus_def
    (X : SchemeOverField k) [Variety X] [IsProper X.hom]
    [SmoothOfRelativeDimension X.dimension X.hom] :
    geometricGenus X = Scheme.Hom.cohomologyFinrank X.hom
      (Λ[X.dimension] Ω[X.hom.toShHom]) 0 := sorry

/-- The irregularity of a proper variety is the degree-one cohomology finrank of its structure
sheaf. -/
noncomputable def irregularity
    (X : SchemeOverField k) [Variety X] [IsProper X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1

/-- The irregularity expands as the degree-one cohomology finrank of the structure sheaf. -/
theorem irregularity_def
    (X : SchemeOverField k) [Variety X] [IsProper X.hom] :
    irregularity X = Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- On a smooth projective geometrically irreducible curve, irregularity agrees with the curve
genus. -/
theorem irregularity_eq_curveGenus
    (X : SchemeOverField k) [Curve X] [Projective X.hom] [Smooth X.hom]
    [GeometricallyIrreducible X.hom] :
    irregularity X = Curve.genus X := sorry

/-- For a smooth proper algebraically closed surface, the geometric genus minus the arithmetic
genus equals the irregularity. -/
theorem surfaceGenusDifference_eq_irregularity
    [IsAlgClosed k]
    (X : SchemeOverField k) [Variety X] [IsProper X.hom]
    [SmoothOfRelativeDimension X.dimension X.hom]
    (h_dimension : X.dimension = 2) :
    (geometricGenus X : ℤ) - arithmeticGenus X = (irregularity X : ℤ) := sorry

/-- For a smooth proper algebraically closed surface, the geometric genus is at least the
arithmetic genus. -/
theorem surfaceGenusDifference_nonnegative
    [IsAlgClosed k]
    (X : SchemeOverField k) [Variety X] [IsProper X.hom]
    [SmoothOfRelativeDimension X.dimension X.hom]
    (h_dimension : X.dimension = 2) :
    0 ≤ (geometricGenus X : ℤ) - arithmeticGenus X := sorry

/-- The irregularity of a product of smooth projective geometrically irreducible curves is the
sum of their genera. -/
theorem irregularity_prod_curves
    [IsAlgClosed k]
    (C₁ C₂ : SchemeOverField k)
    [Curve C₁] [Projective C₁.hom] [Smooth C₁.hom]
    [GeometricallyIrreducible C₁.hom]
    [Curve C₂] [Projective C₂.hom] [Smooth C₂.hom]
    [GeometricallyIrreducible C₂.hom] :
    irregularity (C₁ ⨯ C₂) = Curve.genus C₁ + Curve.genus C₂ := sorry

/-- The genus of a proper one-dimensional scheme over a field whose global functions are
exactly that field equals the degree-zero cohomology finrank of its dualizing module. -/
theorem genus_eq_dualizingModule_finrank
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    genus X h_dimension hΓ = Scheme.Hom.cohomologyFinrank X.hom
      (Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule X.hom) 0 := sorry

end AlgebraicGeometry.SchemeOverField
