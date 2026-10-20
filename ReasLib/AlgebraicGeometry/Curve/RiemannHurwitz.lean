module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Separable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Curve.Ramification
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- For a morphism of smooth proper curves inducing a finite separable function-field
extension, with constant global functions and genera `gX` and `gY`, the genus formula is
`2 * gX - 2 = (2 * gY - 2) * deg(f) + deg(R)`, where `R` is the effective Cartier divisor
defined by the Kähler different and its degree is the dimension of its global functions. -/
@[stacks 0C1D]
theorem riemannHurwitz
    {k : Type u} [Field k] (X Y : SchemeOverField k)
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom))
    (gX gY : ℕ)
    (h_genusX : gX = genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓX)
    (h_genusY : gY = genus Y
      (AlgebraicGeometry.topologicalKrullDim_eq_one Y) hΓY) :
    2 * (gX : ℤ) - 2 =
      (2 * (gY : ℤ) - 2) * (f.left.inducedFunctionFieldDegree : ℤ) +
        (Module.finrank k
          (globalSectionsAlg
            (subschemeι (kaehlerDifferent f.left) ≫ X.hom)) : ℤ) := sorry

/-- For a finite separable morphism of smooth proper curves with constant global functions, the
genus correction is the residue-degree-weighted sum of Kähler-different multiplicities. -/
theorem riemannHurwitz_eq_finsum_multiplicity
    {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X] [Curve Y] [IsProper X.hom]
    [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom))
    (gX gY : ℕ)
    (h_genusX : gX = genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓX)
    (h_genusY : gY = genus Y
      (AlgebraicGeometry.topologicalKrullDim_eq_one Y) hΓY) :
    2 * (gX : ℤ) - 2 =
        (2 * (gY : ℤ) - 2) * (f.left.inducedFunctionFieldDegree : ℤ) +
        ∑ᶠ x : closedPoints X.left,
          (kaehlerDifferentMultiplicity f x : ℤ) *
            (X.hom.residueDegree x.1 : ℤ) := sorry

end AlgebraicGeometry.Curve
