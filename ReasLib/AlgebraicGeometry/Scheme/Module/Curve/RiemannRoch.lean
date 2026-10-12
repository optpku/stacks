/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IntegerDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.Topology.KrullDimension.Equidimensional

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme Scheme.Hom Scheme.Modules
open Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The curve dualizing module of a proper Gorenstein equidimensional curve is invertible. -/
instance instCurveDualizingModuleInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
    [Fact (topologicalKrullDim X.left = 1)] :
    Scheme.Modules.Invertible (curveDualizingModule X.hom) := sorry

/-- The degree of the curve dualizing module is `-2` times the Euler characteristic of the
structure sheaf. -/
theorem curveDualizingModuleDegree
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
    [h_dimension : Fact (topologicalKrullDim X.left = 1)] :
    curveDegreeOfInvertible X.hom h_dimension.out.le
        (curveDualizingModule X.hom) =
      -2 * eulerCharacteristic X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) := sorry

/-- The Riemann–Roch formula for a finite locally free module of constant rank on a proper
Gorenstein equidimensional curve. -/
theorem riemannRoch
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
    [h_dimension : Fact (topologicalKrullDim X.left = 1)]
    (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n] :
    (eulerCharacteristic X.hom E : ℚ) =
      (curveDegree X.hom h_dimension.out.le E n : ℚ) -
        (n : ℚ) *
          (curveDegreeOfInvertible X.hom h_dimension.out.le
            (curveDualizingModule X.hom) : ℚ) / 2 := sorry

/-- Serre duality identifies the cohomology finranks in complementary integer degrees for a
finite locally free module on a proper Gorenstein equidimensional curve. -/
theorem serreDualityFinrank
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
    [Fact (topologicalKrullDim X.left = 1)]
    (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n] (i : ℤ) :
    Scheme.Hom.cohomologyFinrankInt X.hom E i =
      Scheme.Hom.cohomologyFinrankInt X.hom
        (Scheme.Modules.dual E ⊗ curveDualizingModule X.hom) (1 - i) := sorry

/-- The degree of the curve dualizing module of a proper one-dimensional Gorenstein scheme
over a field whose global functions are exactly that field is twice its genus minus two. -/
theorem curveDualizingModuleDegree_eq_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Scheme.Gorenstein X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) :
    -- Local instance justification (defeq pin): the dependent degree expression requires the
    -- invertibility instance using equidimensionality derived from the explicit dimension
    -- and global-functions hypotheses, without adding an independent assumption.
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension hΓ
    -- Local instance justification (defeq pin): the dependent degree expression requires the
    -- invertibility instance using the canonical Fact wrapper of the explicit dimension equality.
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le
        (curveDualizingModule X.hom) =
      2 * (genus X h_dimension hΓ : ℤ) - 2 := sorry

end AlgebraicGeometry.SchemeOverField
