/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IntegerDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme Scheme.Hom Scheme.Modules
open Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped MonoidalCategory

universe u

/- Lemma 53.5.2 (Riemann-Roch) (1): the curve dualizing module is invertible. -/
@[stacks 0BS6] #check (AlgebraicGeometry.SchemeOverField.instCurveDualizingModuleInvertible :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
      [Fact (topologicalKrullDim X.left = 1)],
      Scheme.Modules.Invertible (curveDualizingModule X.hom))

/- Lemma 53.5.2 (Riemann-Roch) (2): the degree of the curve dualizing module is `-2` times the
Euler characteristic of the structure sheaf. -/
@[stacks 0BS6] #check (AlgebraicGeometry.SchemeOverField.curveDualizingModuleDegree :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
      [h_dimension : Fact (topologicalKrullDim X.left = 1)],
      curveDegreeOfInvertible X.hom h_dimension.out.le (curveDualizingModule X.hom) =
        -2 * eulerCharacteristic X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules))

/- Lemma 53.5.2 (Riemann-Roch) (3): the Riemann–Roch formula for a finite locally free module
of constant rank. -/
@[stacks 0BS6] #check (AlgebraicGeometry.SchemeOverField.riemannRoch :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
      [h_dimension : Fact (topologicalKrullDim X.left = 1)]
      (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n],
      (eulerCharacteristic X.hom E : ℚ) =
        (curveDegree X.hom h_dimension.out.le E n : ℚ) -
          (n : ℚ) *
            (curveDegreeOfInvertible X.hom h_dimension.out.le
              (curveDualizingModule X.hom) : ℚ) / 2)

/- Lemma 53.5.2 (Riemann-Roch) (4): cohomology finranks agree in complementary integer degrees. -/
@[stacks 0BS6] #check (AlgebraicGeometry.SchemeOverField.serreDualityFinrank :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left] [EquidimensionalSpace X.left]
      [Fact (topologicalKrullDim X.left = 1)]
      (E : X.left.Modules) (n : ℕ) [E.IsFiniteLocallyFreeOfRank n] (i : ℤ),
      Scheme.Hom.cohomologyFinrankInt X.hom E i =
        Scheme.Hom.cohomologyFinrankInt X.hom
          (Scheme.Modules.dual E ⊗ curveDualizingModule X.hom) (1 - i))
