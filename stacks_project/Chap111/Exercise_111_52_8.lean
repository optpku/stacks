/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GluedCrossedAxes.Components
public import ReasLib.AlgebraicGeometry.GluedCrossedAxes.Cohomology
import StacksCheckRecall

/-!
# Exercise 111.52.8

The scheme obtained by gluing two affine crossed axes through coordinate inversion
is separated and of finite type over `k`. Its structure sheaf has one-dimensional
`H¹`, and it is the union of two projective lines meeting at two rational points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GluedCrossedAxes
open scoped AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/- Exercise 111.52.8 (1): the glued scheme is separated over `k`. -/
@[stacks 02B3] #check (AlgebraicGeometry.GluedCrossedAxes.toBase_isSeparated k :
  IsSeparated (toBase k))

/- Exercise 111.52.8 (2): the glued scheme is of finite type over `k`. -/
@[stacks 02B3] #check (AlgebraicGeometry.GluedCrossedAxes.toBase_finiteType k :
  Scheme.Hom.FiniteType (toBase k))

/- Exercise 111.52.8 (3): the structure sheaf has degree-one cohomology of dimension one. -/
@[stacks 02B3] #check (AlgebraicGeometry.GluedCrossedAxes.structureSheaf_cohomologyFinrank_one k :
  Scheme.Hom.cohomologyFinrank (toBase k)
    (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 1 = 1)

#check (AlgebraicGeometry.GluedCrossedAxes.finiteDimensional_structureSheaf_cohomology_one k :
  FiniteDimensional k (Scheme.Hom.cohomology (toBase k)
    (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) 1))

/- Exercise 111.52.8 (4): two closed projective lines cover the scheme and meet at zero and infinity. -/
@[stacks 02B3] #check (AlgebraicGeometry.GluedCrossedAxes.isUnionOfTwoProjectiveLines k :
  Function.Surjective (coprod.desc (firstComponent k) (secondComponent k)).base)

#check (AlgebraicGeometry.GluedCrossedAxes.firstComponent_isClosedImmersion k :
  IsClosedImmersion (firstComponent k))

#check (AlgebraicGeometry.GluedCrossedAxes.secondComponent_isClosedImmersion k :
  IsClosedImmersion (secondComponent k))

#check (AlgebraicGeometry.GluedCrossedAxes.firstComponent_comp_zeroSection k :
  ProjectiveLine.zeroSection k ≫ firstComponent k = originASection k)

#check (AlgebraicGeometry.GluedCrossedAxes.secondComponent_comp_zeroSection k :
  ProjectiveLine.zeroSection k ≫ secondComponent k = originASection k)

#check (AlgebraicGeometry.GluedCrossedAxes.firstComponent_comp_infinitySection k :
  ProjectiveLine.infinitySection k ≫ firstComponent k = originBSection k)

#check (AlgebraicGeometry.GluedCrossedAxes.secondComponent_comp_infinitySection k :
  ProjectiveLine.infinitySection k ≫ secondComponent k = originBSection k)

#check (AlgebraicGeometry.GluedCrossedAxes.originA_ne_originB k : originA k ≠ originB k)

#check (AlgebraicGeometry.GluedCrossedAxes.componentsPullbackIso k :
  pullback (firstComponent k) (secondComponent k) ≅ Spec (.of k) ⨿ Spec (.of k))
