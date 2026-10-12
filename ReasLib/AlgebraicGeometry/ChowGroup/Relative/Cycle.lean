/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeChow

/-- The degree-`k` relative Chow class represented by the fundamental cycle of `Y`. -/
noncomputable def fundamentalClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (Y : Over S) [LocallyOfFiniteType Y.hom] (k : ℤ) : RelativeChow δ Y k :=
  @chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
    (Y.hom.relativeDimensionFunction δ) inferInstance k
    (@CycleGroup.fundamental Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) k)

/-- The degree-`k` relative Chow class represented by the associated cycle of a closed subscheme. -/
noncomputable def closedSubschemeClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (Y : Over S) [LocallyOfFiniteType Y.hom] (Z : Y.left.IdealSheafData) (k : ℤ) :
    RelativeChow δ Y k :=
  @chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
    (Y.hom.relativeDimensionFunction δ) inferInstance k
    (@Scheme.IdealSheafData.associatedCycle Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom) Z
      (Y.hom.relativeDimensionFunction δ) k)

end AlgebraicGeometry.RelativeChow
