/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Total

/-!
# Total relative Chow groups

This file assembles relative Chow groups in all integer degrees, together with the quotient
from total cycles and proper pushforward.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Total relative Chow homology, graded by relative dimension over a dimensioned base. -/
abbrev Total {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] : Type u :=
  DirectSum ℤ (fun d ↦
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance d)

/-- The total Chow carrier is the direct sum of its relative-dimension pieces. -/
theorem total_def {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    Total delta X = DirectSum ℤ (fun d ↦
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance d) := sorry

namespace Total

/-- The degreewise quotient map from total relative cycles to total relative Chow homology. -/
noncomputable def chowClass {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    CycleGroup.Total delta X →+ ChowGroup.Total delta X :=
  DirectSum.map fun d ↦
    @AlgebraicGeometry.chowClass X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance d

/-- Every total relative Chow class is represented by a total relative cycle. -/
theorem chowClass_surjective {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] :
    Function.Surjective (chowClass delta X) := sorry

/-- Degreewise proper pushforward on total relative Chow homology. -/
noncomputable def map {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] : ChowGroup.Total delta X →+ ChowGroup.Total delta Y :=
  DirectSum.map fun d ↦ ChowGroup.map delta X Y f d

/-- Total Chow pushforward acts degreewise on homogeneous Chow classes. -/
theorem map_of {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (d : ℤ)
    (a : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance d) :
    map delta f (DirectSum.of _ d a) =
      DirectSum.of _ d (ChowGroup.map delta X Y f d a) := sorry

/-- Total proper pushforward commutes with passage from cycles to Chow classes. -/
theorem map_chowClass {S : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (a : CycleGroup.Total delta X) :
    map delta f (chowClass delta X a) =
      chowClass delta Y (CycleGroup.Total.map delta f a) := sorry

end Total

end AlgebraicGeometry.ChowGroup
