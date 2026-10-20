/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Dualizable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.LocallyFree
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for perfect complexes on ringed spaces

The ringed-space projection formula is the categorical projection formula for the canonical
derived pullback-pushforward adjunction.  Its proof-facing local models do not appear in the
public statement.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X Y : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [KFlat.HomotopyTensorDescends Y] [KFlat.TensorDescends Y]
variable [KFlat.IsLocalization Y]
variable (f : X ⟶ Y)
variable [RingedSite.Hom.DerivedAdjunction.HasPair (opensRingedSiteHom f)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Functor.Monoidal (L(f)^*)]

/-- The projection-formula mate for a morphism of ringed spaces is an isomorphism when its
target-side tensor factor is perfect. -/
theorem IsPerfect.isIso_mate
    {K : ModuleDerived Y} (hK : IsPerfect K) (E : ModuleDerived X) :
    IsIso (ProjectionFormula.mate f K E) := sorry

/-- At a fixed perfect target-side factor, the projection-formula mates form an invertible
natural transformation in the source-side derived module. -/
theorem IsPerfect.isIso_mateNatTrans
    {K : ModuleDerived Y} (hK : IsPerfect K) :
    IsIso (ProjectionFormula.mateNatTrans f K) := sorry

/-- The functorial projection-formula isomorphism associated to a perfect target-side factor. -/
noncomputable def IsPerfect.projectionFormulaNatIso
    {K : ModuleDerived Y} (hK : IsPerfect K) :
    R(f)_* ⋙ MonoidalCategory.tensorLeft K ≅
      MonoidalCategory.tensorLeft ((L(f)^*).obj K) ⋙ R(f)_* :=
  @asIso _ _ _ _ (ProjectionFormula.mateNatTrans f K) (hK.isIso_mateNatTrans f)

/-- The left-oriented projection-formula mate for a morphism of ringed spaces is an isomorphism
when its target-side tensor factor is perfect. -/
@[stacks 0B54]
theorem IsPerfect.isIso_leftMate
    {K : ModuleDerived Y} (hK : IsPerfect K) (E : ModuleDerived X) :
    IsIso (ProjectionFormula.leftMate f E K) := sorry

/-- At a fixed perfect target-side factor, the left projection-formula mates form an invertible
natural transformation in the source-side derived module. -/
theorem IsPerfect.isIso_leftMateNatTrans
    {K : ModuleDerived Y} (hK : IsPerfect K) :
    IsIso (ProjectionFormula.leftMateNatTrans f K) := sorry

/-- The functorial left projection-formula isomorphism associated to a perfect target-side
factor. -/
noncomputable def IsPerfect.leftProjectionFormulaNatIso
    {K : ModuleDerived Y} (hK : IsPerfect K) :
    R(f)_* ⋙ MonoidalCategory.tensorRight K ≅
      MonoidalCategory.tensorRight ((L(f)^*).obj K) ⋙ R(f)_* :=
  @asIso _ _ _ _ (ProjectionFormula.leftMateNatTrans f K)
    (hK.isIso_leftMateNatTrans f)

end AlgebraicGeometry.RingedSpace.ModuleDerived

namespace SheafOfModules.IsFiniteLocallyFree

variable {X Y : AlgebraicGeometry.RingedSpace.{u}}
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X]
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends X]
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization X]
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y]
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends Y]
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization Y]
variable (f : X ⟶ Y)
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (AlgebraicGeometry.RingedSpace.opensRingedSiteHom f)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [CategoryTheory.Functor.Monoidal (L(f)^*)]

/-- The canonical projection-formula natural transformation at a finite locally free module
placed in degree zero is invertible. -/
theorem isIso_mateNatTrans (E : Y.Modules) [E.IsFiniteLocallyFree] :
    IsIso
      (AlgebraicGeometry.RingedSpace.ModuleDerived.ProjectionFormula.mateNatTrans f
        ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj E)) := sorry

/-- A finite locally free module placed in degree zero gives a functorial projection-formula
isomorphism on derived modules. -/
@[stacks 01E8 "(2), functorial derived isomorphism"]
noncomputable def projectionFormulaNatIso (E : Y.Modules) [E.IsFiniteLocallyFree] :
    R(f)_* ⋙ MonoidalCategory.tensorLeft
        ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj E) ≅
      MonoidalCategory.tensorLeft
          ((L(f)^*).obj ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj E)) ⋙
        R(f)_* :=
  @asIso _ _ _ _
    (AlgebraicGeometry.RingedSpace.ModuleDerived.ProjectionFormula.mateNatTrans f
      ((DerivedCategory.singleFunctor Y.Modules (0 : ℤ)).obj E))
    (isIso_mateNatTrans f E)

end SheafOfModules.IsFiniteLocallyFree
