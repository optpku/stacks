/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.StandardDerived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import Mathlib.CategoryTheory.Shift.Localization

/-! # Explicit shift comparisons for the actual property-P derived model
The shift payload comes from the actual shifted augmentation and its formal denominator edge,
then the actual property-P augmentation and the supplied strict homotopy shift maps of H.
-/
@[expose] public section
noncomputable section
universe r v u w
open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory
namespace DifferentialGradedModule.PropertyP.StandardDerivedShift
variable {R : Type r} [CommRing R] {A : CochainDGAlgebra.{r, v} R}
variable {C : Type u} [Category.{w} C] [Abelian C]
local instance standardTarget : HasDerivedCategory.{max u w} C := HasDerivedCategory.standard C
variable (H : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A) ⥤
  HomotopyCategory C (ComplexShape.up ℤ)) [H.CommShift ℤ]

/-- The shifted resolving object still has its shifted property-P filtration. -/
theorem shiftedReplacement_propertyP
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) (n : ℤ) :
    HasPropertyP A
      ((shiftFunctor (DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) n).obj
        ((homotopyReplacement A).obj X)).obj := sorry

/-- Shift the actual augmentation; this is the arrow PX[n] → X[n]. -/
def shiftedAugmentation
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) (n : ℤ) :=
  (shiftFunctor (DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) n).map
    ((homotopyAugmentation A).app X)

/-- Its membership certifies the specified arrow and selects no inverse. -/
theorem shiftedAugmentation_mem_trW
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) (n : ℤ) :
    (DifferentialGradedModule.Homotopy.acyclic.{r, v} A).trW
      (shiftedAugmentation X n) := sorry

/-- P(X[n]) ← P(PX[n]) → PX[n], followed by the actual H-shift comparison.
The first reverse map is the image of the literal source denominator reverse edge. -/
def computedShiftIsoApp
    (X : DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) (n : ℤ) :
    (StandardDerived.computed H).obj
        ((shiftFunctor (DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) n).obj X) ≅
      ((StandardDerived.computed H).obj X)⟦n⟧ :=
  ((StandardDerived.computationIso H).app
      ((shiftFunctor (DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) n).obj X)).symm ≪≫
    (StandardDerived.functor H).mapIso
      (Localization.Construction.wIso (shiftedAugmentation X n)
        (shiftedAugmentation_mem_trW X n)).symm ≪≫
    StandardDerived.counitAppIso H
      (((shiftFunctor (DifferentialGradedCategory.K R (DifferentialGradedModule.{r, v} A)) n).obj
        ((homotopyReplacement A).obj X)).obj)
      (shiftedReplacement_propertyP X n) ≪≫
    (DerivedCategory.Qh).mapIso ((H.commShiftIso n).app ((homotopyReplacement A).obj X)) ≪≫
    (DerivedCategory.Qh.commShiftIso n).app (H.obj ((homotopyReplacement A).obj X))

/-- The comparison on standard derived objects, using the canonical localization shift bridge. -/
def derivedShiftIsoApp (X : DifferentialGradedModule.Derived.Category.{r, v} A) (n : ℤ) :
    (StandardDerived.functor H).obj (X⟦n⟧) ≅ ((StandardDerived.functor H).obj X)⟦n⟧ :=
  (StandardDerived.functor H).mapIso
      (((DifferentialGradedModule.Derived.Q A).commShiftIso n).app X.as.obj).symm ≪≫
    (StandardDerived.computationIso H).app (X.as.obj⟦n⟧) ≪≫
    computedShiftIsoApp H X.as.obj n ≪≫
    (shiftFunctor (DerivedCategory C) n).mapIso ((StandardDerived.computationIso H).app X.as.obj).symm

/-- Both natural transformation components are the specified zigzag arrows. -/
def derivedShiftIso (n : ℤ) :
    shiftFunctor (DifferentialGradedModule.Derived.Category.{r, v} A) n ⋙ StandardDerived.functor H ≅
      StandardDerived.functor H ⋙ shiftFunctor (DerivedCategory C) n :=
  NatIso.ofComponents (fun X ↦ derivedShiftIsoApp H X n) (by intro X Y f; sorry)

/-- The explicit zigzag reduces to the canonical zero-shift comparison. -/
theorem derivedShiftIso_zero : derivedShiftIso H 0 =
    Functor.CommShift.isoZero (StandardDerived.functor H) ℤ := sorry

/-- Canonical augmentation comparisons give coherence for addition of all integer shifts. -/
theorem derivedShiftIso_add (i j : ℤ) : derivedShiftIso H (i + j) =
    Functor.CommShift.isoAdd (derivedShiftIso H i) (derivedShiftIso H j) := sorry

/-- Shift data, with maps supplied above and only the coherence laws left as proofs. -/
def commShift : (StandardDerived.functor H).CommShift ℤ where
  commShiftIso := derivedShiftIso H
  commShiftIso_zero := derivedShiftIso_zero H
  commShiftIso_add := derivedShiftIso_add H

end DifferentialGradedModule.PropertyP.StandardDerivedShift
