/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection-Formula Maps on Ringed Spaces

This file specializes the two canonical mates of a monoidal adjunction to derived pullback and
pushforward on ringed spaces. It owns the maps and their fixed-factor natural transformations;
finiteness hypotheses belong in separate files that prove these maps invertible.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.ProjectionFormula

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

/-- The canonical projection-formula mate with the pulled-back factor on the left. -/
noncomputable abbrev mate (K : ModuleDerived Y) (E : ModuleDerived X) :
    (K ⊗ (R(f)_*).obj E) ⟶
      (R(f)_*).obj ((L(f)^*).obj K ⊗ E) :=
  (RingedSpace.modulePullbackDerivedPushforwardAdjunction f).projectionFormulaMate K E

/-- For a fixed target-side factor, the projection-formula mates with that factor on the left
form a natural transformation in the source-side derived module. -/
noncomputable abbrev mateNatTrans (K : ModuleDerived Y) :
    R(f)_* ⋙ MonoidalCategory.tensorLeft K ⟶
      MonoidalCategory.tensorLeft ((L(f)^*).obj K) ⋙ R(f)_* :=
  (RingedSpace.modulePullbackDerivedPushforwardAdjunction f).projectionFormulaMateNatTrans K

/-- The component of `mateNatTrans` is the canonical left-factor projection-formula mate. -/
@[simp]
theorem mateNatTrans_app (K : ModuleDerived Y) (E : ModuleDerived X) :
    (mateNatTrans f K).app E = mate f K E := sorry

/-- 20.54.2.1: the canonical projection-formula mate with the pulled-back factor on the right. -/
@[stacks 0B53]
noncomputable abbrev leftMate (E : ModuleDerived X) (K : ModuleDerived Y) :
    ((R(f)_*).obj E ⊗ K) ⟶
      (R(f)_*).obj (E ⊗ (L(f)^*).obj K) :=
  (RingedSpace.modulePullbackDerivedPushforwardAdjunction f).leftProjectionFormulaMate E K

/-- For a fixed target-side factor, the projection-formula mates with that factor on the right
form a natural transformation in the source-side derived module. -/
noncomputable abbrev leftMateNatTrans (K : ModuleDerived Y) :
    R(f)_* ⋙ MonoidalCategory.tensorRight K ⟶
      MonoidalCategory.tensorRight ((L(f)^*).obj K) ⋙ R(f)_* :=
  (RingedSpace.modulePullbackDerivedPushforwardAdjunction f).leftProjectionFormulaMateNatTrans K

/-- The component of `leftMateNatTrans` is the canonical right-factor projection-formula
mate. -/
@[simp]
theorem leftMateNatTrans_app (E : ModuleDerived X) (K : ModuleDerived Y) :
    (leftMateNatTrans f K).app E = leftMate f E K := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.ProjectionFormula
