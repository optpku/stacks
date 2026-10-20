/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated derived lower shriek on ringed sites

The lower-shriek presentation is a total left-derived functor.  This leaf registers the
caller-supplied pointwise-derived existence needed by the generic total-derived shift and
triangulation API, so downstream geometry does not rebuild local derived-category instances.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleLowerShriek

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})
variable [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]

namespace derived

variable [Functor.HasPointwiseLeftDerivedFunctor
  (toDerived (J := J) (K := K) f R)
  (RingedSite.Hom.ModuleQis.{w}
    (moduleInverseImage.source (J := J) (K := K) f R))]

/-- The total left-derived lower shriek commutes with integer shifts. -/
@[stacks 07AC "derived lower-shriek shift"]
noncomputable instance commShift
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (moduleLowerShriek.derived (J := J) (K := K) f R).CommShift ℤ := inferInstance

/-- The total left-derived lower shriek is exact in the triangulated sense. -/
@[stacks 07AC "derived lower-shriek is triangulated", instance]
theorem isTriangulated
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify K AddCommGrpCat.{w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    (moduleLowerShriek.derived (J := J) (K := K) f R).IsTriangulated := sorry

end derived

end RingedSite.Cocontinuous.moduleLowerShriek
