/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Terms
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineSheafDegreeBridges
export AlgebraicGeometry.Scheme.Modules.DeRham (baseFunctor tensorStructureIso degreeZero degreeOne baseDegreeZero baseDegreeOne)
end CrystallineSheafDegreeBridges
variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (M : Y.Modules)
#check (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeZero f M :
  AlgebraicGeometry.Scheme.Modules.DeRham.baseTerm f M 0 ≅ AlgebraicGeometry.Scheme.Modules.DeRham.asBaseSheaf f M)
