/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

/- Lifts of a module morphism and their ideal-valued translations. -/
#check (AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} (F' G' : X'.Modules),
    ((i^*).obj F' ⟶ (i^*).obj G') → Type u)
#check (AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift.perturb :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} {F' G' : X'.Modules}
    {φ : (i^*).obj F' ⟶ (i^*).obj G'} [IsFirstOrderThickening i],
    ((i^*).obj F' ⟶ AlgebraicGeometry.RingedSpace.Hom.idealMulRestrict i G') →
      AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift F' G' φ →
        AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift F' G' φ)
