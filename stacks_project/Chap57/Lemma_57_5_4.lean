/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Ext.BoundedCoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open DerivedCategory.Bounded
open DerivedCategory.TStructure
open scoped DerivedExt DerivedCategory.CohomologyIn

/- Lemma 57.5.4 -/
@[stacks 0FYD] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.boundedCoherent_iff_finiteTotalExt :
    ∀ {k : Type} [Field k] {X : Scheme}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (K : Scheme.DerivedQCoh X),
      (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K.obj ∧
        (t.bounded : ObjectProperty
          (RingedSpace.ModuleDerived X.toRingedSpace)) K.obj) ↔
        ∀ E : RingedSpace.ModuleDerived X.toRingedSpace,
          RingedSpace.ModuleDerived.IsPerfect E →
            GradedObject.FiniteTotalDimension
              (fun i : ℤ ↦ DerivedExt.value f E K.obj i))

end
