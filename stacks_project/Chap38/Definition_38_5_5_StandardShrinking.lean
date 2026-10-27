/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.StandardShrinking

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The support-point specialization, including rank and comparison-map restriction
compatibility at every stage, remains available at its historical import path. -/
#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt.StandardShrinking :
  {S X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      {x : X} → AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt f F x →
        Type (u + 1))

#check AlgebraicGeometry.Scheme.Modules.CompleteDevissageAt.StandardShrinking.restriction_spec
