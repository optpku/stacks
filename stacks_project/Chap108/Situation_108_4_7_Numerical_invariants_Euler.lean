/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Euler

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Compatibility bridge for the derived numerical pushforward of a coherent family. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.numericalPushforward :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] (x : CohStack.Obj f),
      ModuleDerived X → ModuleDerived (ofOver x.σ.left))

/- The fiberwise Euler-characteristic formula. -/
#check (AlgebraicGeometry.AlgebraicSpace.CohStack.Obj.eulerChar_eq_fibreTensor :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} {f : X ⟶ B}
      [FinitePresentation f] (x : CohStack.Obj f) (E : ModuleDerived X),
      ModuleDerived.IsPerfect E → ∀ (t : FieldValuedPoint (ofOver x.σ.left)),
      x.eulerChar E (Points.mk t) =
        ModuleDerived.fiberEulerChar (x.fibreTensorPushforward E t)
          (Points.mk (FieldValuedPoint.of t.K t.structureHom (𝟙 (ofOver t.overObj)))))
