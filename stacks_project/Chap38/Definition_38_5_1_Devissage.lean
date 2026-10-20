/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver :
  {S X : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) →
    [LocallyOfFiniteType f] → [F.IsQuasicoherent] → [F.IsFiniteType] →
      (s : S) → Type (u + 1))
