/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation
public import stacks_project.Chap98.Definition_98_9_1_Hom

/-! # Approximation of complete local objects -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver.FormalObject

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}

/-- Approximation by positive maximal-adic restriction systems. -/
noncomputable abbrev approximation : CompleteLocalObject X ⥤ FormalObject X :=
  GroupoidsOver.approximation X

#check (AlgebraicGeometry.GroupoidsOver.approximation :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S),
    CompleteLocalObject X ⥤ FormalObject X)

end AlgebraicGeometry.GroupoidsOver.FormalObject
