/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Abelian

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- The inclusion of coherent modules into quasi-coherent modules. -/
abbrev Coh.qCohLift : Coh X ⥤ QCoh X :=
  Coh.toQCoh

end AlgebraicGeometry.AlgebraicStack
