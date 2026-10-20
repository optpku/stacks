/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage
import StacksCheckRecall

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Definition 38.4.1: A one-step dévissage of a finite-type quasicoherent
module over a point of the base scheme. -/
@[stacks 05H4] #check (AlgebraicGeometry.Scheme.Modules.OneStepDevissage :
  {S : Scheme.{u}} → (X : CategoryTheory.Over S) → (F : X.left.Modules) →
    [LocallyOfFiniteType X.hom] → [F.IsQuasicoherent] → [F.IsFiniteType] →
    (s : S) → Type (u + 1))

end AlgebraicGeometry.Scheme.Modules
