/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

/-!
# Lemma 17.11.3

The generic cokernel theorem belongs to `SheafOfModules.IsFinitePresentation`; this file checks
its source-faithful specialization to module sheaves on a ringed space.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable {G F : X.Modules} (f : G ⟶ F)
variable [G.IsFiniteType] [F.IsFinitePresentation]

/- Lemma 17.11.3 (0H96): the cokernel of a morphism from a finite-type module sheaf to a
finitely presented module sheaf is finitely presented. -/
@[stacks 0H96]
#check
  (IsFinitePresentation.cokernel f :
    (cokernel f).IsFinitePresentation)

end SheafOfModules
