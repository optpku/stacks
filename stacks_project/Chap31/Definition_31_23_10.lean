/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 31.23.10: Let `X` be a scheme, let `ℒ` be an invertible
`𝒪_X`-module, and let `s` be a regular meromorphic section of `ℒ`. The canonical
ideal whose local sections multiply `s` into regular sections is the ideal
sheaf of denominators of `s`. This construction is defined for every
meromorphic section; regularity gives the properties proved in Lemma 31.23.9. -/
@[stacks 02P1] #check
  (AlgebraicGeometry.Scheme.denominatorIdealSheaf :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℒ : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ),
      Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
