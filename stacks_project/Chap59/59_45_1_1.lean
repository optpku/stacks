/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Component
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- 59.45.1.1: Descent data relative to S'/S with an étale component over S'
   map to schemes étale over S'. -/
@[stacks 0BTZ] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.componentFunctor :
    ∀ {S' S : Scheme.{u}} (f : S' ⟶ S),
      AlgebraicGeometry.Scheme.DescentData.Etale f ⥤ S'.Etale)

end
