/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.Fppf
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.JacobsonSpace

/- Lemma 35.16.2: the property of a scheme being Jacobson is local for the fppf
precoverage. -/
@[stacks 0368] #check
  (AlgebraicGeometry.Scheme.JacobsonSpace.isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.fppfPrecoverage)

end AlgebraicGeometry.Scheme.JacobsonSpace
