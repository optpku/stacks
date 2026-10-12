/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Fppf
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.16.1: local Noetherianity of schemes is local for the fppf precoverage. -/
@[stacks 034C] #check
  (AlgebraicGeometry.IsLocallyNoetherian.isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.IsLocallyNoetherian :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
