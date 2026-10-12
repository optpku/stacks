/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Integral
import StacksCheckRecall

universe u

/- Lemma 31.32.9: the blowup of an integral scheme in a nonzero quasi-coherent ideal sheaf is
integral. -/
@[stacks 02ND] #check (AlgebraicGeometry.Blowup.isIntegral :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) [AlgebraicGeometry.IsIntegral X],
      I ≠ 0 → AlgebraicGeometry.IsIntegral π.scheme)
