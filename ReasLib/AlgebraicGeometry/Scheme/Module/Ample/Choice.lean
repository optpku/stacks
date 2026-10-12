/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative

/-!
# Witness projections for ample invertible modules

`Scheme.Modules.isAmpleObject` packages the compatible invertibility and
ampleness propositions for a fixed module.  This leaf gives named proof
projections without exposing raw choice terms or any alternate monoidal
structure.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.isAmpleObject

variable {X : Scheme.{u}} {L : X.Modules}

/-- The invertibility witness underlying membership in `isAmpleObject`. -/
theorem invertible (h : Scheme.Modules.isAmpleObject L) :
    Scheme.Modules.Invertible L := sorry

/-- The ampleness witness compatible with `isAmpleObject.invertible h`. -/
theorem isAmple (h : Scheme.Modules.isAmpleObject L) :
    @Scheme.Modules.IsAmple X L (invertible h) := sorry

end AlgebraicGeometry.Scheme.Modules.isAmpleObject
