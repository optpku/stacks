/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech

@[expose] public section

/- Item 20.11.0.2 reuses the Chapter 20 owners from `20_11_0_1`.
It is only a bridge import in the chapter sequence and intentionally keeps no parallel local
copies of `moduleUnderlyingSheaf`, `moduleUnderlyingPresheaf`, or `moduleCechCohomology`. -/
