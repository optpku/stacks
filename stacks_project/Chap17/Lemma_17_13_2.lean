/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 17.13.2 (01C3): the pushforward of a quasicoherent module sheaf along a closed
immersion is locally a cokernel of a morphism between quasicoherent module sheaves. -/
@[stacks 01C3]
#check @RingedSpace.IsClosedImmersion.pushforward_mem_localCokernels

/- The reusable target is an isomorphism-invariant `ObjectProperty`, not a chapter-specific
standalone proposition. -/
#check @SheafOfModules.RingedSite.localCokernels.quasicoherent
