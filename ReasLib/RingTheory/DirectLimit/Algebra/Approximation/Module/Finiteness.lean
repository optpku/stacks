/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.FiniteType.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module finiteness of directed approximations

This leaf contains the finiteness consequences for the stage modules of a
finite-type approximation.  The finite-to-finite-presentation bridge uses the
Noetherian target-stage theorem from `FiniteType.Finiteness`; it is not an
assertion about finite modules over arbitrary rings.
-/

@[expose] public section

universe u v x

namespace Ring.DirectLimit.Algebra.Approximation.Module

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- The finite-module field attached to one approximation stage. -/
@[stacks 00R1 "finite module approximation finiteness"]
theorem stageModule_finite (A : Module f M) (i : A.index) :
    _root_.Module.Finite (A.target i) (A.moduleStage i) := A.moduleStage_finite i

/-- Every finite stage module is finitely presented over its target stage.
This upgrade uses the Noetherian target-stage consequence of the finite-type
ring approximation. -/
@[stacks 00R1 "finite module approximation finiteness"]
theorem stageModule_finitePresentation (A : Module f M) (i : A.index) :
    _root_.Module.FinitePresentation (A.target i) (A.moduleStage i) := sorry

/-- The finite-presentation facts for the ring map and module at one stage. -/
@[stacks 00R1 "finite module approximation finiteness"]
theorem stage_finitePresentation (A : Module f M) (i : A.index) :
    (A.map i).FinitePresentation ∧
      _root_.Module.FinitePresentation (A.target i) (A.moduleStage i) := sorry

end Ring.DirectLimit.Algebra.Approximation.Module
