/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Trace.Projective

@[expose] public section

noncomputable section

universe u v

namespace Algebra

/-- The finite-projective algebra trace, retained under its Chapter-facing name. -/
abbrev finiteProjectiveTrace (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S] : S →ₗ[R] R :=
  Algebra.FiniteProjective.trace R S

end Algebra
