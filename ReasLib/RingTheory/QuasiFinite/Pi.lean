module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-Finite Finite Products

@stack 034Z

This leaf owns the finite-product closure property for Mathlib's fiberwise
notion `Algebra.QuasiFinite`.
-/

universe u v w

namespace Algebra.QuasiFinite

/-- A finite dependent product of quasi-finite commutative algebras is
quasi-finite over the common base. -/
@[stacks 034Z "finite product of quasi-finite algebras"]
theorem pi
    {R : Type u} {ι : Type v} {A : ι -> Type w} [CommRing R] [Finite ι]
    [forall i, CommRing (A i)] [forall i, Algebra R (A i)]
    [forall i, Algebra.QuasiFinite R (A i)] :
    Algebra.QuasiFinite R (forall i, A i) := sorry

end Algebra.QuasiFinite
