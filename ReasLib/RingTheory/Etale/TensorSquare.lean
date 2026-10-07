module

public import Mathlib.RingTheory.Smooth.Fiber
public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.Etale.Weakly.FinitePresentation
public import ReasLib.RingTheory.Unramified.TensorSquare.FiniteType
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale criteria from tensor-square multiplication

This leaf records the finite-presentation consequence of the flat diagonal
criterion.  The formal-unramified and finite-type unramified statements remain in
their respective `Unramified` owner leaves.

@stack 0CKP
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A flat finitely presented algebra with flat tensor-square multiplication is etale. -/
@[stacks 0CKP "flat diagonal criterion for etaleness"]
theorem of_tensorSquareMul_flat [Algebra.FinitePresentation A B] [Module.Flat A B]
    (hflat : (Algebra.tensorSquareMultiplication A B).Flat) :
    Algebra.Etale A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflat
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Algebra.Etale
