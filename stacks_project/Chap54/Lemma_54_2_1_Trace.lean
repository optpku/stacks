module

public import ReasLib.FieldTheory.PurelyInseparable.Trace

@[expose] public section

open Polynomial

universe u

#check (PurelyInseparableTrace.trace :
  ∀ (p : ℕ) (_ : p.Prime) (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R),
    KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) →ₗ[R]
      KaehlerDifferential (ZMod p) R)
