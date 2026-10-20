/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.Trace

@[expose] public section

open Polynomial

universe u

#check (PurelyInseparableTrace.trace :
  ∀ (p : ℕ) (_ : p.Prime) (R : Type u) [CommRing R] [Algebra (ZMod p) R] (a : R),
    KaehlerDifferential R (AdjoinRoot (X ^ p - C a)) →ₗ[R]
      KaehlerDifferential (ZMod p) R)
