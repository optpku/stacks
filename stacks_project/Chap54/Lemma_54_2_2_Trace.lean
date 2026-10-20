/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.HigherTrace

open Polynomial
universe u

#check (PurelyInseparableTrace.Higher.traceOfEquiv :
  ∀ (p : ℕ) (hp : p.Prime) {Λ R : Type u} [CommRing Λ] [CommRing R]
    [Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
    [IsScalarTower (ZMod p) Λ R] [Nontrivial R]
    (a : R) {S : Type u} [CommRing S] [Algebra R S] [Algebra Λ S]
    [IsScalarTower Λ R S] (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)) (n : ℕ),
    RestrictScalars R S (KaehlerDifferential.DeRham.Form Λ S n) →ₗ[R]
      KaehlerDifferential.DeRham.Form Λ R n)
