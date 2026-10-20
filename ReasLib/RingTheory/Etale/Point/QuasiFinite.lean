/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Point
public import ReasLib.RingTheory.QuasiFinite.Decomposition

@[expose] public section

/-!
# Quasi-finite decompositions after a pointed etale extension

@stack 00UL

This leaf combines a pointed etale extension with the neutral quasi-finite
decomposition of a tensor-product base change.  It does not impose any
condition on the induced residue-field maps.
-/

universe u v w

open scoped TensorProduct

namespace PrimeSpectrum.EtalePoint

/-- A pointed etale extension together with a quasi-finite decomposition of
the corresponding tensor-product base change. -/
@[stacks 00UL "quasi-finite decomposition after a pointed etale extension"]
structure QuasiFiniteDecomposition
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    {S : Type v} [CommRing S] [Algebra R S] where
  /-- The pointed etale extension of the selected base point. -/
  etalePoint : EtalePoint.{u, w} p
  /-- The neutral quasi-finite decomposition after base change. -/
  decomposition :
    PrimeSpectrum.QuasiFiniteDecomposition etalePoint.point
      (etalePoint.carrier ⊗[R] S)

namespace QuasiFiniteDecomposition

/-- Combine a pointed etale extension with a neutral quasi-finite
decomposition of its tensor-product base change. -/
@[stacks 00UL "pointed etale quasi-finite decomposition constructor"]
def of {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (etalePoint : EtalePoint.{u, w} p)
    (decomposition :
      PrimeSpectrum.QuasiFiniteDecomposition etalePoint.point
        (etalePoint.carrier ⊗[R] S)) :
    QuasiFiniteDecomposition.{u, v, w} p (S := S) where
  etalePoint := etalePoint
  decomposition := decomposition

end QuasiFiniteDecomposition

end PrimeSpectrum.EtalePoint
