/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Point.QuasiFinite
public import ReasLib.RingTheory.QuasiFinite.Decomposition.PurelyInseparable

@[expose] public section

/-!
# Purely inseparable decompositions after a pointed etale extension

@stack 00UL

This leaf states the existence of a pointed etale decomposition whose
selected residue-field maps are purely inseparable.  The underlying pointed
decomposition is owned independently in `Etale.Point.QuasiFinite`.
-/

universe u v

namespace PrimeSpectrum.EtalePoint

namespace QuasiFiniteDecomposition

/-- Stacks 00UL: after a pointed etale extension, a finite-type algebra has a
quasi-finite product decomposition whose selected residue-field maps are
purely inseparable. -/
@[stacks 00UL]
theorem exists_purelyInseparable
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : PrimeSpectrum R) :
    ∃ D : QuasiFiniteDecomposition.{u, v, u} p (S := S),
      D.decomposition.HasPurelyInseparableResidueFields := sorry

end QuasiFiniteDecomposition

end PrimeSpectrum.EtalePoint
