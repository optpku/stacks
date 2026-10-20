/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Point.QuasiFinite.PurelyInseparable
import StacksCheckRecall

/-!
# Purely inseparable quasi-finite decomposition

@stack 00UL

The shared owner separates the pointed etale extension from the neutral
finite-product decomposition.  In particular, it does not impose the
residue-field isomorphism required by the stronger notion of an
`EtaleNeighborhood`.
-/

@[expose] public section

universe u v

/- Lemma 10.145.4 (Tag 00UL): after a pointed etale extension at a selected
prime, a finite-type algebra admits a finite-product decomposition whose
selected residue-field maps are finite and purely inseparable and whose
remainder has no quasi-finite point over the selected prime. -/
@[stacks 00UL]
#check
  (PrimeSpectrum.EtalePoint.QuasiFiniteDecomposition.exists_purelyInseparable :
    ∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
      [Algebra.FiniteType R S] (p : PrimeSpectrum R),
      ∃ D : PrimeSpectrum.EtalePoint.QuasiFiniteDecomposition.{u, v, u} p (S := S),
        D.decomposition.HasPurelyInseparableResidueFields)

#check @PrimeSpectrum.EtalePoint.spec
#check @PrimeSpectrum.QuasiFiniteDecomposition.equiv
#check @PrimeSpectrum.QuasiFiniteDecomposition.spec
#check @PrimeSpectrum.QuasiFiniteDecomposition.factorResidueMap_spec
