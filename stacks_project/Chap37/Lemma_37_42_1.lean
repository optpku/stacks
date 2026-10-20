/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Point.IntegralDecomposition
import StacksCheckRecall

@[expose] public section

universe u v

open scoped TensorProduct

/- Lemma 37.42.1: an integral algebra with finite prime fiber and finite
maximal separable residue subextensions admits, after a pointed étale base
change, a finite product decomposition into integral singleton-fiber factors
whose selected residue extensions are purely inseparable. -/
@[stacks 0BSR] #check
  (PrimeSpectrum.EtalePoint.exists_integralDecomposition :
    ∀ {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
      [Algebra.IsIntegral R S] (p : PrimeSpectrum R),
      (p.asIdeal.primesOver S).Finite →
      (∀ q : p.asIdeal.primesOver S,
        Ideal.ResidueField.FiniteSeparablePart p.asIdeal q.1) →
      ∃ U : PrimeSpectrum.EtalePoint.{u, u} p,
        ∃ D : PrimeSpectrum.IntegralDecomposition U.point
          (U.carrier ⊗[R] S),
          D.HasPurelyInseparableResidueFields)
