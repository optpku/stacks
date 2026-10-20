/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Fiber.NoetherNormalization

universe u v

/- Lemma 37.31.3: a finite-type `R`-algebra whose fibers have Krull dimension
at most `d` admits a finite-type quasi-finite `R`-algebra homomorphism from
`MvPolynomial (Fin d) R`. -/
@[stacks 0GTG] #check
  (RingHom.FibersKrullDimLE.exists_quasiFinite_mvPolynomial :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S]
      [Algebra R S] [Algebra.FiniteType R S] (d : ℕ)
      (h : RingHom.FibersKrullDimLE d (algebraMap R S)),
      ∃ f : MvPolynomial (Fin d) R →ₐ[R] S,
        RingHom.FiniteType.QuasiFinite f.toRingHom)
