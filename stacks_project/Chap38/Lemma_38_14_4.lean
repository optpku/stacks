/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.AssociatedPrime.Henselian

open scoped DirectSum TensorProduct Algebra.TensorProduct.Right

universe u v w x

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N]
variable {M : Type x} [AddCommGroup M] [Module R M]

/- Lemma 38.14.4: over a Henselian local ring, an exact associated prime of
`N ⊗[R] M` does not become the unit ideal after adjoining the maximal ideal
of `R` to `S`, when `N` is countably generated and Mittag-Leffler over `R`. -/
@[stacks 05IV] #check
  (associatedPrimesOfModule.Henselian.add_map_maximalIdeal_ne_top :
    Module.CountablyGenerated R N →
      Module.MittagLeffler R N →
        ∀ {q : Ideal S},
          q ∈ associatedPrimesOfModule S (N ⊗[R] M) →
            q + Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊤)
