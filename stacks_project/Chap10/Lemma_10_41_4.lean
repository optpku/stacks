/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.RingTheory.Ideal.GoingDown
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.41.4

@stack 00HX
-/

universe u v w

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/- Lemma 10.41.4 (1): if `R → S` and `S → T` satisfy going down, then `R → T` satisfies going
down. This is exactly the canonical mathlib theorem `Algebra.HasGoingDown.trans`. -/
@[stacks 00HX "(1) going-down transitivity"]
#check @Algebra.HasGoingDown.trans

/- Lemma 10.41.4 (2): by Definition 10.41.1, going up for `R → S` is the specializing-map
property of `PrimeSpectrum.comap (algebraMap R S)`. Since `PrimeSpectrum.comap (algebraMap R T)` is
the composite of `PrimeSpectrum.comap (algebraMap S T)` and `PrimeSpectrum.comap (algebraMap R S)`,
the source-facing stability statement is the specialization of the canonical theorem
`SpecializingMap.comp` to these spectrum maps. -/
-- Lemma 10.41.4 (2): source-shaped specialization of `SpecializingMap.comp`.
@[stacks 00HX "(2) going-up transitivity"]
#check
  (show SpecializingMap (comap (algebraMap R S)) →
      SpecializingMap (comap (algebraMap S T)) →
      SpecializingMap (comap (algebraMap R T)) from
    fun hRS hST ↦ by
      simpa [Function.comp, comap_comp, IsScalarTower.algebraMap_eq R S T] using
        SpecializingMap.comp hST hRS)

@[stacks 00HX "specializing-map composition"]
#check @SpecializingMap.comp

end
