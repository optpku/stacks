/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.IsEpi.Localization
import StacksCheckRecall

/-!
# Prime-local detection of algebra epimorphisms

@stack 04VS
-/

@[expose] public section

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.107.5 (Stacks `04VS`): epimorphy of `R → S` is detected after base change to
every prime localization of `R`. -/
@[stacks 04VS]
#check (Algebra.IsEpi.iff_forall_atPrime (R := R) (S := S) :
  Algebra.IsEpi R S ↔
    ∀ p : PrimeSpectrum R,
      Algebra.IsEpi (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] S))

end
