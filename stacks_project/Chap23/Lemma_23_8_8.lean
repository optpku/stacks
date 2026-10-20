/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField.Comparison
import StacksCheckRecall

@[expose] public section

/- Lemma 23.8.8 (1), tag `09Q6`: the field-relative and intrinsic complete-intersection
predicates agree after localization at a prime. -/
universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
variable (q : PrimeSpectrum S)

@[stacks 09Q6 "(1)"]
#check (Algebra.IsCompleteIntersectionOver.atPrime_iff_completeIntersectionLocalRing q :
  Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
    IsCompleteIntersectionLocalRing (Localization.AtPrime q.asIdeal))

end

/- Lemma 23.8.8 (2), tag `09Q6`: for finite-type algebras over a field, the field-relative and
intrinsic local complete-intersection predicates agree. -/
section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

@[stacks 09Q6 "(2)"]
#check (IsLocalCompleteIntersection.iff_isLocalCompleteIntersectionRing (k := k) (S := S) :
  IsLocalCompleteIntersection k S ↔ IsLocalCompleteIntersectionRing S)

end
