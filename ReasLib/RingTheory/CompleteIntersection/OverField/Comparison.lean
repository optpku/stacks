/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.EssentialFiniteness.Basic

@[expose] public section

/-!
# Comparing Complete-Intersection Notions over a Field

@stack 00SF

This leaf relates the field-relative complete-intersection predicates to the intrinsic predicates
on local rings and Noetherian rings.
-/

universe u v w

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

namespace Algebra.IsCompleteIntersectionOver

/-- Lemma 23.8.8 (1), Tag 09Q6: at a prime of a finite-type algebra over a field, the
field-relative and intrinsic complete-intersection local-ring predicates agree. -/
@[stacks 09Q6 "(1)"]
theorem atPrime_iff_completeIntersectionLocalRing (q : PrimeSpectrum S) :
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionLocalRing (Localization.AtPrime q.asIdeal) := sorry

end Algebra.IsCompleteIntersectionOver

namespace IsLocalCompleteIntersection

/-- Lemma 23.8.8 (2), Tag 09Q6: for a finite-type algebra over a field, the field-relative local
complete-intersection predicate agrees with the intrinsic prime-local predicate. -/
@[stacks 09Q6 "(2)"]
theorem iff_isLocalCompleteIntersectionRing :
    IsLocalCompleteIntersection k S ↔ IsLocalCompleteIntersectionRing S := sorry

end IsLocalCompleteIntersection

namespace Algebra.IsCompleteIntersectionOver

variable {T : Type v} [CommRing T] [Algebra k T] [IsLocalRing T]
variable [Algebra.EssFiniteType k T]

/-- Lemma 10.135.7 (00SF): for a local algebra essentially of finite type over a field, complete
intersection over the field, regular kernels of regular-local presentations, and realization as
a prime localization of a global or local complete intersection are equivalent. The presentation
and neighborhood rings live in a universe containing both `k` and `T`; `w` permits further lifting. -/
@[stacks 00SF "local complete-intersection presentation criteria over a field"]
theorem local_tfae :
    List.TFAE
      [ IsCompleteIntersectionOver k T
      , ∀ (R : Type (max u v w)) [CommRing R] [Algebra k R] [Algebra.EssFinitePresentation k R]
          [IsRegularLocalRing R] (pi : R →ₐ[k] T),
          Function.Surjective pi → pi.toRingHom.KernelIsGeneratedByRegularSequence
      , ∃ (R : Type (max u v w)) (_ : CommRing R) (_ : Algebra k R)
          (_ : Algebra.EssFinitePresentation k R) (_ : IsRegularLocalRing R) (pi : R →ₐ[k] T),
          Function.Surjective pi ∧
            ∃ (d : ℕ) (_ : ringKrullDim T + d = ringKrullDim R) (x : Fin d → R),
              Ideal.span (Set.range x) = RingHom.ker pi.toRingHom
      , ∃ (A : Type (max u v w)) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
          (_ : T ≃ₐ[k] Localization.AtPrime a.asIdeal),
          IsGlobalCompleteIntersection k A
      , ∃ (A : Type (max u v w)) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
          (_ : T ≃ₐ[k] Localization.AtPrime a.asIdeal),
          IsLocalCompleteIntersection k A
      ] := sorry

end Algebra.IsCompleteIntersectionOver
