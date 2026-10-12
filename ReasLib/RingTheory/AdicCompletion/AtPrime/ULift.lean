/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.LocalEquiv.Stage
public import ReasLib.RingTheory.Localization.AtPrime.ULift

/-!
# Completed Prime Localizations under Universe Lift

@stack 0523

This leaf lifts the canonical local-ring equivalence in
`ULift.atPrimeEquiv` to maximal-ideal completions and records
the dense and finite-stage computations needed by completion arguments.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace ULift

variable {A : Type u} [CommRing A]

/-- Tag `0523`: completing the canonical universe-lift local-ring equivalence gives an
equivalence of completed local rings. -/
@[stacks 0523 "completed prime localizations under universe lift"]
noncomputable def atPrimeCompletionEquiv (Q : Ideal A) [Q.IsPrime] :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (comapIdeal Q)))
        (Localization.AtPrime (comapIdeal Q)) ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q) :=
  AdicCompletion.mapLocalEquiv (atPrimeEquiv Q)

/-- Tag `0523`: the completed universe-lift comparison sends a dense local-ring image to the
dense image of its transported value. -/
@[simp, stacks 0523 "completed prime localizations under universe lift"]
theorem atPrimeCompletionEquiv_apply_algebraMap (Q : Ideal A) [Q.IsPrime]
    (y : Localization.AtPrime (comapIdeal Q)) :
    atPrimeCompletionEquiv Q
        (algebraMap
          (Localization.AtPrime (comapIdeal Q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (comapIdeal Q)))
            (Localization.AtPrime (comapIdeal Q))) y) =
      algebraMap
        (Localization.AtPrime Q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime Q)) (Localization.AtPrime Q))
        (atPrimeEquiv Q y) := sorry

/-- Tag `0523`: stagewise evaluation commutes with the completed universe-lift local-ring
equivalence. -/
@[stacks 0523 "completed prime localizations under universe lift"]
theorem atPrimeCompletionEquiv_evalₐ (Q : Ideal A) [Q.IsPrime] (n : ℕ)
    (x : AdicCompletion
      (maximalIdeal (Localization.AtPrime (comapIdeal Q)))
      (Localization.AtPrime (comapIdeal Q))) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime Q)) n
        (atPrimeCompletionEquiv Q x) =
      (RingEquiv.MaximalIdeal.quotientPowEquiv (atPrimeEquiv Q) n)
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (comapIdeal Q))) n x) := sorry

end ULift
