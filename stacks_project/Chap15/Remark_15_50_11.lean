/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.GRing.AdicCompletion
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.50.11

@stack 07PW
-/

universe u

/- Remark 15.50.11 (Stacks 07PW): adic completion does not preserve the G-ring property in
general. The reusable owner records the counterexample in its source-faithful existential form. -/
@[stacks 07PW] #check
  (IsGRing.AdicCompletion.exists_not_isGRing :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      IsGRing R ∧ ¬ IsGRing (AdicCompletion I R))
