/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

universe u

open IsLocalRing

namespace AdicCompletion.Counterexample

/-- There exists a local ring whose adic completion is local but is neither a complete local
ring nor adically complete as a module over the original ring. -/
theorem exists_local_not_completeLocalRing :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R) (m : Ideal R)
      (_ : m.IsMaximal) (_ : IsLocalRing (AdicCompletion m R)),
      maximalIdeal (AdicCompletion m R) ≠
          m.map (algebraMap R (AdicCompletion m R)) ∧
        ¬ IsCompleteLocalRing (AdicCompletion m R) ∧
        ¬ IsAdicComplete m (AdicCompletion m R) := sorry

end AdicCompletion.Counterexample
