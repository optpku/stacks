/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic Freeness of Finitely Presented Modules

This leaf records the principal-open form of generic freeness for finitely
presented modules over a domain.  The first theorem is useful when freeness of
the generic fiber is supplied by a separate argument; the second obtains that
freeness from the fraction field automatically.
-/

@[expose] public section

universe u v

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Tag `051T`: a finitely presented module over a domain that is free on its
generic fiber is free after inverting one nonzero element. -/
@[stacks 051T "generic-fiber finite-presentation freeness"]
theorem exists_nonzero_away_free_of_genericFiber
    [Module.FinitePresentation R M]
    [Module.Free (Localization (nonZeroDivisors R))
      (LocalizedModule (nonZeroDivisors R) M)] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := sorry

/-- Tag `051T`: every finitely presented module over a domain is free after
inverting one nonzero element. -/
@[stacks 051T "finite-presentation generic freeness over a domain"]
theorem exists_nonzero_away_free [Module.FinitePresentation R M] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule.Away f M) := sorry

end Module.FinitePresentation
