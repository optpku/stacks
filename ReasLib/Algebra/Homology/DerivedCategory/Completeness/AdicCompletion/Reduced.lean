module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.PowerIntersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completeness of reduced derived-complete rings

For a finitely generated ideal in a reduced ring, derived completeness of the ring implies ordinary
adic completeness.

@stack 0G5V
-/

@[expose] public section

universe u

namespace ModuleCat.IsDerivedCompleteWithRespectTo

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Lemma 15.94.12 (Stacks `0G5V`): if `A` is reduced, `I` is finitely generated, and `A` is
derived complete with respect to `I`, then `A` is `I`-adically complete. -/
@[stacks 0G5V "derived completeness gives adic completeness for a reduced ring"]
theorem isAdicComplete_of_isReduced [IsReduced A]
    (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I) (hI : I.FG) :
    IsAdicComplete I A := sorry

end ModuleCat.IsDerivedCompleteWithRespectTo
