module

public import ReasLib.RingTheory.Smooth.Standard.BaseChange.Selected
public import ReasLib.RingTheory.Smooth.Standard.Element.Fin
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for finite-coordinate standard data

This leaf specializes base change to the source-facing `Fin`-indexed
presentation predicates.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable {n m : ℕ}

/-- A presentation-level elementary standard witness transports to every coefficient base
change. -/
@[stacks 07CC "finite-coordinate elementary standard data under base change"]
theorem IsElementaryStandard.baseChange
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (ha : P.IsElementaryStandard a) :
    (P.baseChange R').IsElementaryStandard ((1 : R') ⊗ₜ[R] a) := sorry

/-- A presentation-level strictly standard witness transports to every coefficient base change. -/
@[stacks 07CC "finite-coordinate strictly standard data under base change"]
theorem IsStrictlyStandard.baseChange
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (ha : P.IsStrictlyStandard a) :
    (P.baseChange R').IsStrictlyStandard ((1 : R') ⊗ₜ[R] a) := sorry

end Algebra.Presentation
