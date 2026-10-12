/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Element.Fin
public import ReasLib.RingTheory.Smooth.Standard.Equiv.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-coordinate standard data under algebra equivalences

This leaf specializes algebra-equivalence transport to the source-facing
`Fin`-indexed presentation predicates.
-/

@[expose] public section

universe u v w

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

namespace Presentation.IsElementaryStandard

variable {n m : ℕ}

/-- A `Fin`-indexed elementary-standard presentation transports along an
algebra equivalence. -/
@[stacks 07C7 "elementary standard presentations under algebra equivalence"]
theorem of_algEquiv
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsElementaryStandard a) (e : A ≃ₐ[R] B) :
    (P.ofAlgEquiv e).IsElementaryStandard (e a) := sorry

/-- The `Fin`-indexed elementary-standard predicate is invariant under
transport along an algebra equivalence. -/
theorem iff_of_algEquiv
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (e : A ≃ₐ[R] B) :
    P.IsElementaryStandard a ↔
      (P.ofAlgEquiv e).IsElementaryStandard (e a) := sorry

end Presentation.IsElementaryStandard

namespace Presentation.IsStrictlyStandard

variable {n m : ℕ}

/-- A `Fin`-indexed strictly-standard presentation transports along an
algebra equivalence. -/
@[stacks 07C7 "strictly standard presentations under algebra equivalence"]
theorem of_algEquiv
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsStrictlyStandard a) (e : A ≃ₐ[R] B) :
    (P.ofAlgEquiv e).IsStrictlyStandard (e a) := sorry

/-- The `Fin`-indexed strictly-standard predicate is invariant under
transport along an algebra equivalence. -/
theorem iff_of_algEquiv
    {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (e : A ≃ₐ[R] B) :
    P.IsStrictlyStandard a ↔
      (P.ofAlgEquiv e).IsStrictlyStandard (e a) := sorry

end Presentation.IsStrictlyStandard

end Algebra
