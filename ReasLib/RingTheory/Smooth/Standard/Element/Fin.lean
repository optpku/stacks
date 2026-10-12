/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Element.Selected
public import ReasLib.RingTheory.Smooth.Standard.Presentation.Fin
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-presentation views of standard elements

This leaf bridges `Fin`-indexed initial-coordinate witnesses to the generic
standard-element predicates.
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (R)

namespace Presentation.IsElementaryStandard

/-- A source-facing finite presentation witness gives the generalized global
elementary-standard predicate. -/
@[stacks 07C7 "finite-presentation elementary data gives an elementary standard element"]
theorem isElementaryStandard
    {n m : ℕ} {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsElementaryStandard a) :
    Algebra.IsElementaryStandard R a := sorry

end Presentation.IsElementaryStandard

namespace Presentation.IsStrictlyStandard

/-- A source-facing finite presentation witness gives the generalized global
strictly-standard predicate. -/
@[stacks 07C7 "finite-presentation strict data gives a strictly standard element"]
theorem isStrictlyStandard
    {n m : ℕ} {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsStrictlyStandard a) :
    Algebra.IsStrictlyStandard R a := sorry

end Presentation.IsStrictlyStandard

namespace IsElementaryStandard

/-- The generalized elementary-standard predicate is equivalent to the
source-facing `Fin`-indexed initial-coordinate formulation. -/
@[stacks 07C7 "finite-presentation characterization of elementary standard elements"]
theorem iff_finPresentation {a : A} :
    IsElementaryStandard R a ↔
      ∃ (n m : ℕ) (P : Presentation R A (Fin n) (Fin m)),
        P.IsElementaryStandard a := sorry

end IsElementaryStandard

namespace IsStrictlyStandard

/-- The generalized strictly-standard predicate is equivalent to the
source-facing `Fin`-indexed initial-coordinate formulation. -/
@[stacks 07C7 "finite-presentation characterization of strictly standard elements"]
theorem iff_finPresentation {a : A} :
    IsStrictlyStandard R a ↔
      ∃ (n m : ℕ) (P : Presentation R A (Fin n) (Fin m)),
        P.IsStrictlyStandard a := sorry

end IsStrictlyStandard

end Algebra
