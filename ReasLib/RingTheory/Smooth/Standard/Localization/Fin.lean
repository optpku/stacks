/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Element.Fin
public import ReasLib.RingTheory.Smooth.Standard.Localization.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-coordinate standard elements and principal localizations

This leaf specializes localization results to the source-facing `Fin`-indexed
presentation predicates.
-/

@[expose] public section

universe u v

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {n m : ℕ}

namespace IsElementaryStandard

/-- An elementary standard witness makes the corresponding principal localization standard
smooth. -/
@[stacks 07EZ "elementary standard localization"]
theorem isStandardSmoothAway {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsElementaryStandard a) :
    IsStandardSmooth R (Localization.Away a) := sorry

end IsElementaryStandard

namespace IsStrictlyStandard

/-- A strictly standard witness makes the corresponding principal localization smooth, without
exposing the stronger stable-freeness output. -/
@[stacks 07EZ "strictly standard localization"]
theorem smoothAway {P : Presentation R A (Fin n) (Fin m)} {a : A}
    (h : P.IsStrictlyStandard a) :
    Smooth R (Localization.Away a) := sorry

end IsStrictlyStandard

end Algebra.Presentation
