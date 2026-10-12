/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.RegularScheme
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 31.21.12: let `i : Z ⟶ X` be an immersion. If `Z` and `X` are regular schemes, then `i`
is a regular immersion. -/
@[stacks 0E9J] #check
  (@AlgebraicGeometry.isRegularImmersion_of_isImmersion_of_regular :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [Scheme.Regular Z] [Scheme.Regular X],
      IsRegularImmersion i)
