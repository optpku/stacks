/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Immersion
import StacksCheckRecall

@[expose] public section

/- Lemma 26.10.4: an immersion is closed exactly when its set-theoretic image is closed. -/
@[stacks 01IQ] #check
  AlgebraicGeometry.Scheme.Hom.isClosedImmersion_iff_isClosed_range_of_isImmersion
