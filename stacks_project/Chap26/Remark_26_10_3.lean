/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Immersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Remark 26.10.3: some immersion does not factor as an open immersion followed by a closed
immersion. -/
@[stacks 01IP] #check exists_isImmersion_not_isOpenThenClosed
#check isOpenThenClosed_iff
