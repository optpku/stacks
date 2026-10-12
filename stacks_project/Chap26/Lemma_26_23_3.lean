/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.23.3: a monomorphism of schemes is separated. -/
@[stacks 01L4] #check IsSeparated.isSeparated_of_mono
