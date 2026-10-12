/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Lemma 26.23.2: `f` is a monomorphism exactly when its diagonal is an
isomorphism. -/
@[stacks 01L3] #check (pullback.isIso_diagonal_iff f).symm
