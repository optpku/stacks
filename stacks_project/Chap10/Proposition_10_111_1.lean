/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.AuslanderBuchsbaum
import StacksCheckRecall

/-!
# The Auslander--Buchsbaum Formula

The reusable theorem belongs to `Module` because it relates the depth and
projective dimension of a finite module over a Noetherian local ring.  This
source file retains the Stacks-facing entry point only.

@stack 090V
-/

@[expose] public section

/- Proposition 10.111.1 (Stacks tag `090V`): a nonzero finite module of finite
projective dimension over a Noetherian local ring has a natural
projective-dimension value `d` satisfying the Auslander--Buchsbaum formula. -/
@[stacks 090V]
#check @Module.exists_auslanderBuchsbaum

/- The formula when the natural projective-dimension value is already fixed. -/
@[stacks 090V "fixed projective-dimension formula"]
#check @Module.auslanderBuchsbaum
