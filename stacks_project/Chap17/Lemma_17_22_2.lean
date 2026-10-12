/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness
import StacksCheckRecall

/-!
# Lemma 17.22.2

Internal-Hom exactness on a ringed space is the specialization of the neutral closed-monoidal
API.  This compatibility file therefore has no dependency on Chapter 18.
-/

@[expose] public section

/- Lemma 17.22.2 (1) (01CO): internal Hom is left exact in its contravariant source. -/
@[stacks 01CO "(1)"]
#check @CategoryTheory.MonoidalClosed.InternalHom.mapOp_exact_of_exact_epi

/- Lemma 17.22.2 (2) (01CO): internal Hom is left exact in its target. -/
@[stacks 01CO "(2)"]
#check @CategoryTheory.MonoidalClosed.InternalHom.map_exact_of_exact_mono
