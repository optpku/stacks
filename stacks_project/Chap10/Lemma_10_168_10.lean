/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.QuasiFinite
import StacksCheckRecall

/-!
# Lemma 10.168.10

@stack 034Z
-/

@[expose] public section

/- Lemma 10.168.10 [stacks 034Z]: canonical recall.  The reusable owner is
`RingHom.FaithfullyFlat.exists_quasiFiniteRefinement`; it is stated for an
arbitrary faithfully flat finitely presented commutative ring map, while this
chapter leaf supplies the source label. -/
@[stacks 034Z]
#check @RingHom.FaithfullyFlat.exists_quasiFiniteRefinement

@[stacks 034Z "explicit quasi-finite refinement constructor"]
#check @RingHom.QuasiFiniteRefinement.of
