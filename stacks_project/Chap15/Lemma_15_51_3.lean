/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.QuasiFinite
import StacksCheckRecall

/-!
# Lemma 15.51.3

@stack 0BIT
-/

@[expose] public section

/- Lemma 15.51.3 (1), tag `0BIT`: quasi-finiteness at a target prime transfers a property from
the corresponding source formal fiber. -/
@[stacks 0BIT "(1)"]
#check @FieldAlgebraProperty.QuasiFiniteAt.formalFiber

/- Lemma 15.51.3 (2), tag `0BIT`: the same hypothesis transfers the property on every formal
fiber of the chosen prime localization. -/
@[stacks 0BIT "(2)"]
#check @FieldAlgebraProperty.QuasiFiniteAt.formalFibers

/- Lemma 15.51.3 (3), tag `0BIT`: finite-type quasi-finite extensions preserve `P`-rings. -/
@[stacks 0BIT "(3)"]
#check @IsPRing.of_quasiFinite
