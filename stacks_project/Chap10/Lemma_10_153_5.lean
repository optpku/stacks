/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finite-type algebras over henselian local rings

@stack 04GJ

Lemma 10.153.5 is a direct recall of the reusable finite-part decomposition.
The canonical statement keeps the finite part and product presentation as
separate owners, avoiding a source-specific existential package of instances.
-/

/- Lemma 10.153.5 [stacks 04GJ]: a finite-type algebra over a henselian local
ring splits into a finite product of henselian local finite algebras and a
remainder with no quasi-finite point over the closed point. -/
@[stacks 04GJ]
#check @HenselianLocalRing.FiniteType.existsFinitePartDecomposition
