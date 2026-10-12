/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition.LinearMap
import StacksCheckRecall

/-!
# Lemma 15.23.11

This file recalls the `(S₁)`, `(S₂)`, and torsion-free `(S₂)` properties of linear-map modules.

@stack 0AV6
-/

@[expose] public section

/- Lemma 15.23.11 (1): `(S₁)` passes from a finite codomain to the linear-map module. -/
@[stacks 0AV6 "Lemma 15.23.11 (1)"]
#check @LinearMap.instSerreConditionSOneOfCodomain

/- Lemma 15.23.11 (2): `(S₂)` passes from a finite codomain to the linear-map module. -/
@[stacks 0AV6 "Lemma 15.23.11 (2)"]
#check @LinearMap.instSerreConditionSTwoOfCodomain

/- Lemma 15.23.11 (3): over a domain, linear maps into a finite torsion-free `(S₂)` module
form a torsion-free `(S₂)` module. -/
@[stacks 0AV6 "Lemma 15.23.11 (3)"]
#check @LinearMap.isTorsionFree_and_serreConditionSTwo_of_codomain

/- The torsion-free component of part (3) is the canonical upstream instance. -/
#check @LinearMap.instIsTorsionFree
