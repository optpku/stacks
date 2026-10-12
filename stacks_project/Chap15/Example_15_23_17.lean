/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive.Counterexample
import StacksCheckRecall

/-!
# Example 15.23.17

@stack 0EBB

The explicit non-`(S₂)` ring, its origin ideal, the two displayed duality equivalences, and the
resulting finite reflexive `(S₂)` module are owned together in ReasLib.  This file records each
independent source clause and the concrete-map specifications needed by downstream users.
-/

@[expose] public section

/- Example 15.23.17 (1): `R = k[y, x^2, xy, x^3]` as a subalgebra of `k[x, y]`. -/
@[stacks 0EBB "Example 15.23.17 (1)"]
#check @Module.ReflexiveCounterexample.ring

/- Example 15.23.17 (2): the origin ideal `𝔪 = (y, x^2, xy, x^3)` in `R`. -/
@[stacks 0EBB "Example 15.23.17 (2)"]
#check @Module.ReflexiveCounterexample.ideal

/- Example 15.23.17 (3): the displayed equivalence `Hom_R(k[x, y], R) ≃ 𝔪`. -/
@[stacks 0EBB "Example 15.23.17 (3)"]
#check @Module.ReflexiveCounterexample.ambientDualEquivIdeal

/- Evaluation at `1` and multiplication specify both directions of the first equivalence. -/
#check @Module.ReflexiveCounterexample.ambientDualToIdeal_bijective
#check @Module.ReflexiveCounterexample.ambientDualToIdeal_comp_idealToAmbientDual
#check @Module.ReflexiveCounterexample.idealToAmbientDual_comp_ambientDualToIdeal
#check @Module.ReflexiveCounterexample.ambientDualEquivIdeal_apply
#check @Module.ReflexiveCounterexample.ambientDualEquivIdeal_symm_apply
#check @Module.ReflexiveCounterexample.ambientDualEquivIdeal_unique

/- Example 15.23.17 (4): the displayed equivalence `Hom_R(𝔪, R) ≃ k[x, y]`. -/
@[stacks 0EBB "Example 15.23.17 (4)"]
#check @Module.ReflexiveCounterexample.idealDualEquivAmbientOf

/- Multiplication specifies the inverse of the second equivalence and characterizes it uniquely. -/
#check @Module.ReflexiveCounterexample.ambientToIdealDual_bijective
#check @Module.ReflexiveCounterexample.idealDualEquivAmbientOf_symm_apply
#check @Module.ReflexiveCounterexample.idealDualEquivAmbientOf_unique
#check @Module.ReflexiveCounterexample.idealDualEquivAmbientOf_congr

/- Example 15.23.17 (5): the counterexample ring is Noetherian; its domain structure is inherited
from the ambient polynomial domain. -/
@[stacks 0EBB "Example 15.23.17 (5)"]
#check @Module.ReflexiveCounterexample.ringIsNoetherian

/- Example 15.23.17 (6): `k[x, y]` is finite as an `R`-module. -/
@[stacks 0EBB "Example 15.23.17 (6)"]
#check @Module.ReflexiveCounterexample.ambientModuleFinite

/- Example 15.23.17 (7): `k[x, y]` is reflexive as an `R`-module. -/
@[stacks 0EBB "Example 15.23.17 (7)"]
#check @Module.ReflexiveCounterexample.ambient_isReflexive

/- Example 15.23.17 (8): `k[x, y]` satisfies module `(S₂)` over `R`. -/
@[stacks 0EBB "Example 15.23.17 (8)"]
#check @Module.ReflexiveCounterexample.ambient_serreConditionSTwo

/- Example 15.23.17 (9): the base ring `R` itself does not satisfy `(S₂)`. -/
@[stacks 0EBB "Example 15.23.17 (9)"]
#check @Module.ReflexiveCounterexample.ring_not_serreConditionSTwo
