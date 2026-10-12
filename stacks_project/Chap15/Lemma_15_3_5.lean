/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Projective.Jacobson

@[expose] public section

/-!
# Lemma 15.3.5 (0BC6)

@stack 0BC6
-/

-- Lemma 15.3.5 (1): a map between finite projective modules is detected as an isomorphism
-- after reduction modulo a Jacobson-radical ideal.
@[stacks 0BC6 "Lemma 15.3.5 (1)"]
#check @bijective_of_bijective_mod_jacobson_of_finite_projective

-- Lemma 15.3.5 (2): an isomorphism between the reductions of finite projective modules lifts.
@[stacks 0BC6 "Lemma 15.3.5 (2)"]
#check @exists_lift_of_quotient_equiv_of_finite_projective

-- Reusable strengthening of (1), requiring projectivity only of the target.
#check @bijective_of_bijective_mod_jacobson_of_finite_projective_target
