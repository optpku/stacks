/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential.FiniteProjectiveLimit
import StacksCheckRecall

/-!
# Finite projective inverse limits

Lemma 15.13.4 identifies the inverse limit of a compatible system of finite flat modules as a
finite projective module and states that its base change to every stage recovers the given stage.

@stack 0D4B
-/

open CategoryTheory

namespace CategoryTheory.SequentialInverseSystem.ModuleSystem.FiniteProjectiveLimit

-- Lemma 15.13.4: the canonical successor and inverse-limit base-change morphisms.
@[stacks 0D4B "successor base-change morphism"]
#check @stageBaseChangeComparison

@[stacks 0D4B "inverse-limit base-change morphism"]
#check @inverseLimitBaseChangeComparison

-- Lemma 15.13.4 (1): the inverse-limit module is finite.
@[stacks 0D4B "(1), inverse-limit module is finite"]
#check @inverseLimit_finite

-- Lemma 15.13.4 (2): the inverse-limit module is projective.
@[stacks 0D4B "(2), inverse-limit module is projective"]
#check @inverseLimit_projective

-- Lemma 15.13.4 (3): base change to every stage is an isomorphism on carriers.
@[stacks 0D4B "(3), stage base change is bijective"]
#check @inverseLimitBaseChangeComparison_bijective

end CategoryTheory.SequentialInverseSystem.ModuleSystem.FiniteProjectiveLimit
