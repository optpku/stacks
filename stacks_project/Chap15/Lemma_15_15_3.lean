/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Projective
import StacksCheckRecall

/-!
# Universal injectivity between projective modules

Lemma 15.15.3 identifies universal injectivity with ordinary injectivity over a ring whose proper
finitely generated ideals have nonzero annihilator.

@stack 05GP
-/

@[expose] public section

-- Lemma 15.15.3: under property `(P)`, a linear map between projective modules is universally
-- injective if and only if it is injective.
@[stacks 05GP "Lemma 15.15.3"]
#check @LinearMap.UniversallyInjective.iff_injective_of_projective_of_annihilator
