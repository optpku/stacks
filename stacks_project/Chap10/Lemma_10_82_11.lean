/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.AtPrime

@[expose] public section

/- Lemma 10.82.11: see the reusable base, prime-local, maximal-local, and relative-local
universal-injectivity criteria. -/
/-!
# Universal Injectivity Localization Recall

The localization predicates and their five-way equivalence are owned by ReasLib.

@stack 05CL
-/
@[stacks 05CL "universal injectivity over the base"]
#check LinearMap.UniversallyInjective.overBase
@[stacks 05CL "universal injectivity at a prime"]
#check LinearMap.UniversallyInjective.atPrime
@[stacks 05CL "universal injectivity at a maximal ideal"]
#check LinearMap.UniversallyInjective.atMaximal
@[stacks 05CL "relative universal injectivity at a prime"]
#check LinearMap.UniversallyInjective.atPrimeOver
@[stacks 05CL "relative universal injectivity at a maximal ideal"]
#check LinearMap.UniversallyInjective.atMaximalOver
@[stacks 05CL "universal injectivity is local at primes"]
#check LinearMap.UniversallyInjective.iff_forall_atPrime
@[stacks 05CL "universal injectivity is local at maximal ideals"]
#check LinearMap.UniversallyInjective.iff_forall_atMaximal
@[stacks 05CL "universal injectivity at contracted primes"]
#check LinearMap.UniversallyInjective.iff_forall_atPrimeOver
@[stacks 05CL "universal injectivity at contracted maximal ideals"]
#check LinearMap.UniversallyInjective.iff_forall_atMaximalOver
@[stacks 05CL "five-way local universal injectivity criterion"]
#check LinearMap.UniversallyInjective.tfae_local
