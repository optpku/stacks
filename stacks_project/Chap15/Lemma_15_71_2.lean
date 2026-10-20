/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.LinearMap.Factorisation.FiniteProjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.71.2

@stack 0G91
-/

/-!
# Lemma 15.71.2: finite projective midpoints
-/

/- Lemma 15.71.2: when the source is finite, a map factoring through a projective module factors
through a finite projective module. -/
@[stacks 0G91]
#check @LinearMap.FactorsThroughProjective.finite

/- For a finite source, the corresponding projective-factor submodules coincide. -/
#check @LinearMap.projectiveFactors_eq_finiteProjectiveFactors

/- The midpoint owner uses the semiring-level `Module.FiniteProjective` predicate. -/
#check @LinearMap.Factorisation.FiniteProjective
